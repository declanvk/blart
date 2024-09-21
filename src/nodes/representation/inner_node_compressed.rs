use crate::{
    rust_nightly_apis::{assume, maybe_uninit_slice_assume_init_ref, maybe_uninit_uninit_array},
    Header, InnerNode, InnerNode48, Node, NodeType, OpaqueNodePtr, RestrictedNodeIndex,
};
use std::{
    fmt,
    iter::{Copied, Zip},
    mem::{self, MaybeUninit},
    ops::{Bound, RangeBounds},
    slice::Iter,
};

#[cfg(feature = "nightly")]
use std::simd::{
    cmp::{SimdPartialEq, SimdPartialOrd},
    u8x16,
};

/// Where a write should happen inside the node
#[derive(Debug)]
enum WritePoint {
    /// In an already existing key fragment
    Existing(usize),
    /// As the last key fragment
    Last(usize),
    /// Shift the key fragments to the right
    Shift(usize),
}

/// Common methods for searching in an [`InnerNodeCompressed`]
trait SearchInnerNodeCompressed {
    /// Get the index of the child if it exists
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize>;

    /// Find the write point for `key_fragment`
    fn find_write_point(&self, key_fragment: u8) -> WritePoint;
}

/// Node type that has a compact representation for key bytes and children
/// pointers.
#[repr(C, align(8))]
pub struct InnerNodeCompressed<K, V, const PREFIX_LEN: usize, const SIZE: usize> {
    /// The common node fields.
    pub header: Header<PREFIX_LEN>,
    /// An array that contains single key bytes in the same index as the
    /// `child_pointers` array contains the matching child tree.
    ///
    /// This array will only be initialized for the first `header.num_children`
    /// values.
    pub keys: [MaybeUninit<u8>; SIZE],
    /// An array that contains the child data.
    ///
    /// This array will only be initialized for the first `header.num_children`
    /// values.
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<K, V, PREFIX_LEN>>; SIZE],
}

impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> Clone
    for InnerNodeCompressed<K, V, PREFIX_LEN, SIZE>
{
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            keys: self.keys,
            child_pointers: self.child_pointers,
        }
    }
}

impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> fmt::Debug
    for InnerNodeCompressed<K, V, PREFIX_LEN, SIZE>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (keys, child_pointers) = self.initialized_portion();
        f.debug_struct("InnerNodeBlock")
            .field("SIZE", &SIZE)
            .field("header", &self.header)
            .field("keys", &keys)
            .field("child_pointers", &child_pointers)
            .finish()
    }
}

/// Iterator type for an [`InnerNodeCompressed`]
pub type InnerNodeCompressedIter<'a, K, V, const PREFIX_LEN: usize> =
    Zip<Copied<Iter<'a, u8>>, Copied<Iter<'a, OpaqueNodePtr<K, V, PREFIX_LEN>>>>;

impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> InnerNodeCompressed<K, V, PREFIX_LEN, SIZE> {
    /// Return the initialized portions of the keys and child pointer arrays.
    pub fn initialized_portion(&self) -> (&[u8], &[OpaqueNodePtr<K, V, PREFIX_LEN>]) {
        // SAFETY: The array prefix with length `header.num_children` is guaranteed to
        // be initialized
        unsafe {
            let num_children = self.header.num_children();
            assume!(num_children <= self.keys.len());
            (
                maybe_uninit_slice_assume_init_ref(self.keys.get_unchecked(0..num_children)),
                maybe_uninit_slice_assume_init_ref(
                    self.child_pointers.get_unchecked(0..num_children),
                ),
            )
        }
    }

    /// Generalized version of [`InnerNode::lookup_child`] for compressed nodes
    fn lookup_child_inner(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>>
    where
        Self: SearchInnerNodeCompressed,
    {
        let idx = self.lookup_child_index(key_fragment)?;
        unsafe {
            // SAFETY: If `idx` is out of bounds the node should already have grown
            // so it's safe to assume that `idx` is in bounds
            assume!(idx < self.child_pointers.len());

            // SAFETY: The value at `child_index` is guaranteed to be initialized because
            // the `lookup_child_index` function will only search in the initialized portion
            // of the `child_pointers` array.
            Some(MaybeUninit::assume_init(self.child_pointers[idx]))
        }
    }

    /// Writes a child to the node by check the order of insertion
    ///
    /// # Panics
    ///  - This functions assumes that the write is gonna be inbound (i.e the
    ///    check for a full node is done previously to the call of this
    ///    function)
    fn write_child_inner(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>,
    ) where
        Self: SearchInnerNodeCompressed,
    {
        let num_children = self.header.num_children();
        let idx = match self.find_write_point(key_fragment) {
            WritePoint::Existing(child_index) => child_index,
            WritePoint::Last(child_index) => {
                self.header.inc_num_children();
                child_index
            },
            WritePoint::Shift(child_index) => {
                #[allow(unused_unsafe)]
                unsafe {
                    // SAFETY: This is by construction, since the number of children
                    // is always <= maximum number of keys (children) that we can hold
                    assume!(num_children <= self.keys.len());

                    // SAFETY: When we are shifting children, because a new minimum one
                    // is being inserted this guarantees to us that the index of insertion
                    // is < current number of children (because if it was >= we wouldn't
                    // need to shift the data)
                    assume!(child_index < num_children);

                    // assume!(child_index + 1 + (num_children - child_index) <=
                    // self.keys.len());
                }
                self.keys
                    .copy_within(child_index..num_children, child_index + 1);
                self.child_pointers
                    .copy_within(child_index..num_children, child_index + 1);
                self.header.inc_num_children();
                child_index
            },
        };
        unsafe {
            // SAFETY: The check for a full node is done previously to the call
            // of this function, so it's safe to assume that the new child index is
            // in bounds
            self.write_child_at(idx, key_fragment, child_pointer);
        }
    }

    /// Writes a child to the node without bounds check or order
    ///
    /// # Safety
    /// - This functions assumes that the write is gonna be inbound (i.e the
    ///   check for a full node is done previously to the call of this function)
    pub unsafe fn write_child_unchecked(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>,
    ) {
        let idx = self.header.num_children();
        unsafe { self.write_child_at(idx, key_fragment, child_pointer) };
        self.header.inc_num_children();
    }

    /// Writes a child to the node without bounds check or order
    ///
    /// # Safety
    ///  - This functions assumes that the write is gonna be inbound (i.e the
    ///    check for a full node is done previously to the call of this
    ///    function)
    unsafe fn write_child_at(
        &mut self,
        idx: usize,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>,
    ) {
        unsafe {
            assume!(idx < self.keys.len());
            self.keys.get_unchecked_mut(idx).write(key_fragment);
            self.child_pointers
                .get_unchecked_mut(idx)
                .write(child_pointer);
        }
    }

    /// Removes child if it exists
    fn remove_child_inner(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>>
    where
        Self: SearchInnerNodeCompressed,
    {
        let child_index = self.lookup_child_index(key_fragment)?;
        let child_ptr = mem::replace(&mut self.child_pointers[child_index], MaybeUninit::uninit());

        // Copy all the child_pointer and key values in higher indices down by one.
        self.child_pointers
            .copy_within((child_index + 1)..self.header.num_children(), child_index);
        self.keys
            .copy_within((child_index + 1)..self.header.num_children(), child_index);

        self.header.dec_num_children();
        // SAFETY: This child pointer value is initialized because we got it by
        // searching through the initialized keys and got the `Ok(index)` value.
        Some(unsafe { MaybeUninit::assume_init(child_ptr) })
    }

    /// Grows or shrinks the node
    fn change_block_size<const NEW_SIZE: usize>(
        &self,
    ) -> InnerNodeCompressed<K, V, PREFIX_LEN, NEW_SIZE> {
        assert!(
            self.header.num_children() <= NEW_SIZE,
            "Cannot change InnerNodeCompressed<{}> to size {} when it has more than {} children. \
             Currently has [{}] children.",
            SIZE,
            NEW_SIZE,
            NEW_SIZE,
            self.header.num_children()
        );

        let header = self.header.clone();
        let mut keys = [MaybeUninit::new(0); NEW_SIZE];
        let mut child_pointers = maybe_uninit_uninit_array();
        let num_children = header.num_children();

        #[allow(unused_unsafe)]
        unsafe {
            // SAFETY: By construction the number of children in the header
            // is kept in sync with the number of children written in the node
            // and if this number exceeds the maximum len the node should have
            // already grown. So we know for a fact that that num_children <= node len
            assume!(num_children <= self.keys.len());
            assume!(num_children <= self.child_pointers.len());

            // SAFETY: When calling this function the NEW_SIZE, should fit the nodes.
            // We only need to be careful when shrinking the node, since when growing
            // NEW_SIZE >= SIZE.
            // This function is only called in a shrink case when a node is removed from
            // a node and the new current size fits in the NEW_SIZE
            assume!(num_children <= keys.len());
            assume!(num_children <= child_pointers.len());
        }

        keys[..num_children].copy_from_slice(&self.keys[..num_children]);
        child_pointers[..num_children].copy_from_slice(&self.child_pointers[..num_children]);

        InnerNodeCompressed {
            header,
            keys,
            child_pointers,
        }
    }

    /// Transform node into a [`InnerNode48`]
    fn grow_node48(&self) -> InnerNode48<K, V, PREFIX_LEN> {
        let header = self.header.clone();
        let mut child_indices = [RestrictedNodeIndex::<48>::EMPTY; 256];
        let mut child_pointers = maybe_uninit_uninit_array();

        let (keys, _) = self.initialized_portion();

        assert_eq!(
            keys.len(),
            self.keys.len(),
            "Node must be full to grow to node 48"
        );

        for (index, key) in keys.iter().copied().enumerate() {
            // SAFETY: This `try_from` will not panic because index is guaranteed to
            // be 15 or less because of the length of the `InnerNode16.keys` array.
            child_indices[usize::from(key)] =
                unsafe { RestrictedNodeIndex::try_from(index).unwrap_unchecked() };
        }

        let num_children = header.num_children();

        #[allow(unused_unsafe)]
        unsafe {
            // SAFETY: By construction the number of children in the header
            // is kept in sync with the number of children written in the node
            // and if this number exceeds the maximum len the node should have
            // already grown. So we know for a fact that that num_children <= node len
            assume!(num_children <= self.child_pointers.len());

            // SAFETY: We know that the new size is >= old size, so this is safe
            assume!(num_children <= child_pointers.len());
        }

        child_pointers[..num_children].copy_from_slice(&self.child_pointers[..num_children]);

        InnerNode48 {
            header,
            child_indices,
            child_pointers,
        }
    }

    /// Get an iterator over the keys and values of the node
    fn inner_iter(&self) -> InnerNodeCompressedIter<'_, K, V, PREFIX_LEN> {
        let (keys, nodes) = self.initialized_portion();
        keys.iter().copied().zip(nodes.iter().copied())
    }

    /// Get an iterator over a range of keys and values of the node.
    fn inner_range_iter(
        &self,
        bound: impl RangeBounds<u8>,
    ) -> InnerNodeCompressedIter<'_, K, V, PREFIX_LEN>
    where
        Self: SearchInnerNodeCompressed,
    {
        {
            match (bound.start_bound(), bound.end_bound()) {
                (Bound::Excluded(s), Bound::Excluded(e)) if s == e => {
                    panic!("range start and end are equal and excluded: ({s:?})")
                },
                (
                    Bound::Included(s) | Bound::Excluded(s),
                    Bound::Included(e) | Bound::Excluded(e),
                ) if s > e => {
                    panic!("range start ({s:?}) is greater than range end ({e:?})")
                },
                _ => {},
            }
        }

        fn fixup_bound_lookup(bound: Bound<WritePoint>, is_start: bool) -> Bound<usize> {
            // [0, 3, 85, 254]
            match bound {
                // key = Included(0), bound = Included(Existing(0)), output = Included(0)
                Bound::Included(WritePoint::Existing(idx)) => Bound::Included(idx),
                // key = Included(255), bound = Included(Last(4)), output = Included(4)
                Bound::Included(WritePoint::Last(idx)) => Bound::Included(idx),
                // key = Included(2), bound = Included(Shift(1)), output = Included(1)
                Bound::Included(WritePoint::Shift(idx)) => {
                    if is_start {
                        Bound::Included(idx)
                    } else {
                        idx.checked_sub(1)
                            .map_or(Bound::Excluded(0), Bound::Included)
                    }
                },
                // key = Excluded(0), bound = Excluded(Existing(0)), output = Excluded(0)
                Bound::Excluded(WritePoint::Existing(idx)) => Bound::Excluded(idx),
                // key = Excluded(255), bound = Excluded(Last(4)), output = Excluded(4)
                Bound::Excluded(WritePoint::Last(idx)) => Bound::Excluded(idx),
                // key = Excluded(2), bound = Excluded(Shift(1)), output = Excluded(0)
                Bound::Excluded(WritePoint::Shift(idx)) => {
                    if is_start {
                        idx.checked_sub(1).map_or(Bound::Unbounded, Bound::Excluded)
                    } else {
                        Bound::Excluded(idx)
                    }
                },
                Bound::Unbounded => Bound::Unbounded,
            }
        }

        let start_idx = fixup_bound_lookup(
            bound.start_bound().map(|val| self.find_write_point(*val)),
            true,
        );
        let end_idx = fixup_bound_lookup(
            bound.end_bound().map(|val| self.find_write_point(*val)),
            false,
        );

        let slice_range = (start_idx, end_idx);

        let (mut keys, mut nodes) = self.initialized_portion();

        keys = &keys[slice_range];
        nodes = &nodes[slice_range];

        keys.iter().copied().zip(nodes.iter().copied())
    }
}

/// Node that references between 2 and 4 children
pub type InnerNode4<K, V, const PREFIX_LEN: usize> = InnerNodeCompressed<K, V, PREFIX_LEN, 4>;

impl<K, V, const PREFIX_LEN: usize> SearchInnerNodeCompressed for InnerNode4<K, V, PREFIX_LEN> {
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize> {
        let (keys, _) = self.initialized_portion();
        for (child_index, key) in keys.iter().enumerate() {
            if key_fragment == *key {
                return Some(child_index);
            }
        }

        None
    }

    fn find_write_point(&self, key_fragment: u8) -> WritePoint {
        let (keys, _) = self.initialized_portion();

        let mut child_index = 0;
        for key in keys {
            #[allow(clippy::comparison_chain)]
            if key_fragment < *key {
                return WritePoint::Shift(child_index);
            } else if key_fragment == *key {
                return WritePoint::Existing(child_index);
            }
            child_index += 1;
        }
        WritePoint::Last(child_index)
    }
}

impl<K, V, const PREFIX_LEN: usize> Node<PREFIX_LEN> for InnerNode4<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node4;
}

impl<K, V, const PREFIX_LEN: usize> InnerNode<PREFIX_LEN> for InnerNode4<K, V, PREFIX_LEN> {
    type GrownNode = InnerNode16<K, V, PREFIX_LEN>;
    type Iter<'a>
        = InnerNodeCompressedIter<'a, K, V, PREFIX_LEN>
    where
        Self: 'a;
    type ShrunkNode = InnerNode4<K, V, PREFIX_LEN>;

    fn header(&self) -> &Header<PREFIX_LEN> {
        &self.header
    }

    fn from_header(header: Header<PREFIX_LEN>) -> Self {
        Self {
            header,
            child_pointers: maybe_uninit_uninit_array(),
            keys: maybe_uninit_uninit_array(),
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        self.lookup_child_inner(key_fragment)
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>) {
        self.write_child_inner(key_fragment, child_pointer)
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        self.remove_child_inner(key_fragment)
    }

    fn grow(&self) -> Self::GrownNode {
        self.change_block_size()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        panic!("unable to shrink a Node4, something went wrong!")
    }

    fn iter(&self) -> Self::Iter<'_> {
        self.inner_iter()
    }

    fn range(
        &self,
        bound: impl RangeBounds<u8>,
    ) -> impl DoubleEndedIterator<Item = (u8, OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>)>
           + std::iter::FusedIterator {
        self.inner_range_iter(bound)
    }

    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        let (keys, children) = self.initialized_portion();
        // SAFETY: Any Node4 must have at least 2 children, so the `keys` and `children`
        // arrays must be non-empty
        unsafe {
            (
                keys.first().copied().unwrap_unchecked(),
                children.first().copied().unwrap_unchecked(),
            )
        }
    }

    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        let (keys, children) = self.initialized_portion();
        // SAFETY: Any Node4 must have at least 2 children, so the `keys` and `children`
        // arrays must be non-empty
        unsafe {
            (
                keys.last().copied().unwrap_unchecked(),
                children.last().copied().unwrap_unchecked(),
            )
        }
    }
}

/// Node that references between 5 and 16 children
pub type InnerNode16<K, V, const PREFIX_LEN: usize> = InnerNodeCompressed<K, V, PREFIX_LEN, 16>;

impl<K, V, const PREFIX_LEN: usize> SearchInnerNodeCompressed for InnerNode16<K, V, PREFIX_LEN> {
    #[cfg(feature = "nightly")]
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize> {
        // SAFETY: Even though the type is marked is uninit data, when
        // crated this is filled with initialized data, we just use it to
        // remind us that a portion might be uninitialized
        let keys = unsafe { MaybeUninit::array_assume_init(self.keys) };
        let cmp = u8x16::splat(key_fragment)
            .simd_eq(u8x16::from_array(keys))
            .to_bitmask() as u32;
        let mask = (1u32 << self.header.num_children()) - 1;
        let bitfield = cmp & mask;
        if bitfield != 0 {
            Some(bitfield.trailing_zeros() as usize)
        } else {
            None
        }
    }

    #[cfg(not(feature = "nightly"))]
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize> {
        let (keys, _) = self.initialized_portion();
        for (child_index, key) in keys.iter().enumerate() {
            if key_fragment == *key {
                return Some(child_index);
            }
        }

        None
    }

    #[cfg(feature = "nightly")]
    fn find_write_point(&self, key_fragment: u8) -> WritePoint {
        match self.lookup_child_index(key_fragment) {
            Some(child_index) => WritePoint::Existing(child_index),
            None => {
                // SAFETY: Even though the type is marked is uninit data, when
                // crated this is filled with initialized data, we just use it to
                // remind us that a portion might be uninitialized
                let keys = unsafe { MaybeUninit::array_assume_init(self.keys) };
                let cmp = u8x16::splat(key_fragment)
                    .simd_lt(u8x16::from_array(keys))
                    .to_bitmask() as u32;
                let mask = (1u32 << self.header.num_children()) - 1;
                let bitfield = cmp & mask;
                if bitfield != 0 {
                    WritePoint::Shift(bitfield.trailing_zeros() as usize)
                } else {
                    WritePoint::Last(self.header.num_children())
                }
            },
        }
    }

    #[cfg(not(feature = "nightly"))]
    fn find_write_point(&self, key_fragment: u8) -> WritePoint {
        let (keys, _) = self.initialized_portion();

        let mut child_index = 0;
        for key in keys {
            #[allow(clippy::comparison_chain)]
            if key_fragment < *key {
                return WritePoint::Shift(child_index);
            } else if key_fragment == *key {
                return WritePoint::Existing(child_index);
            }
            child_index += 1;
        }
        WritePoint::Last(child_index)
    }
}

impl<K, V, const PREFIX_LEN: usize> Node<PREFIX_LEN> for InnerNode16<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node16;
}

impl<K, V, const PREFIX_LEN: usize> InnerNode<PREFIX_LEN> for InnerNode16<K, V, PREFIX_LEN> {
    type GrownNode = InnerNode48<K, V, PREFIX_LEN>;
    type Iter<'a>
        = InnerNodeCompressedIter<'a, K, V, PREFIX_LEN>
    where
        Self: 'a;
    type ShrunkNode = InnerNode4<K, V, PREFIX_LEN>;

    fn header(&self) -> &Header<PREFIX_LEN> {
        &self.header
    }

    fn from_header(header: Header<PREFIX_LEN>) -> Self {
        Self {
            header,
            child_pointers: maybe_uninit_uninit_array(),
            keys: [MaybeUninit::new(0); 16],
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        self.lookup_child_inner(key_fragment)
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>) {
        self.write_child_inner(key_fragment, child_pointer)
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        self.remove_child_inner(key_fragment)
    }

    fn grow(&self) -> Self::GrownNode {
        self.grow_node48()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        self.change_block_size()
    }

    fn iter(&self) -> Self::Iter<'_> {
        self.inner_iter()
    }

    fn range(
        &self,
        bound: impl RangeBounds<u8>,
    ) -> impl DoubleEndedIterator<Item = (u8, OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>)>
           + std::iter::FusedIterator {
        self.inner_range_iter(bound)
    }

    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        let (keys, children) = self.initialized_portion();
        // SAFETY: Covered by the containing function
        unsafe {
            (
                keys.first().copied().unwrap_unchecked(),
                children.first().copied().unwrap_unchecked(),
            )
        }
    }

    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        let (keys, children) = self.initialized_portion();
        // SAFETY: Covered by the containing function
        unsafe {
            (
                keys.last().copied().unwrap_unchecked(),
                children.last().copied().unwrap_unchecked(),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        nodes::representation::tests::{
            inner_node_remove_child_test, inner_node_shrink_test, inner_node_write_child_test,
            FixtureReturn,
        },
        LeafNode, NodePtr,
    };

    use super::*;

    #[test]
    fn node4_lookup() {
        let mut n = InnerNode4::<Box<[u8]>, (), 16>::empty();
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        assert!(n.lookup_child(123).is_none());

        n.header.inc_num_children();
        n.header.inc_num_children();
        n.header.inc_num_children();

        n.keys[0].write(3);
        n.keys[1].write(123);
        n.keys[2].write(1);

        n.child_pointers[0].write(l1_ptr);
        n.child_pointers[1].write(l2_ptr);
        n.child_pointers[2].write(l3_ptr);

        assert_eq!(n.lookup_child(123), Some(l2_ptr));
    }

    #[test]
    fn node4_write_child() {
        inner_node_write_child_test(InnerNode4::<_, _, 16>::empty(), 4)
    }

    #[test]
    fn node4_remove_child() {
        inner_node_remove_child_test(InnerNode4::<_, _, 16>::empty(), 4)
    }

    #[test]
    #[should_panic]
    fn node4_write_child_full_panic() {
        inner_node_write_child_test(InnerNode4::<_, _, 16>::empty(), 5);
    }

    #[test]
    fn node4_grow() {
        let mut n4 = InnerNode4::<Box<[u8]>, (), 16>::empty();
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        n4.write_child(3, l1_ptr);
        n4.write_child(123, l2_ptr);
        n4.write_child(1, l3_ptr);

        let n16 = n4.grow();

        assert_eq!(n16.lookup_child(3), Some(l1_ptr));
        assert_eq!(n16.lookup_child(123), Some(l2_ptr));
        assert_eq!(n16.lookup_child(1), Some(l3_ptr));
        assert_eq!(n16.lookup_child(4), None);
    }

    #[test]
    #[should_panic = "unable to shrink a Node4, something went wrong!"]
    fn node4_shrink() {
        let n4 = InnerNode4::<Box<[u8]>, (), 16>::empty();

        n4.shrink();
    }

    #[test]
    fn node16_lookup() {
        let mut n = InnerNode16::<Box<[u8]>, (), 16>::empty();
        let mut l1 = LeafNode::with_no_siblings(Box::from([]), ());
        let mut l2 = LeafNode::with_no_siblings(Box::from([]), ());
        let mut l3 = LeafNode::with_no_siblings(Box::from([]), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        assert!(n.lookup_child(123).is_none());

        n.header.inc_num_children();
        n.header.inc_num_children();
        n.header.inc_num_children();

        n.keys[0].write(3);
        n.keys[1].write(123);
        n.keys[2].write(1);

        n.child_pointers[0].write(l1_ptr);
        n.child_pointers[1].write(l2_ptr);
        n.child_pointers[2].write(l3_ptr);

        assert_eq!(n.lookup_child(123), Some(l2_ptr));
    }

    #[test]
    fn node16_write_child() {
        inner_node_write_child_test(InnerNode16::<_, _, 16>::empty(), 16)
    }

    #[test]
    fn node16_remove_child() {
        inner_node_remove_child_test(InnerNode16::<_, _, 16>::empty(), 16)
    }

    #[test]
    #[should_panic]
    fn node16_write_child_full_panic() {
        inner_node_write_child_test(InnerNode16::<_, _, 16>::empty(), 17);
    }

    #[test]
    #[should_panic = "Node must be full to grow to node 48"]
    fn node16_grow_panic() {
        let mut n16 = InnerNode16::<Box<[u8]>, (), 16>::empty();
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        n16.write_child(3, l1_ptr);
        n16.write_child(123, l2_ptr);
        n16.write_child(1, l3_ptr);

        let _n48 = n16.grow();
    }

    #[test]
    fn node16_grow() {
        let mut n16 = InnerNode16::<Box<[u8]>, (), 16>::empty();
        let mut v = Vec::new();
        for i in 0..16 {
            let mut l = LeafNode::with_no_siblings(vec![].into(), ());
            let l_ptr = NodePtr::from(&mut l).to_opaque();
            v.push(l_ptr);
            n16.write_child(i * 2, l_ptr);
        }

        let n48 = n16.grow();

        for i in 0..16 {
            assert_eq!(n48.lookup_child(i * 2), Some(v[i as usize]));
        }
    }

    #[test]
    fn node16_shrink() {
        inner_node_shrink_test(InnerNode16::<_, _, 16>::empty(), 4);
    }

    #[test]
    #[should_panic = "Cannot change InnerNodeCompressed<16> to size 4 when it has more than 4 \
                      children. Currently has [5] children."]
    fn node16_shrink_too_many_children_panic() {
        inner_node_shrink_test(InnerNode16::<_, _, 16>::empty(), 5);
    }

    fn node4_fixture() -> FixtureReturn<InnerNode4<Box<[u8]>, (), 16>, 4> {
        let mut n4 = InnerNode4::empty();
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l4 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        n4.write_child(3, l1_ptr);
        n4.write_child(255, l2_ptr);
        n4.write_child(0u8, l3_ptr);
        n4.write_child(85, l4_ptr);

        (n4, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
    }

    #[test]
    fn node4_iterate() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node4_fixture();

        let mut iter = node.iter();

        assert_eq!(iter.next().unwrap(), (0u8, l3_ptr));
        assert_eq!(iter.next().unwrap(), (3, l1_ptr));
        assert_eq!(iter.next().unwrap(), (85, l4_ptr));
        assert_eq!(iter.next().unwrap(), (255, l2_ptr));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn node4_iterate_rev() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node4_fixture();

        let mut iter = node.iter().rev();

        assert_eq!(iter.next().unwrap(), (255, l2_ptr));
        assert_eq!(iter.next().unwrap(), (85, l4_ptr));
        assert_eq!(iter.next().unwrap(), (3, l1_ptr));
        assert_eq!(iter.next().unwrap(), (0u8, l3_ptr));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn node4_range_iterate() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node4_fixture();

        #[track_caller]
        fn check<K, V, const PREFIX_LEN: usize, const N: usize>(
            node: &InnerNodeCompressed<K, V, PREFIX_LEN, 4>,
            bound: impl RangeBounds<u8>,
            expected_pairs: [(u8, OpaqueNodePtr<K, V, PREFIX_LEN>); N],
        ) {
            let pairs = node.range(bound).collect::<Vec<_>>();
            assert_eq!(pairs, expected_pairs);
        }

        check(
            &node,
            (Bound::Included(0), Bound::Included(3)),
            [(0u8, l3_ptr), (3, l1_ptr)],
        );
        check(&node, (Bound::Excluded(0), Bound::Excluded(3)), []);
        check(
            &node,
            (Bound::Included(0), Bound::Included(0)),
            [(0u8, l3_ptr)],
        );
        check(
            &node,
            (Bound::Included(0), Bound::Included(255)),
            [(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (255, l2_ptr)],
        );
        check(
            &node,
            (Bound::Included(255), Bound::Included(255)),
            [(255, l2_ptr)],
        );
        check(&node, (Bound::Included(255), Bound::Excluded(255)), []);
        check(&node, (Bound::Excluded(255), Bound::Included(255)), []);
        check(
            &node,
            (Bound::Excluded(0), Bound::Excluded(255)),
            [(3, l1_ptr), (85, l4_ptr)],
        );
        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Unbounded),
            [(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (255, l2_ptr)],
        );
    }

    fn node4_fixture_empty_edges() -> FixtureReturn<InnerNode4<Box<[u8]>, (), 16>, 4> {
        let mut n4 = InnerNode4::empty();
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l4 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        n4.write_child(3, l1_ptr);
        n4.write_child(254, l2_ptr);
        n4.write_child(2u8, l3_ptr);
        n4.write_child(85, l4_ptr);

        (n4, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
    }

    #[test]
    fn node4_range_iterate_boundary_conditions() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node4_fixture_empty_edges();

        #[track_caller]
        fn check<K, V, const PREFIX_LEN: usize, const N: usize>(
            node: &InnerNodeCompressed<K, V, PREFIX_LEN, 4>,
            bound: impl RangeBounds<u8>,
            expected_pairs: [(u8, OpaqueNodePtr<K, V, PREFIX_LEN>); N],
        ) {
            let pairs = node.range(bound).collect::<Vec<_>>();
            assert_eq!(pairs, expected_pairs);
        }

        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Included(86)),
            [(2u8, l3_ptr), (3, l1_ptr), (85, l4_ptr)],
        );
        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Included(4)),
            [(2u8, l3_ptr), (3, l1_ptr)],
        );
        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Excluded(3)),
            [(2u8, l3_ptr)],
        );
        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Included(2)),
            [(2u8, l3_ptr)],
        );
        check(&node, (Bound::<u8>::Unbounded, Bound::Included(1)), []);
        check(&node, (Bound::<u8>::Unbounded, Bound::Included(0)), []);

        check(
            &node,
            (Bound::Included(1), Bound::<u8>::Unbounded),
            [(2u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (254, l2_ptr)],
        );
        check(
            &node,
            (Bound::Included(3), Bound::<u8>::Unbounded),
            [(3, l1_ptr), (85, l4_ptr), (254, l2_ptr)],
        );
        check(
            &node,
            (Bound::Excluded(84), Bound::<u8>::Unbounded),
            [(85, l4_ptr), (254, l2_ptr)],
        );
        check(
            &node,
            (Bound::Included(253), Bound::<u8>::Unbounded),
            [(254, l2_ptr)],
        );
        check(&node, (Bound::Included(255), Bound::<u8>::Unbounded), []);
    }

    #[test]
    #[should_panic = "range start and end are equal and excluded: (80)"]
    fn node4_range_iterate_out_of_bounds_panic_both_excluded() {
        let (node, _, [_l1_ptr, _l2_ptr, _l3_ptr, _l4_ptr]) = node4_fixture();

        let _pairs = node
            .range((Bound::Excluded(80), Bound::Excluded(80)))
            .collect::<Vec<_>>();
    }

    #[test]
    #[should_panic = "range start (80) is greater than range end (0)"]
    fn node4_range_iterate_start_greater_than_end() {
        let (node, _, [_l1_ptr, _l2_ptr, _l3_ptr, _l4_ptr]) = node4_fixture();

        let _pairs = node
            .range((Bound::Excluded(80), Bound::Included(0)))
            .collect::<Vec<_>>();
    }

    fn node16_fixture() -> FixtureReturn<InnerNode16<Box<[u8]>, (), 16>, 4> {
        let mut n16 = InnerNode16::empty();
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l4 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        n16.write_child(3, l1_ptr);
        n16.write_child(255, l2_ptr);
        n16.write_child(0u8, l3_ptr);
        n16.write_child(85, l4_ptr);

        (n16, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
    }

    #[test]
    fn node16_iterate() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node16_fixture();

        let mut iter = node.iter();

        assert_eq!(iter.next().unwrap(), (0u8, l3_ptr));
        assert_eq!(iter.next().unwrap(), (3, l1_ptr));
        assert_eq!(iter.next().unwrap(), (85, l4_ptr));
        assert_eq!(iter.next().unwrap(), (255, l2_ptr));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn node16_iterate_rev() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node16_fixture();

        let mut iter = node.iter().rev();

        assert_eq!(iter.next().unwrap(), (255, l2_ptr));
        assert_eq!(iter.next().unwrap(), (85, l4_ptr));
        assert_eq!(iter.next().unwrap(), (3, l1_ptr));
        assert_eq!(iter.next().unwrap(), (0u8, l3_ptr));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn node16_range_iterate() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node16_fixture();

        #[track_caller]
        fn check<K, V, const PREFIX_LEN: usize, const N: usize>(
            node: &InnerNodeCompressed<K, V, PREFIX_LEN, 16>,
            bound: impl RangeBounds<u8>,
            expected_pairs: [(u8, OpaqueNodePtr<K, V, PREFIX_LEN>); N],
        ) {
            let pairs = node.range(bound).collect::<Vec<_>>();
            assert_eq!(pairs, expected_pairs);
        }

        check(
            &node,
            (Bound::Included(0), Bound::Included(3)),
            [(0u8, l3_ptr), (3, l1_ptr)],
        );
        check(&node, (Bound::Excluded(0), Bound::Excluded(3)), []);
        check(
            &node,
            (Bound::Included(0), Bound::Included(0)),
            [(0u8, l3_ptr)],
        );
        check(
            &node,
            (Bound::Included(0), Bound::Included(255)),
            [(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (255, l2_ptr)],
        );
        check(
            &node,
            (Bound::Included(255), Bound::Included(255)),
            [(255, l2_ptr)],
        );
        check(&node, (Bound::Included(255), Bound::Excluded(255)), []);
        check(&node, (Bound::Excluded(255), Bound::Included(255)), []);
        check(
            &node,
            (Bound::Excluded(0), Bound::Excluded(255)),
            [(3, l1_ptr), (85, l4_ptr)],
        );
        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Unbounded),
            [(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (255, l2_ptr)],
        );
        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Included(86)),
            [(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr)],
        );
    }

    fn node16_fixture_empty_edges() -> FixtureReturn<InnerNode16<Box<[u8]>, (), 16>, 4> {
        let mut n16 = InnerNode16::empty();
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l4 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        n16.write_child(3, l1_ptr);
        n16.write_child(254, l2_ptr);
        n16.write_child(2u8, l3_ptr);
        n16.write_child(85, l4_ptr);

        (n16, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
    }

    #[test]
    fn node16_range_iterate_boundary_conditions() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node16_fixture_empty_edges();

        #[track_caller]
        fn check<K, V, const PREFIX_LEN: usize, const N: usize>(
            node: &InnerNodeCompressed<K, V, PREFIX_LEN, 16>,
            bound: impl RangeBounds<u8>,
            expected_pairs: [(u8, OpaqueNodePtr<K, V, PREFIX_LEN>); N],
        ) {
            let pairs = node.range(bound).collect::<Vec<_>>();
            assert_eq!(pairs, expected_pairs);
        }

        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Included(86)),
            [(2u8, l3_ptr), (3, l1_ptr), (85, l4_ptr)],
        );
        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Included(4)),
            [(2u8, l3_ptr), (3, l1_ptr)],
        );
        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Excluded(3)),
            [(2u8, l3_ptr)],
        );
        check(
            &node,
            (Bound::<u8>::Unbounded, Bound::Included(2)),
            [(2u8, l3_ptr)],
        );
        check(&node, (Bound::<u8>::Unbounded, Bound::Included(1)), []);
        check(&node, (Bound::<u8>::Unbounded, Bound::Included(0)), []);

        check(
            &node,
            (Bound::Included(1), Bound::<u8>::Unbounded),
            [(2u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (254, l2_ptr)],
        );
        check(
            &node,
            (Bound::Included(3), Bound::<u8>::Unbounded),
            [(3, l1_ptr), (85, l4_ptr), (254, l2_ptr)],
        );
        check(
            &node,
            (Bound::Excluded(84), Bound::<u8>::Unbounded),
            [(85, l4_ptr), (254, l2_ptr)],
        );
        check(
            &node,
            (Bound::Included(253), Bound::<u8>::Unbounded),
            [(254, l2_ptr)],
        );
        check(&node, (Bound::Included(255), Bound::<u8>::Unbounded), []);
    }

    #[test]
    fn node16_range_edge_cases() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node16_fixture();

        let pairs = node
            .range((Bound::<u8>::Excluded(84), Bound::Unbounded))
            .collect::<Vec<_>>();
        assert_eq!(pairs, &[(85, l4_ptr), (255, l2_ptr),]);

        let pairs = node
            .range((Bound::<u8>::Unbounded, Bound::Excluded(4)))
            .collect::<Vec<_>>();
        assert_eq!(pairs, &[(0u8, l3_ptr), (3, l1_ptr)]);
    }

    #[test]
    #[should_panic = "range start and end are equal and excluded: (80)"]
    fn node16_range_iterate_out_of_bounds_panic_both_excluded() {
        let (node, _, [_l1_ptr, _l2_ptr, _l3_ptr, _l4_ptr]) = node16_fixture();

        let pairs = node
            .range((Bound::Excluded(80), Bound::Excluded(80)))
            .collect::<Vec<_>>();
        assert_eq!(pairs, &[]);
    }

    #[test]
    #[should_panic = "range start (80) is greater than range end (0)"]
    fn node16_range_iterate_start_greater_than_end() {
        let (node, _, [_l1_ptr, _l2_ptr, _l3_ptr, _l4_ptr]) = node16_fixture();

        let _pairs = node
            .range((Bound::Excluded(80), Bound::Included(0)))
            .collect::<Vec<_>>();
    }
}
