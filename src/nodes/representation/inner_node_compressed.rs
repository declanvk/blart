use crate::{
    rust_nightly_apis::{assume, maybe_uninit_slice_assume_init_ref, maybe_uninit_uninit_array},
    AsBytes, Header, InnerNode, InnerNode48, Node, NodePtr, NodeType, OpaqueNodePtr,
    RestrictedNodeIndex,
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
pub struct InnerNodeCompressed<K: AsBytes, V, const PREFIX_LEN: usize, const SIZE: usize> {
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

impl<K: AsBytes, V, const PREFIX_LEN: usize, const SIZE: usize> Clone
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

impl<K: AsBytes, V, const PREFIX_LEN: usize, const SIZE: usize> fmt::Debug
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

impl<K: AsBytes, V, const PREFIX_LEN: usize, const SIZE: usize>
    InnerNodeCompressed<K, V, PREFIX_LEN, SIZE>
{
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
        debug_assert!(
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

        debug_assert_eq!(
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

    /// Deep clones the inner node by allocating memory to a new one
    fn inner_deep_clone(&self) -> NodePtr<PREFIX_LEN, Self>
    where
        K: Clone,
        V: Clone,
        Self: InnerNode<PREFIX_LEN, Key = K, Value = V>,
    {
        let mut node = NodePtr::allocate_node_ptr(Self::from_header(self.header.clone()));
        let node_ref = node.as_mut_safe();
        for (idx, (key_fragment, child_pointer)) in self.iter().enumerate() {
            let child_pointer = child_pointer.deep_clone();
            unsafe { node_ref.write_child_at(idx, key_fragment, child_pointer) };
        }

        node
    }
}

/// Node that references between 2 and 4 children
pub type InnerNode4<K, V, const PREFIX_LEN: usize> = InnerNodeCompressed<K, V, PREFIX_LEN, 4>;

impl<K: AsBytes, V, const PREFIX_LEN: usize> SearchInnerNodeCompressed
    for InnerNode4<K, V, PREFIX_LEN>
{
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

impl<K: AsBytes, V, const PREFIX_LEN: usize> Node<PREFIX_LEN> for InnerNode4<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node4;
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> InnerNode<PREFIX_LEN>
    for InnerNode4<K, V, PREFIX_LEN>
{
    type GrownNode = InnerNode16<K, V, PREFIX_LEN>;
    type Iter<'a> = InnerNodeCompressedIter<'a, K, V, PREFIX_LEN> where Self: 'a;
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

    #[inline(always)]
    fn deep_clone(&self) -> NodePtr<PREFIX_LEN, Self>
    where
        K: Clone,
        V: Clone,
    {
        self.inner_deep_clone()
    }
}

/// Node that references between 5 and 16 children
pub type InnerNode16<K, V, const PREFIX_LEN: usize> = InnerNodeCompressed<K, V, PREFIX_LEN, 16>;

impl<K: AsBytes, V, const PREFIX_LEN: usize> SearchInnerNodeCompressed
    for InnerNode16<K, V, PREFIX_LEN>
{
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

impl<K: AsBytes, V, const PREFIX_LEN: usize> Node<PREFIX_LEN> for InnerNode16<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node16;
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> InnerNode<PREFIX_LEN>
    for InnerNode16<K, V, PREFIX_LEN>
{
    type GrownNode = InnerNode48<K, V, PREFIX_LEN>;
    type Iter<'a> = InnerNodeCompressedIter<'a, K, V, PREFIX_LEN> where Self: 'a;
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

    #[inline(always)]
    fn deep_clone(&self) -> NodePtr<PREFIX_LEN, Self>
    where
        K: Clone,
        V: Clone,
    {
        self.inner_deep_clone()
    }
}
