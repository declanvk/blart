use core::{
    cmp::Ordering,
    error::Error,
    fmt,
    iter::{Enumerate, FusedIterator},
    mem::{self, MaybeUninit},
    ops::Bound,
    slice::Iter,
};
#[cfg(feature = "nightly")]
use core::{
    iter::{FilterMap, Map},
    simd::{cmp::SimdPartialEq, u8x64},
};

use crate::{
    raw::{
        Header, InnerNode, InnerNode16, InnerNode256, InnerNodeCompressed, Node, NodeType,
        OpaqueNodePtr,
    },
    rust_nightly_apis::{maybe_uninit_slice_assume_init_mut, maybe_uninit_slice_assume_init_ref},
};

/// A restricted index only valid from 0 to LIMIT - 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct RestrictedNodeIndex<const LIMIT: u8>(u8);

impl<const LIMIT: u8> RestrictedNodeIndex<LIMIT> {
    /// A placeholder index value that indicates that the index is not
    /// occupied
    pub const EMPTY: Self = RestrictedNodeIndex(LIMIT);

    /// Return true if the given index is the empty sentinel value
    pub fn is_empty(self) -> bool {
        self == Self::EMPTY
    }
}

impl<const LIMIT: u8> From<RestrictedNodeIndex<LIMIT>> for u8 {
    fn from(src: RestrictedNodeIndex<LIMIT>) -> Self {
        src.0
    }
}

impl<const LIMIT: u8> From<RestrictedNodeIndex<LIMIT>> for usize {
    fn from(src: RestrictedNodeIndex<LIMIT>) -> Self {
        usize::from(src.0)
    }
}

impl<const LIMIT: u8> TryFrom<usize> for RestrictedNodeIndex<LIMIT> {
    type Error = TryFromByteError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value < usize::from(LIMIT) {
            Ok(RestrictedNodeIndex(value as u8))
        } else {
            Err(TryFromByteError(LIMIT, value))
        }
    }
}

impl<const LIMIT: u8> TryFrom<u8> for RestrictedNodeIndex<LIMIT> {
    type Error = TryFromByteError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value < LIMIT {
            Ok(RestrictedNodeIndex(value))
        } else {
            Err(TryFromByteError(LIMIT, usize::from(value)))
        }
    }
}

impl<const LIMIT: u8> PartialOrd for RestrictedNodeIndex<LIMIT> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.0 == LIMIT || other.0 == LIMIT {
            None
        } else {
            Some(self.0.cmp(&other.0))
        }
    }
}

/// The error type returned when attempting to construct an index outside
/// the accepted range of a PartialNodeIndex.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TryFromByteError(u8, usize);

impl fmt::Display for TryFromByteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Input value [{}] is greater than the allowed maximum [{}] for PartialNodeIndex.",
            self.1, self.0
        )
    }
}

impl Error for TryFromByteError {}

/// Node that references between 17 and 49 children
#[repr(C, align(8))]
pub struct InnerNode48<K, V, const PREFIX_LEN: usize> {
    /// The common node fields.
    pub header: Header<PREFIX_LEN>,
    /// An array that maps key bytes (as the index) to the index value in
    /// the `child_pointers` array.
    ///
    /// All the `child_indices` values are guaranteed to be
    /// `PartialNodeIndex<48>::EMPTY` when the node is constructed.
    pub child_indices: [RestrictedNodeIndex<48>; 256],
    /// For each element in this array, it is assumed to be initialized if
    /// there is a index in the `child_indices` array that points to
    /// it
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<K, V, PREFIX_LEN>>; 48],
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for InnerNode48<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode48")
            .field("header", &self.header)
            .field("child_indices", &self.child_indices)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<K, V, const PREFIX_LEN: usize> Clone for InnerNode48<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_indices: self.child_indices,
            child_pointers: self.child_pointers,
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> InnerNode48<K, V, PREFIX_LEN> {
    /// Return the initialized portions of the child pointer array.
    pub fn initialized_child_pointers(&self) -> &[OpaqueNodePtr<K, V, PREFIX_LEN>] {
        unsafe {
            // SAFETY: The array prefix with length `header.num_children` is guaranteed to
            // be initialized
            core::hint::assert_unchecked(self.header.num_children() <= self.child_pointers.len());
            maybe_uninit_slice_assume_init_ref(&self.child_pointers[..self.header.num_children()])
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> Node<PREFIX_LEN> for InnerNode48<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node48;
}

impl<K, V, const PREFIX_LEN: usize> InnerNode<PREFIX_LEN> for InnerNode48<K, V, PREFIX_LEN> {
    type GrownNode = InnerNode256<K, V, PREFIX_LEN>;
    #[cfg(not(feature = "nightly"))]
    type Iter<'a>
        = Node48Iter<'a, K, V, PREFIX_LEN>
    where
        Self: 'a;
    #[cfg(feature = "nightly")]
    type Iter<'a>
        = Map<
        FilterMap<
            Enumerate<Iter<'a, RestrictedNodeIndex<48>>>,
            impl FnMut((usize, &'a RestrictedNodeIndex<48>)) -> Option<(u8, usize)>,
        >,
        impl FnMut((u8, usize)) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>),
    >
    where
        Self: 'a;
    type ShrunkNode = InnerNode16<K, V, PREFIX_LEN>;

    fn header(&self) -> &Header<PREFIX_LEN> {
        &self.header
    }

    fn from_header(header: Header<PREFIX_LEN>) -> Self {
        InnerNode48 {
            header,
            child_indices: [RestrictedNodeIndex::<48>::EMPTY; 256],
            child_pointers: [MaybeUninit::uninit(); 48],
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        let index = &self.child_indices[usize::from(key_fragment)];
        let child_pointers = self.initialized_child_pointers();
        if !index.is_empty() {
            let idx = usize::from(*index);

            unsafe {
                // SAFETY: If `idx` is out of bounds we have more than
                // 48 children in this node, so it should have already
                // grown. So it's safe to assume that it's in bounds
                core::hint::assert_unchecked(idx < child_pointers.len());
            }
            Some(child_pointers[idx])
        } else {
            None
        }
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>) {
        let key_fragment_idx = usize::from(key_fragment);
        let child_index = if self.child_indices[key_fragment_idx] == RestrictedNodeIndex::EMPTY {
            let child_index = self.header.num_children();
            debug_assert!(child_index < self.child_pointers.len(), "node is full");

            // SAFETY: By construction the number of children in the header
            // is kept in sync with the number of children written in the node
            // and if this number exceeds the maximum len the node should have
            // already grown. So we know for a fact that that num_children <= node len.
            //
            // With this we know that child_index is <= 47, because at the 48th time
            // calling this function for writing, the current len will bet 47, and
            // after this insert we increment it to 48, so this symbolizes that the
            // node is full and before calling this function again the node should
            // have already grown
            self.child_indices[key_fragment_idx] =
                unsafe { RestrictedNodeIndex::try_from(child_index).unwrap_unchecked() };
            self.header.inc_num_children();
            child_index
        } else {
            // overwrite existing
            usize::from(self.child_indices[key_fragment_idx])
        };

        // SAFETY: This index can be up to <= 47 as described above

        unsafe {
            core::hint::assert_unchecked(child_index < self.child_pointers.len());
            self.child_pointers
                .get_unchecked_mut(child_index)
                .write(child_pointer);
        }
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        let restricted_index = self.child_indices[usize::from(key_fragment)];
        if restricted_index.is_empty() {
            return None;
        }

        // Replace child pointer with uninitialized value, even though it may possibly
        // be overwritten by the compaction step
        let child_ptr = mem::replace(
            &mut self.child_pointers[usize::from(restricted_index)],
            MaybeUninit::uninit(),
        );

        // Copy all the child_pointer values in higher indices down by one.
        self.child_pointers.copy_within(
            (usize::from(restricted_index) + 1)..self.header.num_children(),
            usize::from(restricted_index),
        );

        // Take all child indices that are greater than the index we're removing, and
        // subtract one so that they remain valid
        for other_restrict_index in &mut self.child_indices {
            if matches!(
                restricted_index.partial_cmp(other_restrict_index),
                Some(Ordering::Less)
            ) {
                // PANIC SAFETY: This will not underflow, because it is guaranteed to be
                // greater than at least 1 other index. This will not panic in the
                // `try_from` because the new value is derived from an existing restricted
                // index.
                *other_restrict_index =
                    RestrictedNodeIndex::try_from(other_restrict_index.0 - 1).unwrap();
            }
        }

        self.child_indices[usize::from(key_fragment)] = RestrictedNodeIndex::EMPTY;
        self.header.dec_num_children();
        // SAFETY: This child pointer value is initialized because we got it by using a
        // non-`RestrictedNodeIndex::<>::EMPTY` index from the child indices array.
        Some(unsafe { MaybeUninit::assume_init(child_ptr) })
    }

    fn grow(&self) -> Self::GrownNode {
        let header = self.header.clone();
        let mut child_pointers = [None; 256];
        let initialized_child_pointers = self.initialized_child_pointers();
        for (key_fragment, idx) in self.child_indices.iter().enumerate() {
            if idx.is_empty() {
                continue;
            }

            let idx = usize::from(*idx);

            unsafe {
                // SAFETY: When growing initialized_child_pointers should be full
                // i.e initialized_child_pointers len == 48. And idx <= 47, since
                // we can't insert in a full, node
                core::hint::assert_unchecked(idx < initialized_child_pointers.len());
            }
            let child_pointer = initialized_child_pointers[idx];
            child_pointers[key_fragment] = Some(child_pointer);
        }

        InnerNode256 {
            header,
            child_pointers,
        }
    }

    fn shrink(&self) -> Self::ShrunkNode {
        assert!(
            self.header.num_children() <= 16,
            "Cannot shrink a Node48 when it has more than 16 children. Currently has [{}] \
             children.",
            self.header.num_children()
        );

        let header = self.header.clone();

        let mut key_and_child_ptrs = [MaybeUninit::uninit(); 16];

        for (idx, value) in self.iter().enumerate() {
            key_and_child_ptrs[idx].write(value);
        }

        let init_key_and_child_ptrs = {
            // SAFETY: The first `num_children` are guaranteed to be initialized in this
            // array because the previous iterator loops through all children of the inner
            // node.
            let init_key_and_child_ptrs = unsafe {
                maybe_uninit_slice_assume_init_mut(&mut key_and_child_ptrs[..header.num_children()])
            };

            init_key_and_child_ptrs.sort_unstable_by_key(|(key_byte, _)| *key_byte);

            init_key_and_child_ptrs
        };

        let mut keys = [MaybeUninit::uninit(); 16];
        let mut child_pointers = [MaybeUninit::uninit(); 16];

        for (idx, (key_byte, child_ptr)) in init_key_and_child_ptrs.iter().copied().enumerate() {
            keys[idx].write(key_byte);
            child_pointers[idx].write(child_ptr);
        }

        InnerNodeCompressed {
            header,
            keys,
            child_pointers,
        }
    }

    fn iter(&self) -> Self::Iter<'_> {
        let child_pointers = self.initialized_child_pointers();

        #[cfg(not(feature = "nightly"))]
        {
            Node48Iter {
                it: self.child_indices.iter().enumerate(),
                child_pointers,
            }
        }

        #[cfg(feature = "nightly")]
        {
            self.child_indices
                .iter()
                .enumerate()
                .filter_map(|(key, idx)| {
                    (!idx.is_empty()).then_some((key as u8, usize::from(*idx)))
                })
                // SAFETY: By the construction of `Self` idx, must always
                // be inbounds
                .map(|(key, idx)| unsafe { (key, *child_pointers.get_unchecked(idx)) })
        }
    }

    fn range(
        &self,
        bound: impl core::ops::RangeBounds<u8>,
    ) -> impl DoubleEndedIterator<Item = (u8, OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>)>
           + FusedIterator {
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

        let child_pointers = self.initialized_child_pointers();

        let start = bound.start_bound().map(|val| usize::from(*val));
        let key_offset = match bound.start_bound() {
            core::ops::Bound::Included(val) => *val,
            core::ops::Bound::Excluded(val) => val.saturating_add(1),
            core::ops::Bound::Unbounded => 0,
        };
        let end = bound.end_bound().map(|val| usize::from(*val));

        self.child_indices[(start, end)]
            .iter()
            .enumerate()
            .filter_map(|(key, idx)| {
                // normally `enumerate()` has elements of (idx, val), but we're using the index
                // as the key since it ranges from [0, 256)
                (!idx.is_empty()).then_some((key as u8, usize::from(*idx)))
            })
            // SAFETY: By the construction of `Self` idx, must always
            // be inbounds
            .map(move |(key, idx)| unsafe {
                (
                    key.saturating_add(key_offset),
                    *child_pointers.get_unchecked(idx),
                )
            })
    }

    #[cfg(feature = "nightly")]
    #[cfg_attr(test, mutants::skip)]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        // SAFETY: Since `RestrictedNodeIndex` is
        // repr(u8) is safe to transmute it
        let child_indices: &[u8; 256] = unsafe { core::mem::transmute(&self.child_indices) };
        let empty = u8x64::splat(48);
        let r0 = u8x64::from_array(child_indices[0..64].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r1 = u8x64::from_array(child_indices[64..128].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r2 = u8x64::from_array(child_indices[128..192].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r3 = u8x64::from_array(child_indices[192..256].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();

        let key = if r0 != u64::MAX {
            r0.trailing_ones()
        } else if r1 != u64::MAX {
            r1.trailing_ones() + 64
        } else if r2 != u64::MAX {
            r2.trailing_ones() + 128
        } else {
            r3.trailing_ones() + 192
        } as usize;

        unsafe {
            // SAFETY: key can be at up to 256, but we are in a inner node
            // this means that this node has at least 1 child (it's even more
            // strict since, if we have 1 child the node would collapse), so we
            // know that exists at least one idx where != 48
            core::hint::assert_unchecked(key < self.child_indices.len());
        }

        let idx = usize::from(self.child_indices[key]);
        let child_pointers = self.initialized_child_pointers();

        unsafe {
            // SAFETY: We know that idx is in bounds, because the value can't be
            // constructed if it >= 48 and also it has to be < num children, since
            // it's constructed from the num children before being incremented during
            // insertion process
            core::hint::assert_unchecked(idx < child_pointers.len());
        }

        (key as u8, child_pointers[idx])
    }

    #[cfg(not(feature = "nightly"))]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        for (key, idx) in self.child_indices.iter().enumerate() {
            if idx.is_empty() {
                continue;
            }
            let child_pointers = self.initialized_child_pointers();
            return (key as u8, child_pointers[usize::from(*idx)]);
        }
        unreachable!("inner node must have non-zero number of children");
    }

    #[cfg(feature = "nightly")]
    #[cfg_attr(test, mutants::skip)]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        // SAFETY: Since `RestrictedNodeIndex` is
        // repr(u8) is safe to transmute it
        let child_indices: &[u8; 256] = unsafe { core::mem::transmute(&self.child_indices) };
        let empty = u8x64::splat(48);
        let r0 = u8x64::from_array(child_indices[0..64].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r1 = u8x64::from_array(child_indices[64..128].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r2 = u8x64::from_array(child_indices[128..192].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r3 = u8x64::from_array(child_indices[192..256].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();

        let key = if r3 != u64::MAX {
            255 - r3.leading_ones()
        } else if r2 != u64::MAX {
            191 - r2.leading_ones()
        } else if r1 != u64::MAX {
            127 - r1.leading_ones()
        } else {
            // SAFETY: This subtraction can't fail, because we know that
            // we have at least one child, so the number of leading ones
            // in this last case is <= 63
            63 - r0.leading_ones()
        } as usize;

        unsafe {
            // SAFETY: idx can be at up to 255 so it's in bounds
            core::hint::assert_unchecked(key < self.child_indices.len());
        }

        let idx = usize::from(self.child_indices[key]);
        let child_pointers = self.initialized_child_pointers();

        unsafe {
            // SAFETY: We know that idx is in bounds, because the value can't be
            // constructed if it >= 48 and also it has to be < num children, since
            // it's constructed from the num children before being incremented during
            // insertion process
            core::hint::assert_unchecked(idx < child_pointers.len());
        }

        (key as u8, child_pointers[idx])
    }

    #[cfg(not(feature = "nightly"))]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        for (key, idx) in self.child_indices.iter().enumerate().rev() {
            if idx.is_empty() {
                continue;
            }
            let child_pointers = self.initialized_child_pointers();
            return (key as u8, child_pointers[usize::from(*idx)]);
        }
        unreachable!("inner node must have non-zero number of children");
    }
}

/// This struct is an iterator over the children of a [`InnerNode48`].
#[cfg(not(feature = "nightly"))]
pub struct Node48Iter<'a, K, V, const PREFIX_LEN: usize> {
    pub(crate) it: Enumerate<Iter<'a, RestrictedNodeIndex<48>>>,
    pub(crate) child_pointers: &'a [OpaqueNodePtr<K, V, PREFIX_LEN>],
}

#[cfg(not(feature = "nightly"))]
impl<K, V, const PREFIX_LEN: usize> Iterator for Node48Iter<'_, K, V, PREFIX_LEN> {
    type Item = (u8, OpaqueNodePtr<K, V, PREFIX_LEN>);

    fn next(&mut self) -> Option<Self::Item> {
        for (key, idx) in self.it.by_ref() {
            if idx.is_empty() {
                continue;
            }
            let key = key as u8;
            // SAFETY: This idx is in bounds, since the number
            // of iterations is always <= 48 (i.e 0-47)
            let child_pointer = unsafe { *self.child_pointers.get_unchecked(usize::from(*idx)) };
            return Some((key, child_pointer));
        }
        None
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V, const PREFIX_LEN: usize> DoubleEndedIterator for Node48Iter<'_, K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some((key, idx)) = self.it.next_back() {
            if idx.is_empty() {
                continue;
            }
            let key = key as u8;
            // SAFETY: This idx is in bounds, since the number
            // of iterations is always <= 48 (i.e 0-47)
            let child_pointer = unsafe { *self.child_pointers.get_unchecked(usize::from(*idx)) };
            return Some((key, child_pointer));
        }
        None
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V, const PREFIX_LEN: usize> FusedIterator for Node48Iter<'_, K, V, PREFIX_LEN> {}

#[cfg(test)]
mod tests {
    use alloc::{boxed::Box, vec::Vec};
    use core::ops::{Bound, RangeBounds};

    use super::*;
    use crate::raw::{
        representation::tests::{
            inner_node_min_max_test, inner_node_remove_child_test, inner_node_shrink_test,
            inner_node_write_child_test, FixtureReturn,
        },
        LeafNode, NodePtr,
    };

    #[test]
    fn lookup() {
        let mut n = InnerNode48::<Box<[u8]>, (), 16>::empty();
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

        n.child_indices[1] = 2usize.try_into().unwrap();
        n.child_indices[3] = 0usize.try_into().unwrap();
        n.child_indices[123] = 1usize.try_into().unwrap();

        n.child_pointers[0].write(l1_ptr);
        n.child_pointers[1].write(l2_ptr);
        n.child_pointers[2].write(l3_ptr);

        assert_eq!(n.lookup_child(123), Some(l2_ptr));
    }

    #[test]
    fn write_child() {
        inner_node_write_child_test(InnerNode48::<_, _, 16>::empty(), 48)
    }

    #[test]
    fn remove_child() {
        inner_node_remove_child_test(InnerNode48::<_, _, 16>::empty(), 48)
    }

    #[test]
    #[should_panic]
    fn write_child_full_panic() {
        inner_node_write_child_test(InnerNode48::<_, _, 16>::empty(), 49);
    }

    #[test]
    fn grow() {
        let mut n48 = InnerNode48::<Box<[u8]>, (), 16>::empty();
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        n48.write_child(3, l1_ptr);
        n48.write_child(123, l2_ptr);
        n48.write_child(1, l3_ptr);

        let n256 = n48.grow();

        assert_eq!(n256.lookup_child(3), Some(l1_ptr));
        assert_eq!(n256.lookup_child(123), Some(l2_ptr));
        assert_eq!(n256.lookup_child(1), Some(l3_ptr));
        assert_eq!(n256.lookup_child(4), None);
    }

    #[test]
    fn shrink() {
        inner_node_shrink_test(InnerNode48::<_, _, 16>::empty(), 16);
    }

    #[test]
    #[should_panic = "Cannot shrink a Node48 when it has more than 16 children. Currently has [17] \
                      children."]
    fn shrink_too_many_children_panic() {
        inner_node_shrink_test(InnerNode48::<_, _, 16>::empty(), 17);
    }

    #[test]
    fn min_max() {
        inner_node_min_max_test(InnerNode48::<_, _, 16>::empty(), 48);
    }

    fn fixture() -> FixtureReturn<InnerNode48<Box<[u8]>, (), 16>, 4> {
        let mut n4 = InnerNode48::empty();
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
    fn iterate() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = fixture();

        let mut iter = node.iter();

        assert_eq!(iter.next().unwrap(), (0u8, l3_ptr));
        assert_eq!(iter.next().unwrap(), (3, l1_ptr));
        assert_eq!(iter.next().unwrap(), (85, l4_ptr));
        assert_eq!(iter.next().unwrap(), (255, l2_ptr));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iterate_rev() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = fixture();

        let mut iter = node.iter().rev();

        assert_eq!(iter.next().unwrap(), (255, l2_ptr));
        assert_eq!(iter.next().unwrap(), (85, l4_ptr));
        assert_eq!(iter.next().unwrap(), (3, l1_ptr));
        assert_eq!(iter.next().unwrap(), (0u8, l3_ptr));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn range_iterate() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = fixture();

        #[track_caller]
        fn check<K, V, const PREFIX_LEN: usize, const N: usize>(
            node: &InnerNode48<K, V, PREFIX_LEN>,
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

    fn fixture_empty_edges() -> FixtureReturn<InnerNode48<Box<[u8]>, (), 16>, 4> {
        let mut n4 = InnerNode48::empty();
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
    fn range_iterate_boundary_conditions() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = fixture_empty_edges();

        #[track_caller]
        fn check<K, V, const PREFIX_LEN: usize, const N: usize>(
            node: &InnerNode48<K, V, PREFIX_LEN>,
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
    fn range_iterate_out_of_bounds_panic_both_excluded() {
        let (node, _, [_l1_ptr, _l2_ptr, _l3_ptr, _l4_ptr]) = fixture();

        let pairs = node
            .range((Bound::Excluded(80), Bound::Excluded(80)))
            .collect::<Vec<_>>();
        assert_eq!(pairs, &[]);
    }

    #[test]
    #[should_panic = "range start (80) is greater than range end (0)"]
    fn range_iterate_start_greater_than_end() {
        let (node, _, [_l1_ptr, _l2_ptr, _l3_ptr, _l4_ptr]) = fixture();

        let _pairs = node
            .range((Bound::Excluded(80), Bound::Included(0)))
            .collect::<Vec<_>>();
    }
}
