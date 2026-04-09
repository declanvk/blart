#[cfg(feature = "nightly")]
use core::simd::{cmp::SimdPartialEq, u8x64};
use core::{
    fmt,
    iter::{Enumerate, FusedIterator},
    mem::{self, MaybeUninit},
    slice::Iter,
};

use self::index::NonMaxIndex;
use crate::{
    raw::{
        representation::assert_valid_range_bounds, Header, InnerNode, InnerNode16, InnerNodeCommon,
        InnerNodeDirect, InnerNodeSorted, Node, NodeType, OpaqueNodePtr,
    },
    rust_nightly_apis::maybe_uninit_slice_assume_init_ref,
};

mod index;

/// Inner node type that uses a direct lookup for the key byte and uses the
/// resulting value to lookup the child pointer.
///
/// It is "indirect" in the sense that we use the value of the key byte to get
/// an index that lets us finally look up the child pointer.
#[repr(C, align(8))]
pub struct InnerNodeIndirect<K, V, const PREFIX_LEN: usize, const SIZE: usize> {
    /// The common node fields.
    pub header: Header<PREFIX_LEN>,
    /// For each element in this array, it is assumed to be initialized if
    /// there is a index in the `child_indices` array that points to
    /// it
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<K, V, PREFIX_LEN>>; SIZE],
    /// An array that maps key bytes (as the index) to the index value in
    /// the `child_pointers` array.
    ///
    /// All the `child_indices` values are guaranteed to be
    /// `None` when the node is constructed.
    pub child_indices: [Option<NonMaxIndex>; 256],
}

impl<K, V, const PREFIX_LEN: usize, const SIZE: usize, const OTHER_SIZE: usize>
    From<&InnerNodeSorted<K, V, PREFIX_LEN, OTHER_SIZE>>
    for InnerNodeIndirect<K, V, PREFIX_LEN, SIZE>
{
    fn from(value: &InnerNodeSorted<K, V, PREFIX_LEN, OTHER_SIZE>) -> Self {
        assert!(
            value.header.num_children() <= SIZE,
            "Cannot shrink a InnerNodeDirect when it has more than {SIZE} children. Currently has \
             [{}] children.",
            value.header.num_children()
        );

        let header = value.header.clone();
        let mut child_indices = [None; 256];
        let mut child_pointers = [MaybeUninit::uninit(); SIZE];

        let (keys, _) = value.initialized_portion();

        assert_eq!(
            keys.len(),
            value.keys.len(),
            "Node must be full to grow to node 48"
        );

        for (index, key) in keys.iter().copied().enumerate() {
            // SAFETY: This `try_from` will not panic because index is guaranteed to
            // be 15 or less because of the length of the `InnerNode16.keys` array.
            child_indices[usize::from(key)] =
                Some(unsafe { NonMaxIndex::try_from(index).unwrap_unchecked() });
        }

        let num_children = header.num_children();

        unsafe {
            // SAFETY: By construction the number of children in the header
            // is kept in sync with the number of children written in the node
            // and if this number exceeds the maximum len the node should have
            // already grown. So we know for a fact that that num_children <= node len
            core::hint::assert_unchecked(num_children <= value.child_pointers.len());

            // SAFETY: We know that the new size is >= old size, so this is safe
            core::hint::assert_unchecked(num_children <= child_pointers.len());
        }

        child_pointers[..num_children].copy_from_slice(&value.child_pointers[..num_children]);

        Self {
            header,
            child_indices,
            child_pointers,
        }
    }
}

impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> From<&InnerNodeDirect<K, V, PREFIX_LEN>>
    for InnerNodeIndirect<K, V, PREFIX_LEN, SIZE>
{
    fn from(value: &InnerNodeDirect<K, V, PREFIX_LEN>) -> Self {
        assert!(
            value.header.num_children() <= SIZE,
            "Cannot shrink a InnerNodeDirect when it has more than {SIZE} children. Currently has \
             [{}] children.",
            value.header.num_children()
        );

        let header = value.header.clone();
        let mut child_indices = [None; 256];
        let mut child_pointers = [MaybeUninit::uninit(); SIZE];

        for (child_index, (key_byte, child_ptr)) in value.iter().enumerate() {
            // PANIC SAFETY: This `try_from` will not panic because the `next_index` value
            // is guaranteed to be 48 or less by the `assert!(num_children < 48)` at the
            // start of the function.
            let key_byte = usize::from(key_byte);
            child_indices[key_byte] = Some(NonMaxIndex::try_from(child_index).unwrap());
            child_pointers[child_index].write(child_ptr);
        }

        Self {
            header,
            child_indices,
            child_pointers,
        }
    }
}

impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> fmt::Debug
    for InnerNodeIndirect<K, V, PREFIX_LEN, SIZE>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode48")
            .field("header", &self.header)
            .field("child_indices", &self.child_indices)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> Clone
    for InnerNodeIndirect<K, V, PREFIX_LEN, SIZE>
{
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_indices: self.child_indices,
            child_pointers: self.child_pointers,
        }
    }
}

impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> InnerNodeIndirect<K, V, PREFIX_LEN, SIZE> {
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

// SAFETY: `InnerNode48` is `repr(C)` and has a `Header` as the first field
unsafe impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> InnerNodeCommon<K, V, PREFIX_LEN>
    for InnerNodeIndirect<K, V, PREFIX_LEN, SIZE>
{
    type Iter<'a>
        = NodeIndirectIter<'a, K, V, PREFIX_LEN>
    where
        Self: 'a;

    fn header(&self) -> &Header<PREFIX_LEN> {
        &self.header
    }

    fn from_header(header: Header<PREFIX_LEN>) -> Self {
        InnerNodeIndirect {
            header,
            child_indices: [None; 256],
            child_pointers: [MaybeUninit::uninit(); SIZE],
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        let index = &self.child_indices[usize::from(key_fragment)];
        let child_pointers = self.initialized_child_pointers();
        if let Some(index) = index {
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
        let child_index = if let Some(index) = self.child_indices[key_fragment_idx] {
            // overwrite existing
            usize::from(index)
        } else {
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
                Some(unsafe { NonMaxIndex::try_from(child_index).unwrap_unchecked() });
            self.header.inc_num_children();
            child_index
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
        let restricted_index = self.child_indices[usize::from(key_fragment)]?;

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
        for other_restrict_index in self.child_indices.iter_mut().flatten() {
            if restricted_index < *other_restrict_index {
                // PANIC SAFETY: This will not underflow, because it is guaranteed to be
                // greater than at least 1 other index. This will not panic in the
                // `try_from` because the new value is derived from an existing restricted
                // index.
                *other_restrict_index =
                    NonMaxIndex::try_from(other_restrict_index.get() - 1).unwrap();
            }
        }

        self.child_indices[usize::from(key_fragment)] = None;
        self.header.dec_num_children();
        // SAFETY: This child pointer value is initialized because we got it by using a
        // non-`RestrictedNodeIndex::<>::EMPTY` index from the child indices array.
        Some(unsafe { MaybeUninit::assume_init(child_ptr) })
    }

    fn iter(&self) -> NodeIndirectIter<'_, K, V, PREFIX_LEN> {
        let child_pointers = self.initialized_child_pointers();

        NodeIndirectIter {
            it: self.child_indices.iter().enumerate(),
            child_pointers,
        }
    }

    fn range(
        &self,
        bound: impl core::ops::RangeBounds<u8>,
    ) -> impl DoubleEndedIterator<Item = (u8, OpaqueNodePtr<K, V, PREFIX_LEN>)> + FusedIterator
    {
        assert_valid_range_bounds(&bound);

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
                idx.map(|idx| (key as u8, usize::from(idx)))
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
        // SAFETY: Since `NonMaxIndex` is repr(transparent) is safe to transmute it to a
        // u8. Since we're also working with `Option<NonMaxIndex>`, which is underneath
        // actually `Option<NonZeroU8>`, we know that the value representing `None` will
        // be `0`. That way we can check for non-zero values to see where `Some(...)`
        // indices are.
        let child_indices: &[u8; 256] = unsafe { mem::transmute(&self.child_indices) };
        let empty = u8x64::splat(0);
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

        // SAFETY: We know the value at `key` index is not `None` because this node must
        // contain at least one child (similar to the logic above).
        let idx = usize::from(unsafe { self.child_indices[key].unwrap_unchecked() });
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
            let Some(idx) = idx else {
                continue;
            };
            let child_pointers = self.initialized_child_pointers();
            return (key as u8, child_pointers[usize::from(*idx)]);
        }
        unreachable!("inner node must have non-zero number of children");
    }

    #[cfg(feature = "nightly")]
    #[cfg_attr(test, mutants::skip)]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        // SAFETY: Since `NonMaxIndex` is repr(transparent) is safe to transmute it to a
        // u8. Since we're also working with `Option<NonMaxIndex>`, which is underneath
        // actually `Option<NonZeroU8>`, we know that the value representing `None` will
        // be `0`. That way we can check for non-zero values to see where `Some(...)`
        // indices are.
        let child_indices: &[u8; 256] = unsafe { mem::transmute(&self.child_indices) };
        let empty = u8x64::splat(0);
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

        // SAFETY: We know the value at `key` index is not `None` because this node must
        // contain at least one child (similar to the logic above).
        let idx = usize::from(unsafe { self.child_indices[key].unwrap_unchecked() });
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
            let Some(idx) = idx else {
                continue;
            };
            let child_pointers = self.initialized_child_pointers();
            return (key as u8, child_pointers[usize::from(*idx)]);
        }
        unreachable!("inner node must have non-zero number of children");
    }
}

/// Node that references between 17 and 49 children.
pub type InnerNode48<K, V, const PREFIX_LEN: usize> = InnerNodeIndirect<K, V, PREFIX_LEN, 48>;

impl<K, V, const PREFIX_LEN: usize> Node<PREFIX_LEN> for InnerNode48<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node48;
}

impl<K, V, const PREFIX_LEN: usize> InnerNode<PREFIX_LEN> for InnerNode48<K, V, PREFIX_LEN> {
    type GrownNode = InnerNodeDirect<K, V, PREFIX_LEN>;
    type ShrunkNode = InnerNode16<K, V, PREFIX_LEN>;

    fn grow(&self) -> Self::GrownNode {
        self.into()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        self.into()
    }
}

/// This struct is an iterator over the children of a [`InnerNodeIndirect`].
pub struct NodeIndirectIter<'a, K, V, const PREFIX_LEN: usize> {
    pub(crate) it: Enumerate<Iter<'a, Option<NonMaxIndex>>>,
    pub(crate) child_pointers: &'a [OpaqueNodePtr<K, V, PREFIX_LEN>],
}

impl<K, V, const PREFIX_LEN: usize> Iterator for NodeIndirectIter<'_, K, V, PREFIX_LEN> {
    type Item = (u8, OpaqueNodePtr<K, V, PREFIX_LEN>);

    fn next(&mut self) -> Option<Self::Item> {
        for (key, idx) in self.it.by_ref() {
            let Some(idx) = idx else {
                continue;
            };
            let key = key as u8;
            // SAFETY: This idx is in bounds, since the number
            // of iterations is always <= 48 (i.e 0-47)
            let child_pointer = unsafe { *self.child_pointers.get_unchecked(usize::from(*idx)) };
            return Some((key, child_pointer));
        }
        None
    }
}

impl<K, V, const PREFIX_LEN: usize> DoubleEndedIterator for NodeIndirectIter<'_, K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some((key, idx)) = self.it.next_back() {
            let Some(idx) = idx else {
                continue;
            };
            let key = key as u8;
            // SAFETY: This idx is in bounds, since the number
            // of iterations is always <= 48 (i.e 0-47)
            let child_pointer = unsafe { *self.child_pointers.get_unchecked(usize::from(*idx)) };
            return Some((key, child_pointer));
        }
        None
    }
}

impl<K, V, const PREFIX_LEN: usize> FusedIterator for NodeIndirectIter<'_, K, V, PREFIX_LEN> {}

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

        n.child_indices[1] = Some(2usize.try_into().unwrap());
        n.child_indices[3] = Some(0usize.try_into().unwrap());
        n.child_indices[123] = Some(1usize.try_into().unwrap());

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
    #[should_panic = "Cannot shrink a InnerNodeIndirect when it has more than 16 children. \
                      Currently has [17] children."]
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
