use crate::{
    raw::{Header, InnerNode, InnerNode48, Node, NodeType, OpaqueNodePtr, RestrictedNodeIndex},
    rust_nightly_apis::maybe_uninit_uninit_array,
};
use std::{
    fmt,
    iter::{Enumerate, FusedIterator},
    ops::Bound,
    slice::Iter,
};

#[cfg(feature = "nightly")]
use std::{
    iter::FilterMap,
    simd::{cmp::SimdPartialEq, usizex64},
};

/// Node that references between 49 and 256 children
#[repr(C, align(8))]
pub struct InnerNode256<K, V, const PREFIX_LEN: usize> {
    /// The common node fields.
    pub header: Header<PREFIX_LEN>,
    /// An array that directly maps a key byte (as index) to a child node.
    pub child_pointers: [Option<OpaqueNodePtr<K, V, PREFIX_LEN>>; 256],
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for InnerNode256<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode256")
            .field("header", &self.header)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<K, V, const PREFIX_LEN: usize> Clone for InnerNode256<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_pointers: self.child_pointers,
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> Node<PREFIX_LEN> for InnerNode256<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node256;
}

impl<K, V, const PREFIX_LEN: usize> InnerNode<PREFIX_LEN> for InnerNode256<K, V, PREFIX_LEN> {
    type GrownNode = Self;
    #[cfg(not(feature = "nightly"))]
    type Iter<'a>
        = Node256Iter<'a, K, V, PREFIX_LEN>
    where
        Self: 'a;
    #[cfg(feature = "nightly")]
    type Iter<'a>
        = FilterMap<
        Enumerate<Iter<'a, Option<OpaqueNodePtr<K, V, PREFIX_LEN>>>>,
        impl FnMut(
            (usize, &'a Option<OpaqueNodePtr<K, V, PREFIX_LEN>>),
        ) -> Option<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>,
    >
    where
        Self: 'a;
    type ShrunkNode = InnerNode48<K, V, PREFIX_LEN>;

    fn header(&self) -> &Header<PREFIX_LEN> {
        &self.header
    }

    fn from_header(header: Header<PREFIX_LEN>) -> Self {
        InnerNode256 {
            header,
            child_pointers: [None; 256],
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        self.child_pointers[usize::from(key_fragment)]
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>) {
        let key_fragment_idx = usize::from(key_fragment);
        let existing_pointer = self.child_pointers[key_fragment_idx];
        self.child_pointers[key_fragment_idx] = Some(child_pointer);
        if existing_pointer.is_none() {
            self.header.inc_num_children();
        }
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        let removed_child = self.child_pointers[usize::from(key_fragment)].take();

        if removed_child.is_some() {
            self.header.dec_num_children();
        }

        removed_child
    }

    fn grow(&self) -> Self::GrownNode {
        panic!("unable to grow a Node256, something went wrong!")
    }

    fn shrink(&self) -> Self::ShrunkNode {
        assert!(
            self.header.num_children() <= 48,
            "Cannot shrink a Node256 when it has more than 48 children. Currently has [{}] \
             children.",
            self.header.num_children()
        );

        let header = self.header.clone();
        let mut child_indices = [RestrictedNodeIndex::<48>::EMPTY; 256];
        let mut child_pointers = maybe_uninit_uninit_array();

        for (child_index, (key_byte, child_ptr)) in self.iter().enumerate() {
            // PANIC SAFETY: This `try_from` will not panic because the `next_index` value
            // is guaranteed to be 48 or less by the `assert!(num_children < 48)` at the
            // start of the function.
            let key_byte = usize::from(key_byte);
            child_indices[key_byte] = RestrictedNodeIndex::try_from(child_index).unwrap();
            child_pointers[child_index].write(child_ptr);
        }

        InnerNode48 {
            header,
            child_indices,
            child_pointers,
        }
    }

    fn iter(&self) -> Self::Iter<'_> {
        #[cfg(not(feature = "nightly"))]
        {
            Node256Iter {
                it: self.child_pointers.iter().enumerate(),
            }
        }

        #[cfg(feature = "nightly")]
        {
            self.child_pointers
                .iter()
                .enumerate()
                .filter_map(|(key, node)| node.map(|node| (key as u8, node)))
        }
    }

    fn range(
        &self,
        bound: impl std::ops::RangeBounds<u8>,
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

        let start = bound.start_bound().map(|val| usize::from(*val));
        let key_offset = match bound.start_bound() {
            std::ops::Bound::Included(val) => *val,
            std::ops::Bound::Excluded(val) => val.saturating_add(1),
            std::ops::Bound::Unbounded => 0,
        };
        let end = bound.end_bound().map(|val| usize::from(*val));

        self.child_pointers[(start, end)]
            .iter()
            .enumerate()
            .filter_map(move |(key, child)| {
                child.map(|child| ((key as u8).saturating_add(key_offset), child))
            })
    }

    #[cfg(feature = "nightly")]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        use crate::rust_nightly_apis::assume;

        // SAFETY: Due to niche optimization Option<NonNull> has the same
        // size as NonNull and NonNull has the same size as usize
        // so it's safe to transmute
        let child_pointers: &[usize; 256] = unsafe { std::mem::transmute(&self.child_pointers) };
        let empty = usizex64::splat(0);
        let r0 = usizex64::from_array(child_pointers[0..64].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r1 = usizex64::from_array(child_pointers[64..128].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r2 = usizex64::from_array(child_pointers[128..192].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r3 = usizex64::from_array(child_pointers[192..256].try_into().unwrap())
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
            // SAFETY: key can be at up to 256, but we know that we have
            // at least one inner child, it's guarantee to be in bounds
            assume!(key < self.child_pointers.len());
        }

        // SAFETY: Covered by the containing function
        (key as u8, unsafe {
            self.child_pointers[key].unwrap_unchecked()
        })
    }

    #[cfg(not(feature = "nightly"))]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        for (key, child_pointer) in self.child_pointers.iter().enumerate() {
            match child_pointer {
                Some(child_pointer) => return (key as u8, *child_pointer),
                None => continue,
            }
        }
        unreachable!("inner node must have non-zero number of children");
    }

    #[cfg(feature = "nightly")]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        use crate::rust_nightly_apis::assume;

        // SAFETY: Due to niche optimization Option<NonNull> has the same
        // size as NonNull and NonNull has the same size as usize
        // so it's safe to transmute
        let child_pointers: &[usize; 256] = unsafe { std::mem::transmute(&self.child_pointers) };
        let empty = usizex64::splat(0);
        let r0 = usizex64::from_array(child_pointers[0..64].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r1 = usizex64::from_array(child_pointers[64..128].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r2 = usizex64::from_array(child_pointers[128..192].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r3 = usizex64::from_array(child_pointers[192..256].try_into().unwrap())
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
            // SAFETY: idx can be at up to 255, so it's in bounds
            assume!(key < self.child_pointers.len());
        }

        // SAFETY: covered by the containing function
        (key as u8, unsafe {
            self.child_pointers[key].unwrap_unchecked()
        })
    }

    #[cfg(not(feature = "nightly"))]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        for (key, child_pointer) in self.child_pointers.iter().enumerate().rev() {
            match child_pointer {
                Some(child_pointer) => return (key as u8, *child_pointer),
                None => continue,
            }
        }
        unreachable!("inner node must have non-zero number of children");
    }
}

/// This struct is an iterator over the children of a [`InnerNode256`].
#[cfg(not(feature = "nightly"))]
pub struct Node256Iter<'a, K, V, const PREFIX_LEN: usize> {
    pub(crate) it: Enumerate<Iter<'a, Option<OpaqueNodePtr<K, V, PREFIX_LEN>>>>,
}

#[cfg(not(feature = "nightly"))]
impl<K, V, const PREFIX_LEN: usize> Iterator for Node256Iter<'_, K, V, PREFIX_LEN> {
    type Item = (u8, OpaqueNodePtr<K, V, PREFIX_LEN>);

    fn next(&mut self) -> Option<Self::Item> {
        for (key, node) in self.it.by_ref() {
            match node {
                Some(node) => return Some((key as u8, *node)),
                None => continue,
            }
        }
        None
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V, const PREFIX_LEN: usize> DoubleEndedIterator for Node256Iter<'_, K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some((key, node)) = self.it.next_back() {
            match node {
                Some(node) => return Some((key as u8, *node)),
                None => continue,
            }
        }
        None
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V, const PREFIX_LEN: usize> FusedIterator for Node256Iter<'_, K, V, PREFIX_LEN> {}

#[cfg(test)]
mod tests {
    use std::ops::{Bound, RangeBounds};

    use crate::raw::{
        representation::tests::{
            inner_node_remove_child_test, inner_node_shrink_test, inner_node_write_child_test,
            FixtureReturn,
        },
        LeafNode, NodePtr,
    };

    use super::*;

    #[test]
    fn lookup() {
        let mut n = InnerNode256::<Box<[u8]>, (), 16>::empty();
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

        n.child_pointers[1] = Some(l1_ptr);
        n.child_pointers[123] = Some(l2_ptr);
        n.child_pointers[3] = Some(l3_ptr);

        assert_eq!(n.lookup_child(123), Some(l2_ptr));
    }

    #[test]
    fn write_child() {
        inner_node_write_child_test(InnerNode256::<_, _, 16>::empty(), 256)
    }

    #[test]
    fn remove_child() {
        inner_node_remove_child_test(InnerNode256::<_, _, 16>::empty(), 256)
    }

    #[test]
    #[should_panic = "unable to grow a Node256, something went wrong!"]
    fn grow() {
        let n = InnerNode256::<Box<[u8]>, (), 16>::empty();

        n.grow();
    }

    #[test]
    fn shrink() {
        inner_node_shrink_test(InnerNode256::<_, _, 16>::empty(), 48);
    }

    #[test]
    #[should_panic = "Cannot shrink a Node256 when it has more than 48 children. Currently has \
                      [49] children."]
    fn shrink_too_many_children_panic() {
        inner_node_shrink_test(InnerNode256::<_, _, 16>::empty(), 49);
    }

    fn fixture() -> FixtureReturn<InnerNode256<Box<[u8]>, (), 16>, 4> {
        let mut n256 = InnerNode256::empty();
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l4 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        n256.write_child(3, l1_ptr);
        n256.write_child(255, l2_ptr);
        n256.write_child(0u8, l3_ptr);
        n256.write_child(85, l4_ptr);

        (n256, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
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
            node: &InnerNode256<K, V, PREFIX_LEN>,
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

    fn fixture_empty_edges() -> FixtureReturn<InnerNode256<Box<[u8]>, (), 16>, 4> {
        let mut n4 = InnerNode256::empty();
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
            node: &InnerNode256<K, V, PREFIX_LEN>,
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
