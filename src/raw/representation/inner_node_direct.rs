use core::{fmt, iter::FusedIterator, ops::RangeBounds};

use crate::raw::{
    ChildEdge, Header, InnerNode, InnerNode48, InnerNodeCommon, InnerNodeIndirect, InnerNodeSorted,
    Node, NodeType, OpaqueNodePtr, Sibling,
    representation::{Bitmap, assert_valid_range_bounds},
};

/// Inner node that stores up to 256 children, where lookup is performed by
/// indexing with key byte.
#[repr(C, align(8))]
pub struct InnerNodeDirect<K, V, const PREFIX_LEN: usize> {
    /// The common node fields.
    header: Header<PREFIX_LEN>,
    /// The set of key bytes which have a child in `child_pointers`.
    ///
    /// This lets iteration, min/max, and sibling search skip directly to the
    /// populated slots instead of scanning all 256 child pointers.
    ///
    /// Invariant: for every key byte `k`, `present.contains(k)` is true if and only if
    /// `child_pointers[k]` is `Some`.
    present: Bitmap,
    /// An array that directly maps a key byte (as index) to a child node.
    child_pointers: [Option<OpaqueNodePtr<K, V, PREFIX_LEN>>; 256],
}

impl<K, V, const PREFIX_LEN: usize> InnerNodeDirect<K, V, PREFIX_LEN> {
    /// Create a new node with the given header and children.
    ///
    /// The number of children in the header is overwritten with the number of
    /// children yielded by `children`.
    fn from_header_and_children(
        mut header: Header<PREFIX_LEN>,
        children: impl Iterator<Item = ChildEdge<K, V, PREFIX_LEN>>,
    ) -> Self {
        header.reset_num_children();
        let mut node = InnerNodeDirect {
            header,
            present: Bitmap::new(),
            child_pointers: [None; 256],
        };
        for (key_fragment, child_pointer) in children {
            node.write_child(key_fragment, child_pointer);
        }
        node
    }

    /// Return the child edge for a key byte which is a member of
    /// `self.present`.
    ///
    /// # Safety
    ///
    /// The caller must only pass key bytes obtained from `self.present`. This
    /// is checked in debug builds.
    #[inline]
    unsafe fn present_child(&self, key_fragment: u8) -> ChildEdge<K, V, PREFIX_LEN> {
        debug_assert!(
            self.present.contains(key_fragment),
            "key fragment [{key_fragment}] is not present in node"
        );
        let child_pointer = self.child_pointers[usize::from(key_fragment)];
        // SAFETY: Every key fragment passed to this function is a member of
        // `self.present` (by caller requirement). Its an invariant of the `present` field bitmap
        // that `child_pointers[k]` is `Some` for every member `k` of `self.present`.
        (key_fragment, unsafe { child_pointer.unwrap_unchecked() })
    }
}

impl<K, V, const PREFIX_LEN: usize, const OTHER_SIZE: usize>
    From<&InnerNodeSorted<K, V, PREFIX_LEN, OTHER_SIZE>> for InnerNodeDirect<K, V, PREFIX_LEN>
{
    fn from(value: &InnerNodeSorted<K, V, PREFIX_LEN, OTHER_SIZE>) -> Self {
        Self::from_header_and_children(value.header().clone(), value.inner_iter())
    }
}

impl<K, V, const PREFIX_LEN: usize, const OTHER_SIZE: usize>
    From<&InnerNodeIndirect<K, V, PREFIX_LEN, OTHER_SIZE>> for InnerNodeDirect<K, V, PREFIX_LEN>
{
    fn from(value: &InnerNodeIndirect<K, V, PREFIX_LEN, OTHER_SIZE>) -> Self {
        Self::from_header_and_children(value.header().clone(), value.iter())
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for InnerNodeDirect<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNodeDirect")
            .field("header", &self.header)
            .field("present", &self.present)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<K, V, const PREFIX_LEN: usize> Clone for InnerNodeDirect<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            present: self.present,
            child_pointers: self.child_pointers,
        }
    }
}

// SAFETY: `InnerNodeDirect` is `repr(C)` and has a `Header` as the first field
unsafe impl<K, V, const PREFIX_LEN: usize> InnerNodeCommon<K, V, PREFIX_LEN>
    for InnerNodeDirect<K, V, PREFIX_LEN>
{
    unsafe fn from_header(header: Header<PREFIX_LEN>) -> Self {
        Self::from_header_and_children(header, core::iter::empty())
    }

    fn header(&self) -> &Header<PREFIX_LEN> {
        &self.header
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        self.child_pointers[usize::from(key_fragment)]
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>) {
        self.child_pointers[usize::from(key_fragment)] = Some(child_pointer);
        if self.present.insert(key_fragment) {
            self.header.inc_num_children();
        }
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        let removed_child = self.child_pointers[usize::from(key_fragment)].take();

        if self.present.remove(key_fragment) {
            self.header.dec_num_children();
        }

        removed_child
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = ChildEdge<K, V, PREFIX_LEN>> + FusedIterator {
        self.present.iter().map(|key| unsafe {
            // SAFETY: `key` comes from `present`
            self.present_child(key)
        })
    }

    fn range(
        &self,
        bound: impl RangeBounds<u8>,
    ) -> impl DoubleEndedIterator<Item = ChildEdge<K, V, PREFIX_LEN>> + FusedIterator {
        assert_valid_range_bounds(&bound);

        self.present.range(bound).into_iter().map(|key| unsafe {
            // SAFETY: `key` comes from `present`
            self.present_child(key)
        })
    }

    fn min(&self) -> ChildEdge<K, V, PREFIX_LEN> {
        let Some(key) = self.present.first() else {
            unreachable!("inner node must have non-zero number of children");
        };
        // SAFETY: `key` comes from `present`
        unsafe { self.present_child(key) }
    }

    fn max(&self) -> ChildEdge<K, V, PREFIX_LEN> {
        let Some(key) = self.present.last() else {
            unreachable!("inner node must have non-zero number of children");
        };
        // SAFETY: `key` comes from `present`
        unsafe { self.present_child(key) }
    }

    fn nearest_sibling(&self, new_leaf_key_byte: u8) -> Sibling<K, V, PREFIX_LEN> {
        let next = self.present.next_after(new_leaf_key_byte);
        if let Some(next) = next
            && next - new_leaf_key_byte == 1
        {
            // Fast path, common in dense nodes: no sibling can be closer than the
            // adjacent one, and ties prefer the next sibling.
            //
            // SAFETY: `key` comes from `present`
            return Sibling::Next(unsafe { self.present_child(next).1 });
        }
        let previous = self.present.prev_before(new_leaf_key_byte);

        // Prefer the closest sibling, and the next sibling when both are
        // equally distant.
        let use_next = match (previous, next) {
            (Some(previous), Some(next)) => {
                (next - new_leaf_key_byte) <= (new_leaf_key_byte - previous)
            },
            (None, Some(_)) => true,
            (Some(_), None) => false,
            (None, None) => {
                panic!("Inner node has no child other than key byte [{new_leaf_key_byte}]")
            },
        };

        if use_next {
            // PANIC SAFETY: `use_next` is only true when `next` is `Some`
            // SAFETY: `key` comes from `present`
            Sibling::Next(unsafe { self.present_child(next.unwrap()).1 })
        } else {
            // PANIC SAFETY: `use_next` is only false when `previous` is `Some`
            // SAFETY: `key` comes from `present`
            Sibling::Previous(unsafe { self.present_child(previous.unwrap()).1 })
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> Node<PREFIX_LEN> for InnerNodeDirect<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node256;
}

impl<K, V, const PREFIX_LEN: usize> InnerNode<PREFIX_LEN> for InnerNodeDirect<K, V, PREFIX_LEN> {
    type GrownNode = Self;
    type ShrunkNode = InnerNode48<K, V, PREFIX_LEN>;

    fn grow(&self) -> Self::GrownNode {
        panic!("unable to grow a Node256, something went wrong!")
    }

    fn shrink(&self) -> Self::ShrunkNode {
        self.into()
    }
}

#[cfg(test)]
mod tests {
    use alloc::{boxed::Box, vec::Vec};
    use core::ops::{Bound, RangeBounds};

    use super::*;
    use crate::raw::{
        LeafNode, NodePtr,
        representation::tests::{
            FixtureReturn, SiblingKey, inner_node_min_max_test, inner_node_nearest_sibling_test,
            inner_node_remove_child_test, inner_node_shrink_test, inner_node_write_child_test,
            nearest_sibling_keys,
        },
    };

    #[test]
    fn lookup() {
        let mut l1 = LeafNode::with_no_siblings(Box::from([]), ());
        let mut l2 = LeafNode::with_no_siblings(Box::from([]), ());
        let mut l3 = LeafNode::with_no_siblings(Box::from([]), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        let mut n = InnerNodeDirect::<Box<[u8]>, (), 16>::from_two_children(
            &[],
            0,
            (1, l1_ptr),
            (123, l2_ptr),
        );
        n.write_child(3, l3_ptr);

        assert_eq!(n.lookup_child(123), Some(l2_ptr));
    }

    #[test]
    fn write_child() {
        inner_node_write_child_test::<16, InnerNodeDirect<Box<[u8]>, (), 16>>(256)
    }

    #[test]
    fn remove_child() {
        inner_node_remove_child_test::<16, InnerNodeDirect<Box<[u8]>, (), 16>>(256)
    }

    #[test]
    #[should_panic = "unable to grow a Node256, something went wrong!"]
    fn grow() {
        let mut leaf = LeafNode::<Box<[u8]>, (), 16>::with_no_siblings(vec![].into(), ());
        let leaf_ptr = NodePtr::from(&mut leaf).to_opaque();
        let n = InnerNodeDirect::<Box<[u8]>, (), 16>::from_two_children(
            &[],
            0,
            (0, leaf_ptr),
            (1, leaf_ptr),
        );

        n.grow();
    }

    #[test]
    fn shrink() {
        inner_node_shrink_test::<16, InnerNodeDirect<Box<[u8]>, (), 16>>(48);
    }

    #[test]
    #[should_panic = "Cannot shrink a InnerNodeDirect when it has more than 48 children. Currently \
                      has [49] children."]
    fn shrink_too_many_children_panic() {
        inner_node_shrink_test::<16, InnerNodeDirect<Box<[u8]>, (), 16>>(49);
    }

    #[test]
    fn min_max() {
        inner_node_min_max_test::<16, InnerNodeDirect<Box<[u8]>, (), 16>>(256);
    }

    #[test]
    fn nearest_sibling() {
        type Node = InnerNodeDirect<Box<[u8]>, (), 16>;

        inner_node_nearest_sibling_test::<16, Node>(&[10, 200]);
        inner_node_nearest_sibling_test::<16, Node>(&[3, 255, 0, 85]);
        inner_node_nearest_sibling_test::<16, Node>(&(0..=u8::MAX).step_by(2).collect::<Vec<_>>());
        inner_node_nearest_sibling_test::<16, Node>(&(0..=u8::MAX).collect::<Vec<_>>());
    }

    #[test]
    fn nearest_sibling_prefers_closest() {
        use SiblingKey::{Next, Previous};

        let queries = [0, 9, 10, 11, 104, 105, 106, 199, 200, 201, 255];
        let results =
            nearest_sibling_keys::<16, InnerNodeDirect<Box<[u8]>, (), 16>>(&[10, 200], queries);

        // When the next and previous children are equally distant, the next
        // child is preferred.
        assert_eq!(
            results,
            [
                Next(10),
                Next(10),
                Next(200),
                Previous(10),
                Previous(10),
                Next(200),
                Next(200),
                Next(200),
                Previous(10),
                Previous(200),
                Previous(200),
            ]
        );
    }

    fn fixture() -> FixtureReturn<InnerNodeDirect<Box<[u8]>, (), 16>, 4> {
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l4 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        let mut n256 = InnerNodeDirect::from_two_children(&[], 0, (3, l1_ptr), (255, l2_ptr));
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
            node: &InnerNodeDirect<K, V, PREFIX_LEN>,
            bound: impl RangeBounds<u8>,
            expected_pairs: [ChildEdge<K, V, PREFIX_LEN>; N],
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

    fn fixture_empty_edges() -> FixtureReturn<InnerNodeDirect<Box<[u8]>, (), 16>, 4> {
        let mut l1 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l2 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l3 = LeafNode::with_no_siblings(vec![].into(), ());
        let mut l4 = LeafNode::with_no_siblings(vec![].into(), ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        let mut n4 = InnerNodeDirect::from_two_children(&[], 0, (3, l1_ptr), (254, l2_ptr));
        n4.write_child(2u8, l3_ptr);
        n4.write_child(85, l4_ptr);

        (n4, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
    }

    #[test]
    fn range_iterate_boundary_conditions() {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = fixture_empty_edges();

        #[track_caller]
        fn check<K, V, const PREFIX_LEN: usize, const N: usize>(
            node: &InnerNodeDirect<K, V, PREFIX_LEN>,
            bound: impl RangeBounds<u8>,
            expected_pairs: [ChildEdge<K, V, PREFIX_LEN>; N],
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
