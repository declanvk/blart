use crate::{
    alloc::Allocator,
    collections::map::TreeMap,
    map::find_leaf_pointer_for_bound,
    raw::{search_for_delete_point, LeafNode, NodePtr, RawIterator},
    AsBytes,
};
use std::{iter::FusedIterator, ops::Bound};

/// An iterator which uses a closure to determine if an element should be
/// removed.
///
/// This struct is created by the [`extract_if`][TreeMap::extract_if] method
/// on [`TreeMap`]. See its documentation for more.
#[derive(Debug)]
pub struct ExtractIf<'a, K, V, F, const PREFIX_LEN: usize, A: Allocator> {
    tree: &'a mut TreeMap<K, V, PREFIX_LEN, A>,
    pred: F,
    inner: RawIterator<K, V, PREFIX_LEN>,
}

impl<'a, K, V, F, const PREFIX_LEN: usize, A> ExtractIf<'a, K, V, F, PREFIX_LEN, A>
where
    K: AsBytes,
    F: FnMut(&K, &mut V) -> bool,
    A: Allocator,
{
    /// Create a new range iterator over the given tree, starting and ending
    /// according to the given bounds.
    ///
    /// # Panics
    ///
    /// This function will panic if `start_bound` is greater than `end_bound`.
    pub(crate) fn new(
        tree: &'a mut TreeMap<K, V, PREFIX_LEN, A>,
        start_bound: Bound<&[u8]>,
        end_bound: Bound<&[u8]>,
        pred: F,
    ) -> Self {
        let Some(tree_state) = &tree.state else {
            return Self {
                tree,
                pred,
                inner: RawIterator::empty(),
            };
        };

        {
            match (start_bound, end_bound) {
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

        // SAFETY: Since we have a (shared or mutable) reference to the original
        // TreeMap, we know there will be no concurrent mutation
        let possible_start = unsafe { find_leaf_pointer_for_bound(tree_state, start_bound, true) };
        let Some(start) = possible_start else {
            return Self {
                tree,
                pred,
                inner: RawIterator::empty(),
            };
        };

        // SAFETY: Since we have a (shared or mutable) reference to the original
        // TreeMap, we know there will be no concurrent mutation
        let possible_end = unsafe { find_leaf_pointer_for_bound(tree_state, end_bound, false) };
        let Some(end) = possible_end else {
            return Self {
                tree,
                pred,
                inner: RawIterator::empty(),
            };
        };

        // SAFETY: Since we have a (shared or mutable) reference to the original
        // TreeMap, we know there will be no concurrent mutation. Also, the
        // reference lifetimes created are bounded to this `unsafe` block, and
        // don't overlap with any mutation.
        unsafe {
            let start_leaf_bytes = start.as_key_ref().as_bytes();
            let end_leaf_bytes = end.as_key_ref().as_bytes();

            if start_leaf_bytes > end_leaf_bytes {
                // Resolved start leaf is not less than or equal to resolved end leaf for
                // iteration order
                return Self {
                    tree,
                    pred,
                    inner: RawIterator::empty(),
                };
            }
        }

        Self {
            tree,
            pred,
            // SAFETY: `start` is guaranteed to be less than or equal to `end` in the iteration
            // order because of the check we do on the bytes of the resolved leaf pointers, just
            // above this line
            inner: unsafe { RawIterator::new(start, end) },
        }
    }

    /// Test the given leaf node against the predicate and if it returns `true`
    /// remove it from the tree.
    fn test_and_remove_leaf(
        &mut self,
        leaf_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    ) -> Option<LeafNode<K, V, PREFIX_LEN>> {
        // SAFETY: The leaf node lifetime is scoped to this block and we don't have any
        // other reference to this leaf. Also, we hold a mutable reference to the
        // overall tree, so no concurrent modification or access to the tree is
        // possible.
        let leaf_node = unsafe { leaf_ptr.as_mut() };

        let should_remove = {
            let (k, v) = leaf_node.entry_mut();
            (self.pred)(k, v)
        };

        if !should_remove {
            return None;
        }

        let Some(state) = &self.tree.state else {
            return None;
        };

        // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
        // that there are no other references (mutable or immutable) to this same
        // object. Meaning that our access to the root node is unique and there are no
        // other accesses to any node in the tree.
        let delete_point = unsafe {
            search_for_delete_point(state.root, leaf_node.key_ref().as_bytes())
                .expect("the delete point must be present in the tree if we're iterating over it")
        };
        // SAFETY: There are no outstanding pointers (besides leaf min/max which are
        // already fixed by `apply_delete_pointer`).
        let delete_result = unsafe { self.tree.apply_delete_point(delete_point) };

        // The `RawIterator` state is already correct because we "pop" from that
        // iterator already. The leaf linked list is updated by the `apply_delete_point`
        // function.

        Some(delete_result.deleted_leaf)
    }
}

impl<'a, K, V, F, const PREFIX_LEN: usize, A> Iterator for ExtractIf<'a, K, V, F, PREFIX_LEN, A>
where
    K: AsBytes,
    F: FnMut(&K, &mut V) -> bool,
    A: Allocator,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // SAFETY: This iterator has a reference (either shared or mutable) to the
            // original `TreeMap` it is iterating over, preventing any other modification.
            let leaf_ptr = unsafe { self.inner.next()? };

            match self.test_and_remove_leaf(leaf_ptr) {
                Some(leaf) => return Some(leaf.into_entry()),
                None => {
                    continue;
                },
            }
        }
    }
}

impl<'a, K, V, F, const PREFIX_LEN: usize, A> DoubleEndedIterator
    for ExtractIf<'a, K, V, F, PREFIX_LEN, A>
where
    K: AsBytes,
    F: FnMut(&K, &mut V) -> bool,
    A: Allocator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            // SAFETY: This iterator has a reference (either shared or mutable) to the
            // original `TreeMap` it is iterating over, preventing any other modification.
            let leaf_ptr = unsafe { self.inner.next_back()? };

            match self.test_and_remove_leaf(leaf_ptr) {
                Some(leaf) => return Some(leaf.into_entry()),
                None => {
                    continue;
                },
            }
        }
    }
}

impl<K, V, F, const PREFIX_LEN: usize, A> FusedIterator for ExtractIf<'_, K, V, F, PREFIX_LEN, A>
where
    K: AsBytes,
    F: FnMut(&K, &mut V) -> bool,
    A: Allocator,
{
}

#[cfg(test)]
mod tests {
    use crate::{
        tests_common::{generate_key_fixed_length, swap},
        TreeMap,
    };

    #[test]
    fn extract_if_simple() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(.., |_k, v| *v % 2 == 0).collect();

        assert_eq!(drained.len(), 5);
        assert_eq!(map.len(), 5);
        assert_eq!(drained, vec![(0, 0), (2, 2), (4, 4), (6, 6), (8, 8)]);
        assert_eq!(
            map.into_iter().collect::<Vec<_>>(),
            vec![(1, 1), (3, 3), (5, 5), (7, 7), (9, 9)]
        );
    }

    #[test]
    fn extract_if_all() {
        let first_width = if cfg!(miri) { 15 } else { u8::MAX };
        let mut map: TreeMap<_, usize> = generate_key_fixed_length([first_width, 1])
            .enumerate()
            .map(swap)
            .collect();

        let drained: Vec<_> = map.extract_if(.., |_, _| true).collect();
        let expected_len = if cfg!(miri) { 32 } else { 512 };
        assert_eq!(drained.len(), expected_len);
        assert!(map.is_empty());
    }

    #[test]
    fn extract_if_none() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(.., |_, _| false).collect();

        assert!(drained.is_empty());
        assert_eq!(map.len(), 10);
    }

    #[test]
    fn extract_if_mutate() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map
            .extract_if(.., |_k, v| {
                if *v % 2 == 0 {
                    true
                } else {
                    *v *= 2;
                    false
                }
            })
            .collect();

        assert_eq!(drained.len(), 5);
        assert_eq!(map.len(), 5);
        assert_eq!(
            map.into_iter().collect::<Vec<_>>(),
            vec![(1, 2), (3, 6), (5, 10), (7, 14), (9, 18)]
        );
    }

    #[test]
    fn tree_map_extract_if_interrupted() {
        // Exactly the same as `retain`, on panic the iteration should stop.

        let map: TreeMap<[u8; 2], _> = generate_key_fixed_length([15, 3])
            .enumerate()
            .map(swap)
            .collect();

        assert_eq!(map.len(), 64);
        let map = std::sync::Mutex::new(map);
        let res = std::panic::catch_unwind(|| {
            let mut map = map.lock().unwrap();
            let _: Vec<_> = map
                .extract_if(.., |_, v| if *v == 32 { panic!("stop") } else { true })
                .collect();
        });
        assert!(res.is_err());
        assert!(map.is_poisoned());
        // We know in this case that the map should be fine after the panic
        map.clear_poison();
        let map = map.into_inner().unwrap();
        assert!(map.into_values().eq(32..64));
    }

    #[test]
    fn singleton_compress_previous_child_in_node() {
        // The `SingletonCompress` fixup cases has two(?) variants:
        //   1. The single remaining child in the node was already visited by the
        //      `ExtractIf` iterator, in which case we don't need to update it.
        //   2. The single remaining child in the node has not yet been visited, in
        //      which case we need to update it.

        let mut tree: TreeMap<_, _> = [
            // root node
            [1, 0],
            [2, 0],
            [3, 0],
            [4, 0],
            // parent node which will be singleton compressed
            [1, 1],
            [1, 2],
            [1, 3],
        ]
        .into_iter()
        .enumerate()
        .map(swap)
        .collect();

        // Case 1: The first child in the parent node will be kept and singleton
        // compressed
        tree.clone()
            .extract_if(.., |k, _| if k[0] == 1 { k[1] != 0 } else { false })
            .for_each(drop);

        // Case 2: The last child in the parent node will be kept and singleton
        // compressed
        tree.extract_if(.., |k, _| if k[0] == 1 { k[1] != 3 } else { false })
            .for_each(drop);
    }

    #[test]
    fn double_ended_partial() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let mut iter = map.extract_if(.., |k, _v| *k % 2 == 0);

        assert_eq!(iter.next(), Some((0, 0)));
        assert_eq!(iter.next_back(), Some((8, 8)));
        assert_eq!(iter.next(), Some((2, 2)));
        assert_eq!(iter.next_back(), Some((6, 6)));
        assert_eq!(iter.next(), Some((4, 4)));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        assert_eq!(map.len(), 5);
        assert_eq!(
            map.into_iter().collect::<Vec<_>>(),
            vec![(1, 1), (3, 3), (5, 5), (7, 7), (9, 9)]
        );
    }

    #[test]
    fn double_ended_all() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let mut iter = map.extract_if(.., |_, _| true);

        assert_eq!(iter.next(), Some((0, 0)));
        assert_eq!(iter.next_back(), Some((9, 9)));
        assert_eq!(iter.next(), Some((1, 1)));
        assert_eq!(iter.next_back(), Some((8, 8)));

        assert_eq!(map.len(), 6);
        assert_eq!(
            map.into_iter().collect::<Vec<_>>(),
            vec![(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7)]
        );
    }

    #[test]
    fn double_ended_none() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let mut iter = map.extract_if(.., |_, _| false);

        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        assert_eq!(map.len(), 10);
    }

    #[test]
    fn range_inclusive() {
        let mut map: TreeMap<i32, i32> = (0..20).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(2..=18, |k, _v| *k % 2 == 0).collect();

        assert_eq!(drained.len(), 9);
        assert_eq!(map.len(), 11);
        assert_eq!(
            drained,
            vec![
                (2, 2),
                (4, 4),
                (6, 6),
                (8, 8),
                (10, 10),
                (12, 12),
                (14, 14),
                (16, 16),
                (18, 18)
            ]
        );

        let mut expected = (0..20).collect::<Vec<_>>();
        expected.retain(|&i| !(2..=18).contains(&i) || i % 2 != 0);
        let remaining: Vec<_> = map.into_iter().map(|(k, _)| k).collect();
        assert_eq!(remaining, expected);
    }

    #[test]
    fn range_inclusive_rev() {
        let mut map: TreeMap<i32, i32> = (0..20).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(2..=18, |k, _v| *k % 2 == 0).rev().collect();

        assert_eq!(drained.len(), 9);
        assert_eq!(map.len(), 11);
        assert_eq!(
            drained,
            vec![
                (18, 18),
                (16, 16),
                (14, 14),
                (12, 12),
                (10, 10),
                (8, 8),
                (6, 6),
                (4, 4),
                (2, 2)
            ]
        );

        let mut expected = (0..20).collect::<Vec<_>>();
        expected.retain(|&i| !(2..=18).contains(&i) || i % 2 != 0);
        let remaining: Vec<_> = map.into_iter().map(|(k, _)| k).collect();
        assert_eq!(remaining, expected);
    }

    #[test]
    fn range() {
        let mut map: TreeMap<i32, i32> = (0..20).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(2..18, |k, _v| *k % 2 == 0).collect();

        assert_eq!(drained.len(), 8);
        assert_eq!(map.len(), 12);
        assert_eq!(
            drained,
            vec![
                (2, 2),
                (4, 4),
                (6, 6),
                (8, 8),
                (10, 10),
                (12, 12),
                (14, 14),
                (16, 16)
            ]
        );

        let mut expected = (0..20).collect::<Vec<_>>();
        expected.retain(|&i| !(2..18).contains(&i) || i % 2 != 0);
        let remaining: Vec<_> = map.into_iter().map(|(k, _)| k).collect();
        assert_eq!(remaining, expected);
    }

    #[test]
    fn range_from() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(5.., |k, _v| *k % 2 != 0).collect();

        assert_eq!(drained.len(), 3);
        assert_eq!(map.len(), 7);
        assert_eq!(drained, vec![(5, 5), (7, 7), (9, 9)]);

        let mut expected = (0..10).collect::<Vec<_>>();
        expected.retain(|&i| i < 5 || i % 2 == 0);
        let remaining: Vec<_> = map.into_iter().map(|(k, _)| k).collect();
        assert_eq!(remaining, expected);
    }

    #[test]
    fn range_to() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(..5, |k, _v| *k % 2 != 0).collect();

        assert_eq!(drained.len(), 2);
        assert_eq!(map.len(), 8);
        assert_eq!(drained, vec![(1, 1), (3, 3)]);

        let mut expected = (0..10).collect::<Vec<_>>();
        expected.retain(|&i| i >= 5 || i % 2 == 0);
        let remaining: Vec<_> = map.into_iter().map(|(k, _)| k).collect();
        assert_eq!(remaining, expected);
    }

    #[test]
    fn range_to_inclusive() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(..=5, |k, _v| *k % 2 != 0).collect();

        assert_eq!(drained.len(), 3);
        assert_eq!(map.len(), 7);
        assert_eq!(drained, vec![(1, 1), (3, 3), (5, 5)]);

        let mut expected = (0..10).collect::<Vec<_>>();
        expected.retain(|&i| i > 5 || i % 2 == 0);
        let remaining: Vec<_> = map.into_iter().map(|(k, _)| k).collect();
        assert_eq!(remaining, expected);
    }

    #[test]
    fn range_double_ended() {
        let mut map: TreeMap<i32, i32> = (0..20).map(|i| (i, i)).collect();
        let mut iter = map.extract_if(2..18, |k, _v| *k % 2 == 0);

        assert_eq!(iter.next(), Some((2, 2)));
        assert_eq!(iter.next_back(), Some((16, 16)));
        assert_eq!(iter.next(), Some((4, 4)));
        assert_eq!(iter.next_back(), Some((14, 14)));

        assert_eq!(map.len(), 16);

        let mut expected = (0..20).collect::<Vec<_>>();
        expected.retain(|&i| !(2..18).contains(&i) || (i > 4 && i < 14) || i % 2 != 0);
        let remaining: Vec<_> = map.into_iter().map(|(k, _)| k).collect();
        assert_eq!(remaining, expected);
    }

    #[test]
    fn empty_range() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(5..5, |_, _| true).collect();
        assert!(drained.is_empty());
        assert_eq!(map.len(), 10);
    }

    #[test]
    #[should_panic]
    #[allow(clippy::reversed_empty_ranges)]
    fn inverted_range() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let _ = map.extract_if(5..2, |_, _| true);
    }
}
