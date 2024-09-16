use crate::{maximum_unchecked, minimum_unchecked, AsBytes, RawIterator, TreeMap};
use std::iter::FusedIterator;

use super::{
    find_terminating_node, InnerNodeSearchResult, InnerNodeSearchResultReason,
    TerminatingNodeSearchResult,
};

macro_rules! implement_prefix_iter {
    (
        $(#[$outer:meta])*
        struct $name:ident {
            tree: $tree_ty:ty,
            item: $item_ty:ty,
            $leaf_accessor_func:ident
        }
    ) => {
        $(#[$outer])*
        pub struct $name<'a, K, V, const PREFIX_LEN: usize> {
            inner: RawIterator<K, V, PREFIX_LEN>,
            _tree: $tree_ty,
        }

        impl<'a, K: AsBytes, V, const PREFIX_LEN: usize> $name<'a, K, V, PREFIX_LEN> {
            /// Create a new prefix iterator over the given tree, the iterator returning all
            /// key-value pairs where the key starts with the given prefix.
            pub(crate) fn new(
                tree: $tree_ty,
                prefix: &[u8],
            ) -> Self {
                let Some(tree_state) = &tree.state else {
                    return Self {
                        _tree: tree,
                        inner: RawIterator::empty(),
                    };
                };

                // SAFETY: Since we have a (shared or mutable) reference to the original
                // TreeMap, we know there will be no concurrent mutation
                let search_result = unsafe { find_terminating_node(tree_state.root, prefix) };
                let (start, end) = match search_result {
                    TerminatingNodeSearchResult::Leaf { leaf_ptr, .. } => {
                        // SAFETY: Its safe to create a shared reference to the leaf since we hold
                        // either a shared or mutable reference to the owning TreeMap, which prevents
                        // other concurrent mutable references.
                        let leaf = unsafe { leaf_ptr.as_ref() };

                        // Only include the item in the iterator if the prefix actually matches
                        if leaf.key_ref().as_bytes().starts_with(prefix) {
                            (leaf_ptr, leaf_ptr)
                        } else {
                            return Self {
                                _tree: tree,
                                inner: RawIterator::empty(),
                            };
                        }
                    },
                    TerminatingNodeSearchResult::InnerNode(InnerNodeSearchResult { node_ptr, reason, .. }) => {
                        if matches!(reason, InnerNodeSearchResultReason::MissingChild) {
                            // if the child is missing, then there is nothing to be the prefix of
                            return Self {
                                _tree: tree,
                                inner: RawIterator::empty(),
                            };
                        }

                        // SAFETY: Its safe to create a shared reference to the leaf since we hold
                        // either a shared or mutable reference to the owning TreeMap, which prevents
                        // other concurrent mutable references.
                        unsafe { (minimum_unchecked(node_ptr), maximum_unchecked(node_ptr)) }
                    },
                };

                Self {
                    _tree: tree,
                    // SAFETY: `start` is guaranteed to be less than or equal to `end` in the iteration
                    // order because of the check we do on the bytes of the resolved leaf pointers, just
                    // above this line
                    inner: unsafe { RawIterator::new(start, end) },
                }
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize> Iterator for $name<'a, K, V, PREFIX_LEN> {
            type Item = $item_ty;

            fn next(&mut self) -> Option<Self::Item> {
                // SAFETY: This iterator has a reference (either shared or mutable) to the
                // original `TreeMap` it is iterating over, preventing any other modification.
                let leaf_ptr = unsafe { self.inner.next()? };

                // SAFETY: The lifetimes returned from this function are returned as bounded by
                // lifetime 'a, meaning that they cannot outlive this iterator's reference
                // (shared or mutable) to the original TreeMap.
                Some(unsafe { leaf_ptr.$leaf_accessor_func() })
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize> DoubleEndedIterator
            for $name<'a, K, V, PREFIX_LEN>
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                // SAFETY: This iterator has a reference (either shared or mutable) to the
                // original `TreeMap` it is iterating over, preventing any other modification.
                let leaf_ptr = unsafe { self.inner.next_back()? };

                // SAFETY: THe lifetimes returned from this function are returned as bounded by
                // lifetime 'a, meaning that they cannot outlive this iterator's reference
                // (shared or mutable) to the original TreeMap.
                Some(unsafe { leaf_ptr.$leaf_accessor_func() })
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize> FusedIterator for $name<'a, K, V, PREFIX_LEN> {}
    };
}

implement_prefix_iter!(
    /// An iterator over a range of entries that all have the same key prefix in a [`TreeMap`].
    ///
    /// This struct is created by the [`prefix`][TreeMap::prefix] method on `TreeMap`.
    /// See its documentation for more details.
    struct Prefix {
        tree: &'a TreeMap<K, V, PREFIX_LEN>,
        item: (&'a K, &'a V),
        as_key_value_ref
    }
);

implement_prefix_iter!(
    /// A mutable iterator over a range of entries that all have the same key prefix in a [`TreeMap`].
    ///
    /// This struct is created by the [`prefix_mut`][TreeMap::prefix_mut] method on `TreeMap`.
    /// See its documentation for more details.
    struct PrefixMut {
        tree: &'a mut TreeMap<K, V, PREFIX_LEN>,
        item: (&'a K, &'a mut V),
        as_key_ref_value_mut
    }
);

#[cfg(test)]
mod tests {
    use crate::{tests_common::swap, TreeMap};

    #[test]
    fn prefix() {
        let mut t = TreeMap::new();
        t.insert(c"abcde", 0);
        t.insert(c"abcx", 0);
        t.insert(c"abcdx", 0);
        t.insert(c"bx", 0);
        let p0: Vec<_> = t.prefix(c"abcde".to_bytes()).collect();
        let p1: Vec<_> = t.prefix(c"abcde".to_bytes()).rev().collect();
        assert_eq!(p0, vec![(&c"abcde", &0)]);
        assert_eq!(p1, vec![(&c"abcde", &0)]);

        let mut t = TreeMap::new();
        t.insert(c"abcde", 0);
        t.insert(c"abcdexxx", 0);
        t.insert(c"abcdexxy", 0);
        t.insert(c"abcdx", 0);
        t.insert(c"abcx", 0);
        t.insert(c"bx", 0);
        let p0: Vec<_> = t.prefix(c"abcde".to_bytes()).collect();
        let p1: Vec<_> = t.prefix(c"abcde".to_bytes()).rev().collect();
        assert_eq!(
            p0,
            vec![(&c"abcde", &0), (&c"abcdexxx", &0), (&c"abcdexxy", &0)]
        );
        assert_eq!(
            p1,
            vec![(&c"abcdexxy", &0), (&c"abcdexxx", &0), (&c"abcde", &0)]
        );

        let mut t = TreeMap::new();
        t.insert(c"abcdexxx", 0);
        t.insert(c"abcdexxy", 0);
        t.insert(c"abcx", 0);
        t.insert(c"bx", 0);
        let p0: Vec<_> = t.prefix(c"abcde".to_bytes()).collect();
        let p1: Vec<_> = t.prefix(c"abcde".to_bytes()).rev().collect();
        assert_eq!(p0, vec![(&c"abcdexxx", &0), (&c"abcdexxy", &0)]);
        assert_eq!(p1, vec![(&c"abcdexxy", &0), (&c"abcdexxx", &0)]);
    }

    #[test]
    fn empty_tree_returns_no_entries() {
        let tree = TreeMap::<[u8; 2], usize>::new();

        assert_eq!(tree.prefix(&[]).count(), 0);
    }

    #[test]
    fn empty_prefix_returns_all_entries() {
        let tree: TreeMap<_, _> = [[0, 0, 0], [255, 12, 12], [127, 8, 2]]
            .into_iter()
            .enumerate()
            .map(swap)
            .collect();

        assert_eq!(tree.prefix(&[]).count(), 3);
    }

    #[test]
    fn singleton_tree_wrong_key_returns_no_entries() {
        let tree: TreeMap<_, _> = [[0, 0, 0]].into_iter().enumerate().map(swap).collect();

        assert_eq!(tree.prefix(&[255, 255, 255]).count(), 0);
    }

    #[test]
    fn non_existent_prefix_returns_no_entries() {
        let tree: TreeMap<_, _> = [[0, 0, 0], [255, 12, 12], [127, 8, 2]]
            .into_iter()
            .enumerate()
            .map(swap)
            .collect();

        assert_eq!(tree.prefix(&[128]).count(), 0);
    }
}
