use core::iter::FusedIterator;

use super::{
    find_terminating_node, InnerNodeSearchResult, InnerNodeSearchResultReason,
    TerminatingNodeSearchResult,
};
use crate::{
    allocator::{Allocator, Global},
    map::{NonEmptyTree, DEFAULT_PREFIX_LEN},
    raw::{maximum_unchecked, minimum_unchecked, RawIterator},
    AsBytes, TreeMap,
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
        pub struct $name<'a, K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global> {
            inner: RawIterator<K, V, PREFIX_LEN>,
            _tree: $tree_ty,
        }

        impl<'a, K: AsBytes, V, A: Allocator, const PREFIX_LEN: usize> $name<'a, K, V, PREFIX_LEN, A> {
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

                let inner = prefix_iter_constructor(tree_state, prefix);

                Self {
                    _tree: tree,
                    inner,
                }
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> Iterator for $name<'a, K, V, PREFIX_LEN, A> {
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

        impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> DoubleEndedIterator
            for $name<'a, K, V, PREFIX_LEN, A>
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

        impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> FusedIterator for $name<'a, K, V, PREFIX_LEN, A> {}
    };
}

fn prefix_iter_constructor<K: AsBytes, V, const PREFIX_LEN: usize>(
    tree_state: &NonEmptyTree<K, V, PREFIX_LEN>,
    prefix: &[u8],
) -> RawIterator<K, V, PREFIX_LEN> {
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
                return RawIterator::empty();
            }
        },
        TerminatingNodeSearchResult::InnerNode(InnerNodeSearchResult {
            node_ptr, reason, ..
        }) => {
            match reason {
                InnerNodeSearchResultReason::PrefixMismatch
                | InnerNodeSearchResultReason::MissingChild => {
                    // if the child is missing OR there is a prefix mismatch, then there is nothing
                    // to be the prefix of
                    return RawIterator::empty();
                },
                InnerNodeSearchResultReason::InsufficientBytes => {
                    // SAFETY: Its safe to create a shared reference to the leaf since we hold
                    // either a shared or mutable reference to the owning TreeMap, which prevents
                    // other concurrent mutable references.
                    unsafe { (minimum_unchecked(node_ptr), maximum_unchecked(node_ptr)) }
                },
            }
        },
    };

    // SAFETY: `start` is guaranteed to be less than or equal to `end` in the
    // iteration order because of the check we do on the bytes of the resolved
    // leaf pointers, just above this line
    unsafe { RawIterator::new(start, end) }
}

implement_prefix_iter!(
    /// An iterator over a range of entries that all have the same key prefix in a [`TreeMap`].
    ///
    /// This struct is created by the [`prefix`][TreeMap::prefix] method on `TreeMap`.
    /// See its documentation for more details.
    struct Prefix {
        tree: &'a TreeMap<K, V, PREFIX_LEN, A>,
        item: (&'a K, &'a V),
        as_key_value_ref
    }
);

// SAFETY: This iterator holds a shared reference to the underlying `TreeMap`
// and thus can be moved across threads if the `TreeMap<K, V>: Sync`.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for Prefix<'_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

// SAFETY: This iterator has no interior mutability and can be shared across
// thread so long as the reference `TreeMap<K, V>` can as well.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for Prefix<'_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

implement_prefix_iter!(
    /// A mutable iterator over a range of entries that all have the same key prefix in a [`TreeMap`].
    ///
    /// This struct is created by the [`prefix_mut`][TreeMap::prefix_mut] method on `TreeMap`.
    /// See its documentation for more details.
    struct PrefixMut {
        tree: &'a mut TreeMap<K, V, PREFIX_LEN, A>,
        item: (&'a K, &'a mut V),
        as_key_ref_value_mut
    }
);

// SAFETY: This iterator has a mutable reference to the underlying `TreeMap` and
// can be moved across threads if `&mut TreeMap<K, V>` is `Send`, which requires
// `TreeMap<K, V>` to be `Send` as well.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for PrefixMut<'_, K, V, PREFIX_LEN, A>
where
    K: Send,
    V: Send,
    A: Send + Allocator,
{
}

// SAFETY: This iterator uses no interior mutability and can be shared across
// threads so long as `TreeMap<K, V>: Sync`.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for PrefixMut<'_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::*;
    use crate::{testing::swap, TreeMap};

    #[test]
    fn iterators_are_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        fn prefix_is_send<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_send::<Prefix<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn prefix_is_sync<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_sync::<Prefix<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        prefix_is_send::<[u8; 3], usize, Global>();
        prefix_is_sync::<[u8; 3], usize, Global>();

        fn prefix_mut_is_send<'a, K: Send + 'a, V: Send + 'a, A: Send + Allocator + 'a>() {
            is_send::<PrefixMut<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn prefix_mut_is_sync<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_sync::<PrefixMut<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        prefix_mut_is_send::<[u8; 3], usize, Global>();
        prefix_mut_is_sync::<[u8; 3], usize, Global>();
    }

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

    #[test]
    fn prefix_mut() {
        let mut t = TreeMap::new();
        t.insert(c"abcde", 0);
        t.insert(c"abcx", 0);
        t.insert(c"abcdx", 0);
        t.insert(c"bx", 0);

        for (key, value) in t.prefix_mut(c"abc".to_bytes()) {
            if key.to_bytes().ends_with(b"x") {
                *value = 100;
            }
        }

        assert_eq!(
            t.into_iter().collect::<Vec<_>>(),
            vec![(c"abcde", 0), (c"abcdx", 100), (c"abcx", 100), (c"bx", 0)]
        )
    }

    #[test]
    fn prefix_mut_rev() {
        let mut t = TreeMap::new();
        t.insert(c"abcde", 1);
        t.insert(c"abcdexxx", 2);
        t.insert(c"abcdexxy", 3);
        t.insert(c"bx", 4);

        let result: Vec<_> = t.prefix_mut(c"abcde".to_bytes()).rev().collect();
        assert_eq!(
            result,
            vec![
                (&c"abcdexxy", &mut 3),
                (&c"abcdexxx", &mut 2),
                (&c"abcde", &mut 1),
            ]
        );
    }

    #[test]
    fn prefix_interleaved_forward_and_backward() {
        let mut t = TreeMap::new();
        t.insert(c"abcde", 0);
        t.insert(c"abcdexxx", 1);
        t.insert(c"abcdexxy", 2);
        t.insert(c"abcdexyz", 3);

        let mut it = t.prefix(c"abcde".to_bytes());
        assert_eq!(it.next(), Some((&c"abcde", &0)));
        assert_eq!(it.next_back(), Some((&c"abcdexyz", &3)));
        assert_eq!(it.next(), Some((&c"abcdexxx", &1)));
        assert_eq!(it.next_back(), Some((&c"abcdexxy", &2)));
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);
    }

    #[test]
    fn prefix_fused_after_exhaustion() {
        let mut t = TreeMap::new();
        t.insert(c"abc", 0);

        let mut it = t.prefix(c"abc".to_bytes());
        assert_eq!(it.next(), Some((&c"abc", &0)));
        assert_eq!(it.next(), None);
        // fused: must keep returning None
        assert_eq!(it.next(), None);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn prefix_longer_than_all_keys_returns_empty() {
        let mut t = TreeMap::new();
        t.insert(c"ab", 0);
        t.insert(c"abc", 1);

        // Searching for a prefix longer than any existing key
        assert_eq!(t.prefix(b"abcdefgh").count(), 0);
    }

    #[test]
    fn prefix_key_is_also_a_prefix_of_other_keys() {
        // "abcde" is both a key and a prefix of "abcdexxx"
        let mut t = TreeMap::new();
        t.insert(c"abcde", 0);
        t.insert(c"abcdexxx", 1);
        t.insert(c"abcx", 2);

        let p: Vec<_> = t.prefix(c"abcde".to_bytes()).collect();
        assert_eq!(p, vec![(&c"abcde", &0), (&c"abcdexxx", &1)]);
    }

    #[test]
    fn prefix_single_matching_key() {
        let mut t = TreeMap::new();
        t.insert([1u8, 2u8, 3u8], 42);

        assert_eq!(t.prefix(&[1u8, 2u8, 3u8]).count(), 1);
        assert_eq!(t.prefix(&[1u8, 2u8]).count(), 1);
        assert_eq!(t.prefix(&[1u8]).count(), 1);
        assert_eq!(t.prefix(&[2u8]).count(), 0);
    }

    #[test]
    fn prefix_multiple_disjoint_subtrees() {
        // Keys share no common prefix; each subtree should be isolated
        let mut t = TreeMap::new();
        t.insert(c"aaa", 0);
        t.insert(c"aab", 1);
        t.insert(c"baa", 2);
        t.insert(c"bab", 3);

        let pa: Vec<_> = t.prefix(c"a".to_bytes()).collect();
        assert_eq!(pa, vec![(&c"aaa", &0), (&c"aab", &1)]);

        let pb: Vec<_> = t.prefix(c"b".to_bytes()).collect();
        assert_eq!(pb, vec![(&c"baa", &2), (&c"bab", &3)]);
    }

    #[test]
    fn prefix_full_key_bytes_no_nul_terminator() {
        // Use raw byte arrays so there is no implicit NUL; the prefix is the
        // full key, ensuring the leaf-check path in the iterator is exercised.
        let mut t = TreeMap::<[u8; 3], i32>::new();
        t.insert([0u8, 0u8, 1u8], 1);
        t.insert([0u8, 0u8, 2u8], 2);
        t.insert([0u8, 1u8, 0u8], 3);

        let p: Vec<_> = t.prefix(&[0u8, 0u8]).collect();
        assert_eq!(p, vec![(&[0u8, 0u8, 1u8], &1), (&[0u8, 0u8, 2u8], &2)]);

        // Prefix that matches exactly one leaf
        let p: Vec<_> = t.prefix(&[0u8, 0u8, 1u8]).collect();
        assert_eq!(p, vec![(&[0u8, 0u8, 1u8], &1)]);
    }

    /// Regression test for https://github.com/declanvk/blart/issues/66
    ///
    /// The prefix iterator should return an empty iterator when no keys match
    /// the prefix. In blart 0.3.0 and 0.4.0 it incorrectly returns both
    /// keys.
    #[test]
    fn prefix_iterator_no_false_matches() {
        // Construct a map with the following keys
        // [0, 0]
        // [0, 1]
        let mut map = TreeMap::<[u8; 2], ()>::new();
        map.insert(0u16.to_be_bytes(), ());
        map.insert(1u16.to_be_bytes(), ());

        // Search for entries with prefix [1, 0]
        let prefix: &[u8] = &256u16.to_be_bytes();

        // There should be no results here
        assert_eq!(0, map.prefix(prefix).count());
    }
}
