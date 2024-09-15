//! This module contains types and functions relating to iterating over a
//! range of the [`TreeMap`].

use std::{
    cmp::Ordering,
    fmt,
    iter::FusedIterator,
    ops::{Bound, ControlFlow},
};

use crate::{
    map::NonEmptyTree, maximum_unchecked, minimum_unchecked, AsBytes, ConcreteNodePtr, InnerNode,
    LeafNode, MatchPrefixResult, NodePtr, OpaqueNodePtr, RawIterator, TreeMap,
};

/// This struct contains details of where and why the search stopped in an inner
/// node.
struct InnerNodeSearchResult<K, V, const PREFIX_LEN: usize> {
    /// This is a pointer to the inner node where search stopped.
    node_ptr: OpaqueNodePtr<K, V, PREFIX_LEN>,

    /// The number of bytes of the key that were consumed, not including the
    /// byte that was used to look for a child node.
    current_depth: usize,

    /// This is a comparison from the full prefix of the inner node to the
    /// corresponding segment of the search key.
    node_prefix_comparison_to_search_key_segment: Ordering,

    /// This field indicates why the search stopped in the inner node.
    reason: InnerNodeSearchResultReason,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for InnerNodeSearchResult<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNodeSearchResult")
            .field("node_ptr", &self.node_ptr)
            .field("current_depth", &self.current_depth)
            .field(
                "node_prefix_comparison_to_search_key_segment",
                &self.node_prefix_comparison_to_search_key_segment,
            )
            .field("reason", &self.reason)
            .finish()
    }
}

/// These are search termination reasons specific to inner nodes.
#[derive(Debug)]
enum InnerNodeSearchResultReason {
    /// This variant means the search terminated in a mismatched prefix of an
    /// inner node OR the prefix matched, but there were insufficient key bytes
    /// to lookup a child of the inner node.
    PrefixMismatchOrInsufficientBytes,
    /// This variant means the search terminated in an inner node, when there
    /// was no corresponding child for a key byte.
    MissingChild,
}

/// This enum provides the different cases of search result when looking for a
/// starting/ending point for iteration.
enum TerminatingNodeSearchResult<K, V, const PREFIX_LEN: usize> {
    /// This variant means the search terminated at a leaf node.
    Leaf {
        /// The leaf node pointer where search terminated.
        leaf_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
        /// The ordering of the leaf key bytes relative to the search bytes.
        leaf_key_comparison_to_search_key: Ordering,
    },
    /// This variant means the search terminated at an inner node.
    InnerNode(InnerNodeSearchResult<K, V, PREFIX_LEN>),
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for TerminatingNodeSearchResult<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Leaf {
                leaf_ptr,
                leaf_key_comparison_to_search_key,
            } => f
                .debug_struct("Leaf")
                .field("leaf_ptr", leaf_ptr)
                .field(
                    "leaf_key_comparison_to_search_key",
                    leaf_key_comparison_to_search_key,
                )
                .finish(),
            Self::InnerNode(arg0) => f.debug_tuple("InnerNode").field(arg0).finish(),
        }
    }
}

/// Find the node (inner or leaf) that is identified by the given bytestring.
///
/// # Safety
///
/// This function cannot be called concurrently with any mutating operation
/// on `root` or any child node of `root`. This function will arbitrarily
/// read to any child in the given tree.
unsafe fn find_terminating_node<K: AsBytes, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
) -> TerminatingNodeSearchResult<K, V, PREFIX_LEN> {
    /// This function will search some key bytes at a specific depth in the
    /// given inner node, returning different results depending on if the search
    /// terminated or needs to continue down the trie.
    ///
    /// If this function returns [`ControlFlow::Continue`] then the search
    /// continues down the trie, otherwise it terminates at this inner node.
    ///
    /// # Safety
    ///
    /// Callers must guarantee that there is no concurrent mutation of the given
    /// inner node for the duration of this function.
    unsafe fn check_prefix_lookup_child<K, V, N, const PREFIX_LEN: usize>(
        inner_ptr: NodePtr<PREFIX_LEN, N>,
        key_bytes: &[u8],
        current_depth: &mut usize,
    ) -> ControlFlow<InnerNodeSearchResult<K, V, PREFIX_LEN>, OpaqueNodePtr<K, V, PREFIX_LEN>>
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
        K: AsBytes,
    {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `check_prefix_lookup_child` function.
        let inner_node = unsafe { inner_ptr.as_ref() };
        let match_prefix = inner_node.match_prefix(key_bytes, *current_depth);
        match match_prefix {
            MatchPrefixResult::Mismatch { .. } => {
                let (full_prefix, _) = inner_node.read_full_prefix(*current_depth);
                let upper_bound = (*current_depth + full_prefix.len()).min(key_bytes.len());
                let key_segment = &key_bytes[(*current_depth)..upper_bound];

                let node_prefix_comparison_to_search_key_segment = full_prefix.cmp(key_segment);

                ControlFlow::Break(InnerNodeSearchResult {
                    node_ptr: inner_ptr.to_opaque(),
                    current_depth: *current_depth,
                    reason: InnerNodeSearchResultReason::PrefixMismatchOrInsufficientBytes,
                    node_prefix_comparison_to_search_key_segment,
                })
            },
            MatchPrefixResult::Match { matched_bytes } => {
                // Since the prefix matched, advance the depth by the size of the prefix
                *current_depth += matched_bytes;

                let next_key_fragment = if *current_depth < key_bytes.len() {
                    key_bytes[*current_depth]
                } else {
                    // the key has insufficient bytes, it is a prefix of an existing key. Thus, the
                    // key must not exist in the tree by the requirements of the insert function
                    // (any key in the tree must not be the prefix of any other key in the tree)
                    return ControlFlow::Break(InnerNodeSearchResult {
                        node_ptr: inner_ptr.to_opaque(),
                        current_depth: *current_depth,
                        reason: InnerNodeSearchResultReason::PrefixMismatchOrInsufficientBytes,
                        node_prefix_comparison_to_search_key_segment: Ordering::Equal,
                    });
                };

                let child_lookup = inner_node.lookup_child(next_key_fragment);

                match child_lookup {
                    Some(child_ptr) => {
                        // Since the prefix matched and it found a child, advance the depth by 1
                        // more key byte
                        *current_depth += 1;
                        ControlFlow::Continue(child_ptr)
                    },
                    None => ControlFlow::Break(InnerNodeSearchResult {
                        node_ptr: inner_ptr.to_opaque(),
                        current_depth: *current_depth,
                        reason: InnerNodeSearchResultReason::MissingChild,
                        node_prefix_comparison_to_search_key_segment: Ordering::Equal,
                    }),
                }
            },
        }
    }

    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        let next_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety documentation on the
                // containing function
                check_prefix_lookup_child(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety documentation on the
                // containing function
                check_prefix_lookup_child(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety documentation on the
                // containing function
                check_prefix_lookup_child(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety documentation on the
                // containing function
                check_prefix_lookup_child(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_ptr) => {
                // SAFETY: The shared reference is bounded to this block and there are no
                // concurrent modifications, by the safety conditions of this function.
                let leaf_node = unsafe { leaf_ptr.as_ref() };

                let leaf_key_comparison_to_search_key =
                    leaf_node.key_ref().as_bytes().cmp(key_bytes);

                return TerminatingNodeSearchResult::Leaf {
                    leaf_ptr,
                    leaf_key_comparison_to_search_key,
                };
            },
        };

        match next_node {
            ControlFlow::Continue(next_node) => {
                current_node = next_node;
            },
            ControlFlow::Break(reason) => {
                return TerminatingNodeSearchResult::InnerNode(reason);
            },
        }
    }
}

/// This function searches a trie for the smallest/largest leaf node that is
/// greater/less than the given bound.
///
/// If `is_start` is true, its looking for the smallest leaf node that is
/// greater than the given bound. If `is_start` is false, we're looking for the
/// greatest leaf node that is smaller than the given bound.
///
/// # Safety
///
/// Callers must guarantee that there is no concurrent mutation of the given
/// trie for the duration of this function.
unsafe fn find_leaf_pointer_for_bound<K: AsBytes, V, const PREFIX_LEN: usize>(
    tree: &NonEmptyTree<K, V, PREFIX_LEN>,
    bound: Bound<&[u8]>,
    is_start: bool,
) -> Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>> {
    Some(match bound {
        Bound::Included(key_bytes) | Bound::Excluded(key_bytes) => {
            // SAFETY: Covered by function safety doc
            let terminating_node = unsafe { find_terminating_node(tree.root, key_bytes) };

            match terminating_node {
                TerminatingNodeSearchResult::Leaf {
                    leaf_ptr,
                    leaf_key_comparison_to_search_key,
                } => match leaf_key_comparison_to_search_key {
                    Ordering::Less => {
                        if is_start {
                            // SAFETY: Covered by function safety doc
                            let leaf = unsafe { leaf_ptr.as_ref() };
                            leaf.next?
                        } else {
                            leaf_ptr
                        }
                    },
                    Ordering::Equal => {
                        if matches!(bound, Bound::Excluded(_)) {
                            // SAFETY: Covered by function safety doc
                            let leaf = unsafe { leaf_ptr.as_ref() };
                            if is_start { leaf.next } else { leaf.previous }?
                        } else {
                            leaf_ptr
                        }
                    },
                    Ordering::Greater => {
                        if is_start {
                            leaf_ptr
                        } else {
                            // SAFETY: Covered by function safety doc
                            let leaf = unsafe { leaf_ptr.as_ref() };
                            leaf.previous?
                        }
                    },
                },
                TerminatingNodeSearchResult::InnerNode(InnerNodeSearchResult {
                    node_ptr,
                    current_depth,
                    reason,
                    node_prefix_comparison_to_search_key_segment,
                }) => match reason {
                    InnerNodeSearchResultReason::PrefixMismatchOrInsufficientBytes => {
                        match (is_start, node_prefix_comparison_to_search_key_segment) {
                            (true, Ordering::Equal | Ordering::Greater) => unsafe {
                                // SAFETY: Covered by function safety doc
                                minimum_unchecked(node_ptr)
                            },
                            (true, Ordering::Less) => unsafe {
                                // SAFETY: Covered by function safety doc
                                let max_leaf_ptr = maximum_unchecked(node_ptr);
                                let max_leaf = max_leaf_ptr.as_ref();
                                max_leaf.next?
                            },
                            (false, Ordering::Equal | Ordering::Less) => unsafe {
                                // SAFETY: Covered by function safety doc
                                maximum_unchecked(node_ptr)
                            },
                            (false, Ordering::Greater) => unsafe {
                                // SAFETY: Covered by function safety doc
                                let min_leaf_ptr = minimum_unchecked(node_ptr);
                                let min_leaf = min_leaf_ptr.as_ref();
                                min_leaf.previous?
                            },
                        }
                    },
                    InnerNodeSearchResultReason::MissingChild => {
                        fn access_closest_child<
                            const PREFIX_LEN: usize,
                            N: InnerNode<PREFIX_LEN>,
                        >(
                            inner_ptr: NodePtr<PREFIX_LEN, N>,
                            child_bounds: (Bound<u8>, Bound<u8>),
                            is_start: bool,
                        ) -> Option<(u8, OpaqueNodePtr<N::Key, N::Value, PREFIX_LEN>)>
                        {
                            // SAFETY: Covered by function safety doc
                            let inner = unsafe { inner_ptr.as_ref() };
                            let mut child_it = inner.range(child_bounds);
                            if is_start {
                                child_it.next()
                            } else {
                                child_it.next_back()
                            }
                        }

                        let child_bounds = if is_start {
                            (bound.map(|_| key_bytes[current_depth]), Bound::Unbounded)
                        } else {
                            (Bound::Unbounded, bound.map(|_| key_bytes[current_depth]))
                        };
                        let possible_next_child = match node_ptr.to_node_ptr() {
                            ConcreteNodePtr::Node4(inner_ptr) => {
                                access_closest_child(inner_ptr, child_bounds, is_start)
                            },
                            ConcreteNodePtr::Node16(inner_ptr) => {
                                access_closest_child(inner_ptr, child_bounds, is_start)
                            },
                            ConcreteNodePtr::Node48(inner_ptr) => {
                                access_closest_child(inner_ptr, child_bounds, is_start)
                            },
                            ConcreteNodePtr::Node256(inner_ptr) => {
                                access_closest_child(inner_ptr, child_bounds, is_start)
                            },
                            ConcreteNodePtr::LeafNode(_) => unreachable!(
                                "This branch is unreachable because the \
                                 TerminatingNodeSearchResult had the value InnerNode"
                            ),
                        };
                        let (_, next_child) = possible_next_child?;

                        if is_start {
                            // SAFETY: Covered by function safety doc
                            unsafe { minimum_unchecked(next_child) }
                        } else {
                            // SAFETY: Covered by function safety doc
                            unsafe { maximum_unchecked(next_child) }
                        }
                    },
                },
            }
        },
        Bound::Unbounded => {
            if is_start {
                tree.min_leaf
            } else {
                tree.max_leaf
            }
        },
    })
}

macro_rules! implement_range_iter {
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
            /// Create a new range iterator over the given tree, starting and ending
            /// according to the given bounds.
            ///
            /// # Panics
            ///
            /// This function will panic if `start_bound` is greater than `end_bound`.
            pub(crate) fn new(
                tree: $tree_ty,
                start_bound: Bound<&[u8]>,
                end_bound: Bound<&[u8]>,
            ) -> Self {
                let Some(tree_state) = &tree.state else {
                    return Self {
                        _tree: tree,
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

                // SAFETY: Since we have a (shared or mutable) reference to the original TreeMap, we know
                // there will be no concurrent mutation
                let possible_start =
                    unsafe { find_leaf_pointer_for_bound(tree_state, start_bound, true) };
                let Some(start) = possible_start else {
                    return Self {
                        _tree: tree,
                        inner: RawIterator::empty(),
                    };
                };

                // SAFETY: Since we have a (shared or mutable) reference to the original TreeMap, we know
                // there will be no concurrent mutation
                let possible_end =
                    unsafe { find_leaf_pointer_for_bound(tree_state, end_bound, false) };
                let Some(end) = possible_end else {
                    return Self {
                        _tree: tree,
                        inner: RawIterator::empty(),
                    };
                };

                // SAFETY: Since we have a (shared or mutable) reference to the original TreeMap, we know
                // there will be no concurrent mutation. Also, the reference lifetimes created
                // are bounded to this `unsafe` block, and don't overlap with any mutation.
                unsafe {
                    let start_leaf_bytes = start.as_key_ref().as_bytes();
                    let end_leaf_bytes = end.as_key_ref().as_bytes();

                    if start_leaf_bytes > end_leaf_bytes {
                        // Resolved start leaf is not less than or equal to resolved end leaf for
                        // iteration order
                        return Self {
                            _tree: tree,
                            inner: RawIterator::empty(),
                        };
                    }
                }

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

                // SAFETY: THe lifetimes returned from this function are returned as bounded by
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

implement_range_iter!(
    /// An iterator over a sub-range of entries in a [`TreeMap`].
    ///
    /// This struct is created by the [`range`][TreeMap::range] method on `TreeMap`.
    /// See its documentation for more details.
    struct Range {
        tree: &'a TreeMap<K, V, PREFIX_LEN>,
        item: (&'a K, &'a V),
        as_key_value_ref
    }
);

implement_range_iter!(
    /// A mutable iterator over a sub-range of entries in a [`TreeMap`].
    ///
    /// This struct is created by the [`range_mut`][TreeMap::range_mut] method on `TreeMap`.
    /// See its documentation for more details.
    struct RangeMut {
        tree: &'a mut TreeMap<K, V, PREFIX_LEN>,
        item: (&'a K, &'a mut V),
        as_key_ref_value_mut
    }
);

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture_tree() -> TreeMap<[u8; 3], usize> {
        fn swap<A, B>((a, b): (A, B)) -> (B, A) {
            (b, a)
        }

        [
            [0, 0, 0],
            [0, 0, u8::MAX],
            [0, u8::MAX, 0],
            [0, u8::MAX, u8::MAX],
            [127, 127, 0],
            [127, 127, 127],
            [127, 127, u8::MAX],
            [u8::MAX, 0, 0],
            [u8::MAX, 0, u8::MAX],
            [u8::MAX, u8::MAX, 0],
            [u8::MAX, u8::MAX, u8::MAX],
        ]
        .into_iter()
        .enumerate()
        .map(swap)
        .collect()
    }

    #[test]
    fn range_iteration_normal_tree() {
        let tree = fixture_tree();

        // Included on end of key range
        let mut it = Range::new(
            &tree,
            Bound::Included([u8::MAX, u8::MAX, u8::MAX].as_slice()),
            Bound::Unbounded,
        )
        .map(|(k, _)| k);
        assert_eq!(it.next().unwrap(), &[u8::MAX, u8::MAX, u8::MAX]);
        assert_eq!(it.next(), None);

        // Excluded on end of key range
        let mut it = Range::new(
            &tree,
            Bound::Excluded([u8::MAX, u8::MAX, u8::MAX].as_slice()),
            Bound::Unbounded,
        )
        .map(|(k, _)| k);
        assert_eq!(it.next(), None);

        // Included on start of key range
        let mut it = Range::new(
            &tree,
            Bound::Unbounded,
            Bound::Included([0, 0, 0].as_slice()),
        )
        .map(|(k, _)| k);
        assert_eq!(it.next().unwrap(), &[0, 0, 0]);
        assert_eq!(it.next(), None);

        // Excluded on start of key range
        let mut it = Range::new(
            &tree,
            Bound::Unbounded,
            Bound::Excluded([0, 0, 0].as_slice()),
        )
        .map(|(k, _)| k);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn range_iteration_on_key_prefix() {
        let tree = fixture_tree();

        let mut it = Range::new(
            &tree,
            Bound::Included([0].as_slice()),
            Bound::Excluded([1].as_slice()),
        )
        .map(|(k, _)| k);

        assert_eq!(it.next().unwrap(), &[0, 0, 0]);
        assert_eq!(it.next().unwrap(), &[0, 0, u8::MAX]);
        assert_eq!(it.next().unwrap(), &[0, u8::MAX, 0]);
        assert_eq!(it.next().unwrap(), &[0, u8::MAX, u8::MAX]);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn range_prefix_mismatch_or_insufficient_bytes_lower_bounds() {
        let tree = fixture_tree();

        let mut it = Range::new(
            &tree,
            Bound::Included([127, 126].as_slice()),
            Bound::Excluded([128].as_slice()),
        )
        .map(|(k, _)| k);

        // This should produce the 3 keys because the start key [127, 126] is ordered
        // before the key [127, 127, 0]
        assert!([127, 126].as_slice() < [127, 127, 0].as_slice());
        assert_eq!(it.next().unwrap(), &[127, 127, 0]);
        assert_eq!(it.next().unwrap(), &[127, 127, 127]);
        assert_eq!(it.next().unwrap(), &[127, 127, u8::MAX]);
        assert_eq!(it.next(), None);

        let mut it = Range::new(
            &tree,
            Bound::Included([127, 128].as_slice()),
            Bound::Excluded([128].as_slice()),
        )
        .map(|(k, _)| k);

        // This should produce no keys because the start key [127, 128] is ordered after
        // the key [127, 127, u8::MAX]
        assert!([127, 128].as_slice() > [127, 127, u8::MAX].as_slice());
        assert_eq!(it.next(), None);

        let mut it = Range::new(
            &tree,
            Bound::Included([127].as_slice()),
            Bound::Excluded([128].as_slice()),
        )
        .map(|(k, _)| k);

        // This should produce the 3 keys because the start key [127] is ordered
        // before the key [127, 127, 0]
        assert!([127].as_slice() < [127, 127, 0].as_slice());
        assert_eq!(it.next().unwrap(), &[127, 127, 0]);
        assert_eq!(it.next().unwrap(), &[127, 127, 127]);
        assert_eq!(it.next().unwrap(), &[127, 127, u8::MAX]);
        assert_eq!(it.next(), None);

        let mut it = Range::new(
            &tree,
            Bound::Included([127, 127].as_slice()),
            Bound::Excluded([128].as_slice()),
        )
        .map(|(k, _)| k);

        // This should produce the 3 keys because the start key [127, 127] is ordered
        // before the key [127, 127, 0]
        assert!([127, 127].as_slice() < [127, 127, 0].as_slice());
        assert_eq!(it.next().unwrap(), &[127, 127, 0]);
        assert_eq!(it.next().unwrap(), &[127, 127, 127]);
        assert_eq!(it.next().unwrap(), &[127, 127, u8::MAX]);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn range_prefix_mismatch_or_insufficient_bytes_upper_bounds() {
        let tree = fixture_tree();

        let mut it = Range::new(
            &tree,
            Bound::Excluded([126].as_slice()),
            Bound::Excluded([128].as_slice()),
        )
        .map(|(k, _)| k);
        assert_eq!(it.next().unwrap(), &[127, 127, 0]);
        assert_eq!(it.next().unwrap(), &[127, 127, 127]);
        assert_eq!(it.next().unwrap(), &[127, 127, u8::MAX]);
        assert_eq!(it.next(), None);

        let mut it = Range::new(
            &tree,
            Bound::Excluded([126].as_slice()),
            Bound::Included([127, 127, u8::MAX].as_slice()),
        )
        .map(|(k, _)| k);
        assert_eq!(it.next().unwrap(), &[127, 127, 0]);
        assert_eq!(it.next().unwrap(), &[127, 127, 127]);
        assert_eq!(it.next().unwrap(), &[127, 127, u8::MAX]);
        assert_eq!(it.next(), None);

        let mut it = Range::new(
            &tree,
            Bound::Excluded([126].as_slice()),
            Bound::Included([127, 127, 0].as_slice()),
        )
        .map(|(k, _)| k);
        assert_eq!(it.next().unwrap(), &[127, 127, 0]);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn empty_tree_empty_iterator() {
        let tree = TreeMap::<[u8; 3], usize>::new();

        let it = Range::new(
            &tree,
            Bound::Excluded([1, 1, 1].as_slice()),
            Bound::Excluded([1, 1, 1].as_slice()),
        );

        assert_eq!(it.count(), 0);
    }

    #[test]
    #[should_panic(expected = "range start and end are equal and excluded: ([1, 1, 1])")]
    fn equal_excluded_bounds_should_panic() {
        let tree = fixture_tree();

        let _it = Range::new(
            &tree,
            Bound::Excluded([1, 1, 1].as_slice()),
            Bound::Excluded([1, 1, 1].as_slice()),
        );
    }

    #[test]
    #[should_panic(expected = "range start ([1, 1, 1]) is greater than range end ([0, 0, 0])")]
    fn excluded_excluded_start_greater_than_end_should_panic() {
        let tree = fixture_tree();

        let _it = Range::new(
            &tree,
            Bound::Excluded([1, 1, 1].as_slice()),
            Bound::Excluded([0, 0, 0].as_slice()),
        );
    }

    #[test]
    #[should_panic(expected = "range start ([1, 1, 1]) is greater than range end ([0, 0, 0])")]
    fn included_included_start_greater_than_end_should_panic() {
        let tree = fixture_tree();

        let _it = Range::new(
            &tree,
            Bound::Included([1, 1, 1].as_slice()),
            Bound::Included([0, 0, 0].as_slice()),
        );
    }

    #[test]
    fn excluded_excluded_empty_range_should_be_empty() {
        let tree = fixture_tree();

        let it = Range::new(
            &tree,
            Bound::Excluded([127, 127, 127].as_slice()),
            Bound::Excluded([127, 127, 128].as_slice()),
        );

        assert_eq!(it.count(), 0);

        let it = Range::new(
            &tree,
            Bound::Excluded([127, 127, 126].as_slice()),
            Bound::Excluded([127, 127, 127].as_slice()),
        );

        assert_eq!(it.count(), 0);
    }

    #[test]
    fn included_included_range_on_middle() {
        let tree = fixture_tree();

        let mut it = Range::new(
            &tree,
            Bound::Included([126, 0, 0].as_slice()),
            Bound::Included([128, 0, 0].as_slice()),
        )
        .map(|(k, _)| k);

        assert_eq!(it.next().unwrap(), &[127, 127, 0]);
        assert_eq!(it.next().unwrap(), &[127, 127, 127]);
        assert_eq!(it.next().unwrap(), &[127, 127, u8::MAX]);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn range_mut_mutate_some_keys() {
        let mut tree = fixture_tree();

        tree.values_mut().for_each(|value| *value = 0);

        tree.range_mut([126, 0, 0]..=[128u8, 0, 0])
            .for_each(|(_, value)| *value = 1024);

        assert_eq!(
            tree.into_iter().collect::<Vec<_>>(),
            [
                ([0, 0, 0], 0),
                ([0, 0, 255], 0),
                ([0, 255, 0], 0),
                ([0, 255, 255], 0),
                ([127, 127, 0], 1024),
                ([127, 127, 127], 1024),
                ([127, 127, 255], 1024),
                ([255, 0, 0], 0),
                ([255, 0, 255], 0),
                ([255, 255, 0], 0),
                ([255, 255, 255], 0)
            ]
        );
    }
}
