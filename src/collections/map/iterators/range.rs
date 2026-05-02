//! This module contains types and functions relating to iterating over a
//! range of the [`TreeMap`].

use core::{
    cmp::Ordering,
    fmt,
    iter::FusedIterator,
    ops::{Bound, ControlFlow},
};

use crate::{
    allocator::{Allocator, Global},
    map::{NonEmptyTree, DEFAULT_PREFIX_LEN},
    raw::{
        match_concrete_node_ptr, maximum_unchecked, minimum_unchecked, ConcreteNodePtr,
        ExplicitMismatch, InnerNode, LeafNode, NodePtr, OpaqueNodePtr, PrefixMatch, RawIterator,
    },
    AsBytes, TreeMap,
};

/// This struct contains details of where and why the search stopped in an inner
/// node.
pub(crate) struct InnerNodeSearchResult<K, V, const PREFIX_LEN: usize> {
    /// This is a pointer to the inner node where search stopped.
    pub node_ptr: OpaqueNodePtr<K, V, PREFIX_LEN>,

    /// The number of bytes of the key that were consumed, not including the
    /// byte that was used to look for a child node.
    pub current_depth: usize,

    /// This is a comparison from the full prefix of the inner node to the
    /// corresponding segment of the search key.
    pub node_prefix_comparison_to_search_key_segment: Ordering,

    /// This field indicates why the search stopped in the inner node.
    pub reason: InnerNodeSearchResultReason,
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
pub(crate) enum InnerNodeSearchResultReason {
    /// This variant means the search terminated in a mismatched prefix of an
    /// inner node.
    PrefixMismatch,
    /// This variant means the search terminated because the key was too short,
    /// not because of a mismatch with prefix or child key byte.
    InsufficientBytes,
    /// This variant means the search terminated in an inner node, when there
    /// was no corresponding child for a key byte.
    MissingChild,
}

/// This enum provides the different cases of search result when looking for a
/// starting/ending point for iteration.
pub(crate) enum TerminatingNodeSearchResult<K, V, const PREFIX_LEN: usize> {
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
pub(crate) unsafe fn find_terminating_node<K: AsBytes, V, const PREFIX_LEN: usize>(
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

        assert!(*current_depth <= key_bytes.len());
        // SAFETY: The condition that "`current_depth` must be less than or equal to
        // `key.len()`" is checked via assertion just above.
        // TODO: Figure out a better reasoning for this safety condition, I think it
        // should be possible just via reasoning through the range lookup
        // process (without needing an assert).
        let match_prefix = unsafe { inner_node.match_full_prefix(key_bytes, *current_depth) };
        match match_prefix {
            Err(ExplicitMismatch {
                matched_bytes,
                node_prefix_comparison_to_search_key_segment,
                ..
            }) => {
                // We report a prefix mismatch if the prefix is longer that the remaining
                // portion of the key bytes. However, in the context of the
                // `InnerNodeSearchResultReason` running out of bytes is really a different
                // thing than a mismatch. We should only report mismatch as the reason if there
                // was an actual byte difference.
                let reason = if matched_bytes == key_bytes[*current_depth..].len() {
                    InnerNodeSearchResultReason::InsufficientBytes
                } else {
                    InnerNodeSearchResultReason::PrefixMismatch
                };

                ControlFlow::Break(InnerNodeSearchResult {
                    node_ptr: inner_ptr.to_opaque(),
                    current_depth: *current_depth,
                    reason,
                    node_prefix_comparison_to_search_key_segment,
                })
            },
            Ok(PrefixMatch { matched_bytes }) => {
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
                        reason: InnerNodeSearchResultReason::InsufficientBytes,
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
        let next_node = match_concrete_node_ptr!(match (current_node.to_node_ptr()) {
            InnerNode(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety documentation on the
                // containing function
                check_prefix_lookup_child(inner_ptr, key_bytes, &mut current_depth)
            },
            LeafNode(leaf_ptr) => {
                // SAFETY: The shared reference is bounded to this block and there are no
                // concurrent modifications, by the safety conditions of this function.
                let leaf_node = unsafe { leaf_ptr.as_ref() };

                let leaf_key_comparison_to_search_key = leaf_node.compare_full_key(key_bytes);

                return TerminatingNodeSearchResult::Leaf {
                    leaf_ptr,
                    leaf_key_comparison_to_search_key,
                };
            },
        });

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

/// Panic if the given range bounds
#[track_caller]
pub(crate) fn validate_range_bounds(start_bound: &Bound<&[u8]>, end_bound: &Bound<&[u8]>) {
    match (*start_bound, *end_bound) {
        (Bound::Excluded(s), Bound::Excluded(e)) if s == e => {
            panic!("range start and end are equal and excluded: ({s:?})")
        },
        (Bound::Included(s) | Bound::Excluded(s), Bound::Included(e) | Bound::Excluded(e))
            if s > e =>
        {
            panic!("range start ({s:?}) is greater than range end ({e:?})")
        },
        _ => {},
    }
}

type KeyByteAndChild<K, V, const PREFIX_LEN: usize> = Option<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>;

/// This function searches a trie for the smallest/largest leaf node that is
/// greater than or equal (GTE) / less than or equal (LTE) to the given bound.
///
/// If `is_start` is true, its looking for the smallest leaf node that is
/// GTE than the given bound. If `is_start` is false, we're looking for the
/// greatest leaf node that is LTE than the given bound.
///
/// # Safety
///
/// Callers must guarantee that there is no concurrent mutation of the given
/// trie for the duration of this function.
pub(crate) unsafe fn find_leaf_pointer_for_bound<K: AsBytes, V, const PREFIX_LEN: usize>(
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
                    InnerNodeSearchResultReason::PrefixMismatch => {
                        // If there was a prefix mismatch while searching, then we must know whether
                        // the mismatch occurred because the search key was
                        // greater than OR less than the prefix.

                        if matches!(
                            node_prefix_comparison_to_search_key_segment,
                            Ordering::Greater
                        ) {
                            // If the node prefix was greater than the search key segment, then our
                            // candidates are going to be around the minimum leaf of this subtree.

                            // SAFETY: Covered by function safety doc
                            let min_leaf_ptr = unsafe { minimum_unchecked(node_ptr) };
                            if is_start {
                                // In the context of a start bound, the search key being
                                // lexicographically smaller is easy to understand, since it will be
                                // ordered before the minimum key of the subtree in all cases.

                                min_leaf_ptr
                            } else {
                                // In the context of a end bound, the search key being
                                // lexicographically shorted means
                                // that none of the keys in this subtree are eligible to
                                // be in range. So we must find the minimum and then go one before
                                // that.

                                // SAFETY: Covered by function safety doc
                                unsafe {
                                    let min_leaf = min_leaf_ptr.as_ref();
                                    min_leaf.previous?
                                }
                            }
                        } else {
                            // We assume here that Equal is impossible otherwise
                            // there would be no mismatch.
                            //
                            // If the node prefix was less than the search key segment, then our
                            // candidates are going to be around the maximum leaf of this subtree.

                            // SAFETY: Covered by function safety doc
                            let max_leaf_ptr = unsafe { maximum_unchecked(node_ptr) };
                            if is_start {
                                // In the case of a start bound, the maximum leaf of this tree is
                                // going to be smaller than the search key. So we need to get the
                                // next larger leaf
                                unsafe {
                                    let max_leaf = max_leaf_ptr.as_ref();
                                    max_leaf.next?
                                }
                            } else {
                                // In the case of an end bound, the maximum leaf is the largest key
                                // less than or equal to the search key, so we return it directly.
                                max_leaf_ptr
                            }
                        }
                    },
                    InnerNodeSearchResultReason::InsufficientBytes => {
                        // If we've run out of bytes while searching, it means that the key was
                        // shorter than all the keys in the subtree rooted by
                        // the inner node. In a lexicographic ordering, given an equal prefix, the
                        // shorter sequence is always ordered before the longer sequence.

                        // SAFETY: Covered by function safety doc
                        let min_leaf_ptr = unsafe { minimum_unchecked(node_ptr) };
                        if is_start {
                            // In the context of a start bound, the search key being
                            // lexicographically shorter is easy to understand, since it will be
                            // ordered before the minimum key of the subtree in all cases.

                            min_leaf_ptr
                        } else {
                            // In the context of a end bound, the search key being lexicographically
                            // shorted means that none of the keys in this subtree are eligible to
                            // be in range. So we must find the minimum and then go one before that.

                            // SAFETY: Covered by function safety doc
                            unsafe {
                                let min_leaf = min_leaf_ptr.as_ref();
                                min_leaf.previous?
                            }
                        }
                    },
                    InnerNodeSearchResultReason::MissingChild => {
                        // If we stopped on an inner node because there was no corresponding child
                        // to continue the search, then it is possible that the key is anywhere
                        // within the subtree rooted by the inner node. In this case, we have to
                        // find the next largest or next smallest child and then find their minimum
                        // or maximum leaf node accordingly.
                        //
                        // There are a couple of baseline cases without considering the `is_start`
                        // bit yet. Imagine an array of child keys (with implicit pointers):
                        //
                        // ```text
                        //   Middle         Start           End
                        // |---|---|      |---|---|      |---|---|
                        // | 3 | 7 |      | 3 | 7 |      | 3 | 7 |
                        // |---|---|      |---|---|      |---|---|
                        //     ^          ^                      ^
                        //     5          1                      9
                        // ```
                        //
                        // Now consider start vs end bound:
                        //  - If we're in the "Middle" case, with `is_start == true`, then we want
                        //    the next largest key and `is_start == false` we want the next smallest
                        //    key. Both are accessible within this subtree, just selecting the
                        //    appropriate child neighbor and then going to the minimum or maximum
                        //    descendant.
                        //  - If we're in the "Start" case, then `is_start == true` is the same as
                        //    the "Middle" case. The `is_start == false` means we need to go the
                        //    portion of the tree just outside of this node, to the "left" (less).
                        fn access_closest_child<
                            const PREFIX_LEN: usize,
                            N: InnerNode<PREFIX_LEN>,
                        >(
                            inner_ptr: NodePtr<PREFIX_LEN, N>,
                            child_bounds: (Bound<u8>, Bound<u8>),
                            is_start: bool,
                        ) -> KeyByteAndChild<N::Key, N::Value, PREFIX_LEN> {
                            // SAFETY: Covered by outer function safety doc
                            let inner = unsafe { inner_ptr.as_ref() };
                            let mut child_it = inner.range(child_bounds);
                            if is_start {
                                child_it.next()
                            } else {
                                child_it.next_back()
                            }
                        }

                        // The close-side of the range is always excluded because the child that
                        // would have been equal was missing.
                        let child_bounds = if is_start {
                            (Bound::Excluded(key_bytes[current_depth]), Bound::Unbounded)
                        } else {
                            (Bound::Unbounded, Bound::Excluded(key_bytes[current_depth]))
                        };

                        let possible_next_child =
                            match_concrete_node_ptr!(match (node_ptr.to_node_ptr()) {
                                InnerNode(inner_ptr) => {
                                    access_closest_child(inner_ptr, child_bounds, is_start)
                                },
                                LeafNode(_leaf) => unreachable!(
                                    "This branch is unreachable because the \
                                     TerminatingNodeSearchResult had the value InnerNode"
                                ),
                            });

                        match (is_start, possible_next_child) {
                            (true, None) => {
                                // This is case "End" from above. If we're trying to get the start
                                // bound, but there is no next sibling, we should go to leaf after
                                // the maximum leaf of this subtree.

                                // SAFETY: Covered by function safety doc
                                unsafe {
                                    let max_leaf_ptr = maximum_unchecked(node_ptr);
                                    let max_leaf = max_leaf_ptr.as_ref();
                                    max_leaf.next?
                                }
                            },
                            (true, Some((_, next_child))) => {
                                // This is possibly case "Middle" from above. We select the smallest
                                // leaf of the next larger sibling.

                                // SAFETY: Covered by function safety doc
                                unsafe { minimum_unchecked(next_child) }
                            },
                            (false, None) => {
                                // This is case "Start" from above. If we're
                                // trying to get the end bound, but there is no
                                // previous sibling, we should go the leaf prior
                                // to the minimum leaf of this subtree.

                                // SAFETY: Covered by function safety doc
                                unsafe {
                                    let min_leaf_ptr = minimum_unchecked(node_ptr);
                                    let min_leaf = min_leaf_ptr.as_ref();
                                    min_leaf.previous?
                                }
                            },
                            (false, Some((_, prev_child))) => {
                                // This is possibly case "Middle" from above. We
                                // select the largest leaf of the next smaller
                                // sibling.

                                // SAFETY: Covered by function safety doc
                                unsafe { maximum_unchecked(prev_child) }
                            },
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
        pub struct $name<'a, K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global> {
            inner: RawIterator<K, V, PREFIX_LEN>,
            _tree: $tree_ty,
        }

        impl<'a, K: AsBytes, V, const PREFIX_LEN: usize, A: Allocator> $name<'a, K, V, PREFIX_LEN, A> {
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

                // Validation happens after the empty check so we can avoid panicking for invalid range
                // when the tree is empty. I believe this matches BTreeMap behavior.
                validate_range_bounds(&start_bound, &end_bound);

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

        impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> Iterator for $name<'a, K, V, PREFIX_LEN, A> {
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

implement_range_iter!(
    /// An iterator over a sub-range of entries in a [`TreeMap`].
    ///
    /// This struct is created by the [`range`][TreeMap::range] method on `TreeMap`.
    /// See its documentation for more details.
    struct Range {
        tree: &'a TreeMap<K, V, PREFIX_LEN, A>,
        item: (&'a K, &'a V),
        as_key_value_ref
    }
);

// SAFETY: This iterator holds a shared reference to the underlying `TreeMap`
// and thus can be moved across threads if the `TreeMap<K, V>: Sync`.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for Range<'_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

// SAFETY: This iterator has no interior mutability and can be shared across
// thread so long as the reference `TreeMap<K, V>` can as well.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for Range<'_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

implement_range_iter!(
    /// A mutable iterator over a sub-range of entries in a [`TreeMap`].
    ///
    /// This struct is created by the [`range_mut`][TreeMap::range_mut] method on `TreeMap`.
    /// See its documentation for more details.
    struct RangeMut {
        tree: &'a mut TreeMap<K, V, PREFIX_LEN, A>,
        item: (&'a K, &'a mut V),
        as_key_ref_value_mut
    }
);

// SAFETY: This iterator has a mutable reference to the underlying `TreeMap` and
// can be moved across threads if `&mut TreeMap<K, V>` is `Send`, which requires
// `TreeMap<K, V>` to be `Send` as well.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for RangeMut<'_, K, V, PREFIX_LEN, A>
where
    K: Send,
    V: Send,
    A: Send + Allocator,
{
}

// SAFETY: This iterator uses no interior mutability and can be shared across
// threads so long as `TreeMap<K, V>: Sync`.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for RangeMut<'_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

#[cfg(test)]
mod tests {
    use alloc::{boxed::Box, vec::Vec};

    use super::*;
    use crate::testing::{generate_key_with_prefix, swap, PrefixExpansion};

    #[test]
    fn iterators_are_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        fn range_is_send<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_send::<Range<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn range_is_sync<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_sync::<Range<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        range_is_send::<[u8; 3], usize, Global>();
        range_is_sync::<[u8; 3], usize, Global>();

        fn range_mut_is_send<'a, K: Send + 'a, V: Send + 'a, A: Send + Allocator + 'a>() {
            is_send::<RangeMut<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn range_mut_is_sync<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_sync::<RangeMut<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        range_mut_is_send::<[u8; 3], usize, Global>();
        range_mut_is_sync::<[u8; 3], usize, Global>();
    }

    fn fixture_tree() -> TreeMap<[u8; 3], usize> {
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

    #[test]
    fn lookup_on_tree_with_implicit_prefix_bytes() {
        let mut tree = TreeMap::<_, _, 0>::with_prefix_len();

        for (key, value) in generate_key_with_prefix(
            [3, 3, 3],
            [PrefixExpansion {
                base_index: 0,
                expanded_length: 4,
            }],
        )
        .enumerate()
        .map(swap)
        {
            let _ = tree.try_insert(key, value).unwrap();
        }

        assert_eq!(
            tree.range(Box::from([0u8, 0, 0, 0, 0, 0])..Box::from([0u8, 0, 0, 0, 0, 4]))
                .collect::<Vec<_>>(),
            &[
                (&[0, 0, 0, 0, 0, 0].into(), &0),
                (&[0, 0, 0, 0, 0, 1].into(), &1),
                (&[0, 0, 0, 0, 0, 2].into(), &2),
                (&[0, 0, 0, 0, 0, 3].into(), &3)
            ]
        );

        assert_eq!(
            tree.range(Box::from([0u8, 0])..Box::from([0u8, 0, 0, 0, 0, 4]))
                .collect::<Vec<_>>(),
            &[
                (&[0, 0, 0, 0, 0, 0].into(), &0),
                (&[0, 0, 0, 0, 0, 1].into(), &1),
                (&[0, 0, 0, 0, 0, 2].into(), &2),
                (&[0, 0, 0, 0, 0, 3].into(), &3)
            ]
        );
    }

    #[test]
    fn range_inclusive_end_past_all_node_keys() {
        // Regression test: when the end bound's key byte at a Node4/Node16 level
        // exceeds all child key bytes and no child is found (MissingChild), the
        // node's range() method was called with Included(byte > max_key), which
        // mapped Last(n) → Included(n) and caused an out-of-bounds panic on the
        // n-element initialized slice.

        let mut tree: TreeMap<u8, usize> = TreeMap::default();
        tree.try_insert(0x10u8, 1).unwrap();
        tree.try_insert(0x20u8, 2).unwrap();
        tree.try_insert(0x30u8, 3).unwrap();

        // End-bound first byte 0x50 > max child byte 0x30 at root → MissingChild
        // → inner.range((Unbounded, Included(0x50))) was previously OOB
        let result: Vec<_> = tree
            .range((
                core::ops::Bound::Unbounded,
                core::ops::Bound::Included(0x50u8),
            ))
            .map(|(k, v)| (*k, *v))
            .collect();
        assert_eq!(result, [(0x10u8, 1), (0x20u8, 2), (0x30u8, 3),]);
    }

    #[test]
    fn range_excluded_start_past_all_node_keys() {
        // Regression test: when the start bound's key byte at a Node4/Node16 level
        // exceeds all child key bytes and no child is found (MissingChild), the
        // node's range() method was called with Excluded(byte > max_key), which
        // mapped Last(n) → Excluded(n) and caused an out-of-bounds panic (slice
        // start at n+1 on an n-element slice).

        let mut tree: TreeMap<u8, usize> = TreeMap::default();
        tree.try_insert(0x10u8, 1).unwrap();
        tree.try_insert(0x20u8, 2).unwrap();
        tree.try_insert(0x30u8, 3).unwrap();

        // Start-bound first byte 0x50 > max child byte 0x30 at root → MissingChild
        // → inner.range((Excluded(0x50), Unbounded)) was previously OOB
        let result: Vec<_> = tree
            .range((
                core::ops::Bound::Excluded(0x50u8),
                core::ops::Bound::Unbounded,
            ))
            .collect();
        assert!(result.is_empty(), "expected empty range, got {result:?}");
    }

    #[test]
    fn range_excluded_empty_end_bound_is_empty() {
        // Regression test: Excluded(&[]) as an end bound should yield an empty
        // iterator because [] is the lexicographic minimum — no key is less than
        // the empty slice.  Previously find_leaf_pointer_for_bound hit the
        // (false, Equal) arm of PrefixMismatchOrInsufficientBytes and returned
        // maximum_unchecked(root), producing all entries instead of none.
        let mut tree: TreeMap<Box<[u8]>, u32> = TreeMap::new();
        for i in 0u8..=9 {
            tree.try_insert(Box::from([i]), i as u32).unwrap();
        }

        let result: Vec<_> = tree
            .range::<[u8], _>((Bound::Unbounded, Bound::Excluded([].as_ref())))
            .collect();
        assert!(result.is_empty(), "expected empty range, got {result:?}");
    }

    #[test]
    fn range_regression_missing_child_62c8b0067a82ea8bf3a296d73915e1c0b76359ae() {
        // [
        //     TryInsertMany(
        //         [
        //             59,
        //         ],
        //         7,
        //     ),
        //     TryInsertMany(
        //         [
        //             247,
        //         ],
        //         35,
        //     ),
        //     Range(
        //         Included(
        //             [
        //                 59,
        //                 59,
        //                 0,
        //             ],
        //         ),
        //         Unbounded,
        //     ),
        // ]
        let mut map = TreeMap::<Box<[u8]>, usize>::new();

        for first_subtree in 0..=7u8 {
            map.try_insert(Box::new([59, first_subtree]), map.len())
                .unwrap();
        }
        for second_subtree in 0..=35 {
            map.try_insert(Box::new([247, second_subtree]), map.len())
                .unwrap();
        }

        let contents = map
            .range((Bound::Included(Box::from([59u8, 59, 0])), Bound::Unbounded))
            .map(|(k, _)| k.clone())
            .collect::<Vec<_>>();

        assert_eq!(
            contents,
            (0..=35u8).map(|v| Box::from([247, v])).collect::<Vec<_>>()
        );
    }

    #[test]
    fn range_regression_prefix_mismatch_b91a7f054453649d83d175c6ca31635e311f03fa() {
        // [
        //     TryInsertMany(
        //         [
        //             151,
        //             93,
        //             151,
        //             151,
        //             151,
        //             151,
        //             215,
        //             151,
        //             255,
        //             255,
        //             151,
        //             255,
        //             255,
        //             247,
        //             0,
        //             3,
        //             16,
        //         ],
        //         91,
        //     ),
        //     Range(
        //         Included(
        //             [
        //                 255,
        //                 26,
        //             ],
        //         ),
        //         Unbounded,
        //     ),
        // ]

        let mut map = TreeMap::<Box<[u8]>, usize>::new();
        for k in 0..=91u8 {
            map.try_insert(
                Box::from([
                    151u8, 93, 151, 151, 151, 151, 215, 151, 255, 255, 151, 255, 255, 247, 0, 3,
                    16, k,
                ]),
                map.len(),
            )
            .unwrap();
        }

        let contents = map
            .range((Bound::Included(Box::from([255, 26])), Bound::Unbounded))
            // Make it easier to read, only unique part of key is last byte
            .map(|(k, _)| k[17])
            .collect::<Vec<_>>();

        // Results should be empty because `255, 26` is greater than the prefix
        assert_eq!(contents, &[]);
    }

    #[test]
    fn range_regression_excluded_0ef360aad5ebf9e3d5968d3ca6ba381ccb749cc8() {
        // [
        //     TryInsertMany(
        //         [
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //             255,
        //         ],
        //         225,
        //     ),
        //     Range(
        //         Excluded(
        //             [
        //                 225,
        //                 146,
        //                 225,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 251,
        //                 232,
        //                 2,
        //             ],
        //         ),
        //         Unbounded,
        //     ),
        // ]

        let mut map = TreeMap::<Box<[u8]>, usize>::new();
        for k in 0..=64 {
            map.try_insert(
                Box::from([
                    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
                    255, k,
                ]),
                map.len(),
            )
            .unwrap();
        }

        let contents = map
            .range((
                Bound::Excluded(Box::from([
                    225, 146, 225, 251, 251, 251, 251, 251, 251, 251, 251, 251, 251, 251, 251, 251,
                    232, 2,
                ])),
                Bound::Unbounded,
            ))
            // Make it easier to read, only unique part of key is last byte
            .map(|(k, _)| k[17])
            .collect::<Vec<_>>();

        // The range should contain all elements in the tree because the range start is
        // less than all the keys in the tree.
        assert_eq!(contents, (0..=64).collect::<Vec<_>>());
    }
}
