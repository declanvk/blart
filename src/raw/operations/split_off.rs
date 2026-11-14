use alloc::vec::Vec;
use core::{
    alloc::Allocator,
    cmp::Ordering,
    fmt,
    ops::{Bound, ControlFlow},
};

use crate::{
    AsBytes, OpaqueNodePtr,
    raw::{
        ConcreteInnerNodePtr, InnerNode, InnerNode4, InnerNode16, InnerNode48, InnerNodeCommon,
        InnerNodeDirect, InnerNodeType, LeafNode, NodePtr, PrefixMatch,
        match_concrete_inner_node_ptr, match_concrete_node_ptr,
        operations::{maximum_unchecked, minimum_unchecked},
    },
};

/// Split the tree rooted by `root` into two at the given `key_bytes`.
///
/// The keys less than `key_bytes` end up in one tree, and the keys greater than or equal to
/// `key_bytes` end up in the other.
///
/// The split happens in three phases:
///  1. Search for `key_bytes` from the root, recording every inner node on the path and which of
///     its children are to the left and right of the path (see [`collect_split_point_nodes`]). The
///     search stops at one of the following:
///     - a leaf, which goes to the left if its key is less than `key_bytes` and to the right
///       otherwise.
///     - an inner node whose prefix does not match `key_bytes`. The whole node goes to the left or
///       right depending on how its prefix compares to `key_bytes`.
///     - an inner node with no child for the next key byte, which is split at that key byte.
///  2. Cut the leaf linked list between the maximum leaf on the left and the minimum leaf on the
///     right. If one side is empty, return the tree unchanged instead.
///  3. Walk back up the path, splitting each inner node into a left and right node (see
///     [`split_ancestor`]).
///
/// Leaf nodes are never split, each one is moved whole to one of the two trees. When an inner node
/// is split, its allocation is reused for one side if the number of children on that side fits the
///  node type, otherwise a new node of the right size is allocated. If a side has only one child,
/// that level of the tree is collapsed into the child, by prepending the inner node's prefix and
/// key byte to the child's prefix. Inner nodes that are not reused are deallocated.
///
/// # Safety
///  - `root` must be the root of a well-formed tree, and every node of the tree must have been
///    allocated with `alloc`.
///  - This function requires exclusive access to the tree, no other operation may read or write any
///    node of the tree for the duration of this function.
///  - After this function returns, `root` must not be used except through the root pointers in the
///    returned [`SplitOffResult`]. For a [`SplitOffResult::NormalSplit`], some of the inner nodes
///    on the path to the split point have been modified or deallocated.
///
/// # Panics
///
/// This function calls [`AsBytes::as_bytes`] on keys in the tree, which may panic. Those calls all
/// happen before the tree is modified, so a panic leaves the tree unchanged.
pub unsafe fn split_off_unchecked<K: AsBytes, V, A: Allocator, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
    alloc: &A,
) -> SplitOffResult<K, V, PREFIX_LEN> {
    let CollectSplitPointResult { path, terminal } = unsafe {
        // SAFETY: There is no concurrent mutation of the tree, covered by the safety requirements
        // of this function
        collect_split_point_nodes(root, key_bytes)
    };

    // Find the leaves on either side of the split before making any further changes, since we can
    // figure out whether to return early based on these leaves.
    //
    // SAFETY: The tree has not been modified yet and there is no concurrent mutation, covered by
    // the safety requirements of this function
    let (max_left, min_right) = unsafe { find_split_boundary(&terminal) };
    let (max_left, min_right) = match (max_left, min_right) {
        (None, Some(_)) => {
            return SplitOffResult::OnlyGreaterThanOrEqual {
                greater_than_or_equal_root: root,
            };
        },
        (Some(_), None) => {
            return SplitOffResult::OnlyLessThan {
                less_than_root: root,
            };
        },
        (Some(max_left), Some(min_right)) => (max_left, min_right),
        (None, None) => unreachable!("the tree contains at least one leaf"),
    };

    // Cut the linked list between the two trees
    //
    // SAFETY: We have exclusive access to the tree, covered by the safety requirements of this
    // function. `max_left` and `min_right` are different leaves, and each mutable reference only
    // lasts for its own statement.
    unsafe {
        max_left.as_mut().next = None;
        min_right.as_mut().previous = None;
    }

    let (mut left, mut right) = match terminal {
        CollectSplitPointTerminal::Leaf {
            leaf_ptr,
            ordering_to_split_key,
        } => match ordering_to_split_key {
            Ordering::Less => (Some(leaf_ptr.to_opaque()), None),
            Ordering::Equal | Ordering::Greater => (None, Some(leaf_ptr.to_opaque())),
        },
        CollectSplitPointTerminal::InnerNodePrefixMismatch {
            inner_node,
            ordering_to_split_key,
        } => match ordering_to_split_key {
            Ordering::Less => (Some(inner_node.to_opaque()), None),
            Ordering::Equal | Ordering::Greater => (None, Some(inner_node.to_opaque())),
        },
        CollectSplitPointTerminal::InnerNodeMissingChild(inner_node_path_elem) => {
            // SAFETY: We have exclusive access to the tree and every node was allocated with
            // `alloc`, covered by the safety requirements of this function. The element was just
            // built by `collect_split_point_nodes` and the tree has not been restructured since
            // (only the leaf linked list was cut), so it satisfies the `InnerNodePathElem`
            // invariants. There is no child on the path, so no slot in the inner node is stale,
            // and the children are exactly `left_children` plus `right_children`.
            let InnerNodeSplit { left, right, pos } =
                unsafe { inner_node_path_elem.split(key_bytes, None, alloc) };

            // SAFETY: We have exclusive access to the tree. `split` puts each child of the inner
            // node on exactly one side, and the inner node itself was either reused for a `Many`
            // side or deallocated, so nothing else accesses a singleton child during this call.
            // `pos` came from a prefix match against `key_bytes`, so its prefix range is in
            // bounds.
            unsafe {
                (
                    left.into_opaque(key_bytes, &pos),
                    right.into_opaque(key_bytes, &pos),
                )
            }
        },
    };

    for elem in path.into_iter().rev() {
        // SAFETY: We have exclusive access to the tree and every node was allocated with `alloc`,
        // covered by the safety requirements of this function. `elem` was built by
        // `collect_split_point_nodes`, and its inner node has not been modified since, because
        // the path is processed from the deepest element up and each split only touches its own
        // inner node and the halves of its child. `left` and `right` are the halves of the path
        // child of `elem`: on the first iteration they come from the terminal, and afterwards
        // from splitting the element one level deeper, which is the path child of this one.
        (left, right) = unsafe { split_ancestor(key_bytes, left, right, elem, alloc) };
    }

    match (left, right) {
        (Some(less_than_root), Some(greater_than_or_equal_root)) => SplitOffResult::NormalSplit {
            less_than_root,
            less_than_root_max_leaf: max_left,
            greater_than_or_equal_root,
            greater_than_or_equal_min_leaf: min_right,
        },
        _ => unreachable!("both sides of the split must be non-empty"),
    }
}

/// The result of [`split_off_unchecked`].
pub enum SplitOffResult<K, V, const PREFIX_LEN: usize> {
    /// The tree had keys on both sides of the split, and was split into two trees.
    ///
    /// The leaf linked list was cut between `less_than_root_max_leaf` and
    /// `greater_than_or_equal_min_leaf`. The minimum leaf of the original tree is now the minimum
    /// leaf of the less than tree, and the maximum leaf of the original tree is now the maximum
    /// leaf of the greater than or equal tree.
    NormalSplit {
        /// The root of the tree with all keys less than the split key
        less_than_root: OpaqueNodePtr<K, V, PREFIX_LEN>,
        /// The maximum leaf of the less than tree
        less_than_root_max_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
        /// The root of the tree with all keys greater than or equal to the split key
        greater_than_or_equal_root: OpaqueNodePtr<K, V, PREFIX_LEN>,
        /// The minimum leaf of the greater than or equal tree
        greater_than_or_equal_min_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    },
    /// Every key in the tree is less than the split key, so the tree was not modified.
    OnlyLessThan {
        /// The root of the original tree
        less_than_root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    },
    /// Every key in the tree is greater than or equal to the split key, so the tree was not
    /// modified.
    OnlyGreaterThanOrEqual {
        /// The root of the original tree
        greater_than_or_equal_root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    },
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for SplitOffResult<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NormalSplit {
                less_than_root,
                less_than_root_max_leaf,
                greater_than_or_equal_root,
                greater_than_or_equal_min_leaf,
            } => f
                .debug_struct("NormalSplit")
                .field("less_than_root", less_than_root)
                .field("less_than_root_max_leaf", less_than_root_max_leaf)
                .field("greater_than_or_equal_root", greater_than_or_equal_root)
                .field(
                    "greater_than_or_equal_min_leaf",
                    greater_than_or_equal_min_leaf,
                )
                .finish(),
            Self::OnlyLessThan { less_than_root } => f
                .debug_struct("OnlyLessThan")
                .field("less_than_root", less_than_root)
                .finish(),
            Self::OnlyGreaterThanOrEqual {
                greater_than_or_equal_root,
            } => f
                .debug_struct("OnlyGreaterThanOrEqual")
                .field("greater_than_or_equal_root", greater_than_or_equal_root)
                .finish(),
        }
    }
}

/// Search for `key_bytes` from `root`, and collect the inner nodes on the path along with the node
/// where the search stopped.
///
/// For each inner node on the path, the children are partitioned into those with a key byte less
/// than the path's key byte (the left) and those with a greater key byte (the right). The child on
/// the path is in neither.
///
/// This function does not modify the tree.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation on `root` or any
///    child node of `root`.
unsafe fn collect_split_point_nodes<K: AsBytes, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
) -> CollectSplitPointResult<K, V, PREFIX_LEN> {
    /// Match the prefix of an inner node and look up the child for the next key byte. Returns the
    /// child to continue the search with, or the terminal if the search stops at this node.
    ///
    /// On return, `*current_depth` is still less than or equal to `key_bytes.len()`. When this
    /// returns [`ControlFlow::Continue`], `*current_depth` has advanced past the node's prefix and
    /// the key byte of the returned child.
    ///
    /// # Safety
    ///  - `inner_node_ptr` must point to a live inner node of type `N`, which is the root of a
    ///    well-formed subtree (every node reachable from it is live).
    ///  - This function cannot be called concurrently with any mutating operation on the node at
    ///    `inner_node_ptr` or any of its descendants.
    ///  - `*current_depth` must be less than or equal to `key_bytes.len()`.
    unsafe fn visit_inner_node<K, V, N, const PREFIX_LEN: usize>(
        inner_node_ptr: NodePtr<PREFIX_LEN, N>,
        key_bytes: &[u8],
        path: &mut Vec<InnerNodePathElem<K, V, PREFIX_LEN>>,
        current_depth: &mut usize,
    ) -> ControlFlow<CollectSplitPointTerminal<K, V, PREFIX_LEN>, OpaqueNodePtr<K, V, PREFIX_LEN>>
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
        K: AsBytes,
        NodePtr<PREFIX_LEN, N>: Into<ConcreteInnerNodePtr<K, V, PREFIX_LEN>>,
    {
        // SAFETY: `inner_node_ptr` points to a live node with no concurrent mutation, covered by
        // the safety requirements of this function. The reference does not outlive this function.
        let inner_node = unsafe { inner_node_ptr.as_ref() };

        let depth_at_prefix_start = *current_depth;

        // SAFETY: `depth_at_prefix_start <= key_bytes.len()`, covered by the safety requirements
        // of this function.
        match unsafe { inner_node.match_full_prefix(key_bytes, depth_at_prefix_start) } {
            Ok(PrefixMatch { matched_bytes }) => {
                // Since the prefix matched, advance the depth by the size of the prefix. On a
                // match, `matched_bytes` counts pairs zipped from the prefix and
                // `key_bytes[depth_at_prefix_start..]`, so the depth stays `<= key_bytes.len()`.
                *current_depth += matched_bytes;

                let next_key_fragment = if *current_depth < key_bytes.len() {
                    key_bytes[*current_depth]
                } else {
                    // The key has insufficient bytes, so it is a strict prefix of every key under
                    // this node. Shorter sequences sort first, so every key under this node is
                    // greater than the split key. See the `split_off_key_ends_before_node` test.
                    return ControlFlow::Break(
                        CollectSplitPointTerminal::InnerNodePrefixMismatch {
                            inner_node: inner_node_ptr.into(),
                            ordering_to_split_key: Ordering::Greater,
                        },
                    );
                };

                let child_lookup = inner_node.lookup_child(next_key_fragment);
                let left_children = inner_node.range(..next_key_fragment).collect();
                // Exclude the child at `next_key_fragment` from both sides, since it lies on the
                // path and will itself be split
                let right_children = inner_node
                    .range((Bound::Excluded(next_key_fragment), Bound::Unbounded))
                    .collect();

                let pos = InnerNodeKeyPosition {
                    depth_at_prefix_start,
                    prefix_length: matched_bytes,
                    next_key_fragment,
                };

                match child_lookup {
                    Some(child_ptr) => {
                        // Since the prefix matched and it found a child, advance the depth by 1
                        // more key byte. This branch is only reached when
                        // `*current_depth < key_bytes.len()`, so the depth stays
                        // `<= key_bytes.len()`.
                        *current_depth += 1;

                        path.push(InnerNodePathElem {
                            inner_node_ptr: inner_node_ptr.into(),
                            left_children,
                            right_children,
                            pos,
                        });
                        ControlFlow::Continue(child_ptr)
                    },
                    None => ControlFlow::Break(CollectSplitPointTerminal::InnerNodeMissingChild(
                        InnerNodePathElem {
                            inner_node_ptr: inner_node_ptr.into(),
                            left_children,
                            right_children,
                            pos,
                        },
                    )),
                }
            },
            Err(mismatch) => {
                ControlFlow::Break(CollectSplitPointTerminal::InnerNodePrefixMismatch {
                    inner_node: inner_node_ptr.into(),
                    ordering_to_split_key: mismatch.node_prefix_comparison_to_search_key_segment,
                })
            },
        }
    }

    let mut current_node = root;
    let mut path = Vec::new();
    let mut current_depth = 0;

    loop {
        let control = match_concrete_node_ptr!(match (current_node.to_node_ptr()) {
            InnerNode(inner_node_ptr) => {
                // SAFETY: `current_node` is either `root` or a child returned by a previous
                // visit, so it is a live node of the tree, and there is no concurrent mutation,
                // covered by the safety requirements of this function. `current_depth` starts at
                // 0, and each previous visit kept it `<= key_bytes.len()`.
                unsafe {
                    visit_inner_node(inner_node_ptr, key_bytes, &mut path, &mut current_depth)
                }
            },
            LeafNode(leaf_ptr) => {
                // SAFETY: There is no concurrent mutation of the tree, covered by the safety
                // requirements of this function. The reference does not outlive this block.
                let leaf_key = unsafe { leaf_ptr.as_key_ref() };
                // This call may panic, since it is user-provided, we just need to ensure that there
                // are no memory leaks and we don't leave the tree in an invalid state
                let leaf_key_bytes = leaf_key.as_bytes();
                let ordering_to_split_key = leaf_key_bytes.cmp(key_bytes);

                return CollectSplitPointResult {
                    path,
                    terminal: CollectSplitPointTerminal::Leaf {
                        leaf_ptr,
                        ordering_to_split_key,
                    },
                };
            },
        });

        current_node = match control {
            ControlFlow::Continue(next_node) => next_node,
            ControlFlow::Break(terminal) => return CollectSplitPointResult { path, terminal },
        };
    }
}

/// The result of [`collect_split_point_nodes`].
struct CollectSplitPointResult<K, V, const PREFIX_LEN: usize> {
    /// The inner nodes that the split key passed through, starting from the root. Each of these
    /// has a child on the path.
    path: Vec<InnerNodePathElem<K, V, PREFIX_LEN>>,
    /// The node where the search for the split key stopped
    terminal: CollectSplitPointTerminal<K, V, PREFIX_LEN>,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for CollectSplitPointResult<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CollectSplitPointResult")
            .field("path", &self.path)
            .field("terminal", &self.terminal)
            .finish()
    }
}

/// The node where the search for the split key stopped, and how it relates to the split key.
enum CollectSplitPointTerminal<K, V, const PREFIX_LEN: usize> {
    /// The search reached a leaf
    Leaf {
        leaf_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
        /// The ordering of the leaf's key compared to the split key
        ordering_to_split_key: Ordering,
    },
    /// The prefix of an inner node did not match the split key.
    ///
    /// This also covers the insufficient bytes case, since we could view it as a "mismatch" of
    /// length. In that case the `ordering_to_split_key` would always be `Ordering::Greater`
    /// because the split key is a strict prefix of every key in the node, and shorter
    /// sequences are always ordered before longer sequences in a lexicographic ordering.
    InnerNodePrefixMismatch {
        inner_node: ConcreteInnerNodePtr<K, V, PREFIX_LEN>,
        /// The ordering of every key under the inner node compared to the split key
        ordering_to_split_key: Ordering,
    },
    /// The prefix of an inner node matched, but the child lookup for the next key byte failed
    InnerNodeMissingChild(InnerNodePathElem<K, V, PREFIX_LEN>),
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for CollectSplitPointTerminal<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Leaf {
                leaf_ptr,
                ordering_to_split_key,
            } => f
                .debug_struct("Leaf")
                .field("leaf_ptr", leaf_ptr)
                .field("ordering_to_split_key", ordering_to_split_key)
                .finish(),
            Self::InnerNodePrefixMismatch {
                inner_node,
                ordering_to_split_key,
            } => f
                .debug_struct("InnerNodePrefixMismatch")
                .field("inner_node", inner_node)
                .field("ordering_to_split_key", ordering_to_split_key)
                .finish(),
            Self::InnerNodeMissingChild(elem) => {
                f.debug_tuple("InnerNodeMissingChild").field(elem).finish()
            },
        }
    }
}

/// Find the pair of adjacent leaves where the split happens, returning the maximum leaf less than
/// the split key and the minimum leaf greater than or equal to the split key.
///
/// Either leaf is `None` when there are no leaves on that side of the split.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation on the tree that
///    `terminal` was collected from.
unsafe fn find_split_boundary<K, V, const PREFIX_LEN: usize>(
    terminal: &CollectSplitPointTerminal<K, V, PREFIX_LEN>,
) -> SplitLeafNodes<K, V, PREFIX_LEN> {
    // SAFETY: Covered by the safety requirements of the containing function
    let from_max_left = |max_left: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>| {
        (Some(max_left), unsafe { max_left.as_ref() }.next)
    };
    // SAFETY: Covered by the safety requirements of the containing function
    let from_min_right = |min_right: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>| {
        (unsafe { min_right.as_ref() }.previous, Some(min_right))
    };

    match terminal {
        CollectSplitPointTerminal::Leaf {
            leaf_ptr,
            ordering_to_split_key,
        } => match ordering_to_split_key {
            Ordering::Less => from_max_left(*leaf_ptr),
            Ordering::Equal | Ordering::Greater => from_min_right(*leaf_ptr),
        },
        CollectSplitPointTerminal::InnerNodePrefixMismatch {
            inner_node,
            ordering_to_split_key,
        } => match ordering_to_split_key {
            // SAFETY: Covered by the safety requirements of the containing function
            Ordering::Less => from_max_left(unsafe { maximum_unchecked(inner_node.to_opaque()) }),
            Ordering::Equal | Ordering::Greater => {
                // SAFETY: Covered by the safety requirements of the containing function
                from_min_right(unsafe { minimum_unchecked(inner_node.to_opaque()) })
            },
        },
        CollectSplitPointTerminal::InnerNodeMissingChild(elem) => {
            if let Some((_, child)) = elem.left_children.last() {
                // SAFETY: Covered by the safety requirements of the containing function
                from_max_left(unsafe { maximum_unchecked(*child) })
            } else if let Some((_, child)) = elem.right_children.first() {
                // SAFETY: Covered by the safety requirements of the containing function
                from_min_right(unsafe { minimum_unchecked(*child) })
            } else {
                unreachable!("inner node must have at least one child")
            }
        },
    }
}

type SplitLeafNodes<K, V, const PREFIX_LEN: usize> = (
    Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>>,
    Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>>,
);

/// Split an inner node on the path, given the two halves of its child on the path.
///
/// `left_child` and `right_child` are the result of splitting the child on the path (the child at
/// `elem.pos.next_key_fragment`), and either may be `None` if that side is empty. Returns the left
/// and right halves of the inner node in `elem`, in the same form.
///
/// This works because every key under the path child has the same key byte at this inner node,
/// so both halves of the path child keep that key byte. Every left sibling has a smaller key byte,
/// so the left half goes after them. Every right sibling has a larger key byte, so the right half
/// goes before them. After that, the inner node is split the same way as one with no child on the
/// path, except that its slot for the path child is stale (see [`InnerNodePathElem::split`]).
///
/// # Safety
///  - The caller must have exclusive access to the inner node of `elem` and every node reachable
///    from it, and no other operation may read or write those nodes for the duration of this
///    function.
///  - Every node reachable from the inner node of `elem`, and every node in the subtrees of
///    `left_child` and `right_child`, must have been allocated with `alloc`.
///  - `elem` must satisfy the [`InnerNodePathElem`] invariants, and its inner node must have a
///    child at `elem.pos.next_key_fragment` (the path child). That is, `elem` was pushed onto the
///    path by [`collect_split_point_nodes`], and its inner node has not been modified since.
///  - `left_child` and `right_child` must be the result of splitting the path child. Each must
///    point to a live node. They must be different nodes, and neither may be in
///    `elem.left_children` or `elem.right_children`. Apart from the stale path slot in the inner
///    node of `elem`, no node outside their own subtrees may point to them or to any node in their
///    subtrees.
///  - `key_bytes` must be the same key bytes that `elem` was collected with.
///
/// After this function returns, the inner node of `elem` must not be used except through the
/// returned pointers, since it was either reused for one side or deallocated.
unsafe fn split_ancestor<K: AsBytes, V, const PREFIX_LEN: usize>(
    key_bytes: &[u8],
    left_child: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
    right_child: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
    mut elem: InnerNodePathElem<K, V, PREFIX_LEN>,
    alloc: &impl Allocator,
) -> SplitNodes<K, V, PREFIX_LEN> {
    let path_key_fragment = elem.pos.next_key_fragment;
    if let Some(left_child) = left_child {
        // Every left sibling has a smaller key byte, so this sorts last
        elem.left_children.push((path_key_fragment, left_child));
    }
    if let Some(right_child) = right_child {
        // Every right sibling has a larger key byte, so this sorts first
        // TODO(opt): avoid shifting the whole vector
        elem.right_children
            .insert(0, (path_key_fragment, right_child));
    }

    // SAFETY: Exclusive access and the allocator are covered by the safety requirements of this
    // function. `elem` satisfied the `InnerNodePathElem` invariants on entry, and adding at most
    // one half of the path child to each side at the path key byte preserves them: every left
    // sibling has a smaller key byte and every right sibling a larger one, so both vectors stay
    // strictly ascending. The inner node has a child at `path_key_fragment`, which is the stale
    // slot. The halves are live, not already in either vector, and not pointed to by any other
    // node except through that stale slot, covered by the safety requirements of this function.
    let InnerNodeSplit { left, right, pos } =
        unsafe { elem.split(key_bytes, Some(path_key_fragment), alloc) };

    // SAFETY: Exclusive access is covered by the safety requirements of this function. `split`
    // puts each child of the inner node, and each half of the path child, on exactly one side. The
    // inner node was either reused for a `Many` side or deallocated, so nothing else accesses a
    // singleton child during this call. `pos` came from a prefix match against `key_bytes`, so its
    // prefix range is in bounds.
    unsafe {
        (
            left.into_opaque(key_bytes, &pos),
            right.into_opaque(key_bytes, &pos),
        )
    }
}

type SplitNodes<K, V, const PREFIX_LEN: usize> = (
    Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
    Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
);

/// An inner node that the split key passed through, with its children partitioned around the
/// split key.
///
/// # Invariants
///
/// Let `node` be the inner node at `inner_node_ptr` and `b` be `pos.next_key_fragment`. The type
/// does not enforce these. [`collect_split_point_nodes`] establishes them, [`split_ancestor`]
/// preserves them, and [`InnerNodePathElem::split`] requires them:
///  - **Partition:** for each child of `node` at key byte `k`, if `k < b` then `(k, child)` appears
///    exactly once in `left_children`, and if `k > b` then it appears exactly once in
///    `right_children`. The only other entries allowed are at most one entry with key byte `b` in
///    each vector, which are halves of the path child added by [`split_ancestor`]. So every child
///    of `node` other than the one at `b` ends up on exactly one side, which is what makes it sound
///    to give each side ownership of its children.
///  - **Ordering:** `left_children` and `right_children` are each strictly ascending by key byte.
///  - **Prefix:** for the key bytes that this element was collected with,
///    `pos.depth_at_prefix_start + pos.prefix_length < key_bytes.len()`. The full prefix of `node`
///    equals `key_bytes[pos.depth_at_prefix_start..][..pos.prefix_length]`.
///  - `node` is live and has not been modified since the element was collected.
struct InnerNodePathElem<K, V, const PREFIX_LEN: usize> {
    /// Pointer to the inner node
    inner_node_ptr: ConcreteInnerNodePtr<K, V, PREFIX_LEN>,
    /// The children with a key byte less than `pos.next_key_fragment`, in order
    left_children: Vec<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>,
    /// The children with a key byte greater than `pos.next_key_fragment`, in order
    right_children: Vec<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>,
    /// The position of the inner node relative to the split key
    pos: InnerNodeKeyPosition,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for InnerNodePathElem<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNodePathElem")
            .field("inner_node_ptr", &self.inner_node_ptr)
            .field("left_children", &self.left_children)
            .field("right_children", &self.right_children)
            .field("pos", &self.pos)
            .finish()
    }
}

impl<K, V, const PREFIX_LEN: usize> InnerNodePathElem<K, V, PREFIX_LEN> {
    /// Split the inner node into a left side made from `left_children` and a right side made from
    /// `right_children`.
    ///
    /// Each side either reuses the original inner node, becomes a single child, or is a newly
    /// allocated inner node. Only one side can reuse the original node, and if neither does, it is
    /// deallocated.
    ///
    /// `stale_path_slot` is the key byte of the child on the path, if there is one. The original
    /// inner node still has a slot at that key byte pointing to the child as it was before it was
    /// split. That pointer is stale, the child may have been reused for one of its halves or
    /// deallocated. The halves of the path child (if any) are already in `left_children` and
    /// `right_children`, so the stale slot must not be copied over if the original node is reused.
    ///
    /// # Safety
    ///  - The caller must have exclusive access to the inner node at `self.inner_node_ptr` and
    ///    every node in `left_children` and `right_children`. No other operation may read or write
    ///    them for the duration of this function.
    ///  - The inner node must have been allocated with `alloc`.
    ///  - `self` must satisfy the [`InnerNodePathElem`] invariants, and `key_bytes` must be the
    ///    same key bytes that `self` was collected with.
    ///  - If `stale_path_slot` is `None`, `left_children` and `right_children` must have no entries
    ///    at `self.pos.next_key_fragment`, and the inner node must have no child there. If
    ///    `stale_path_slot` is `Some(b)`, then `b` must equal `self.pos.next_key_fragment`, and the
    ///    inner node must have a child at `b`.
    ///  - Every node in `left_children` and `right_children` must be live. The only node allowed to
    ///    point to them is the inner node, through its own slots or the stale path slot.
    ///
    /// After this function returns, `self.inner_node_ptr` must not be used except through the
    /// returned [`SplitSide::Many`], since the inner node was either reused for one side or
    /// deallocated. Each entry of `left_children` and `right_children` ends up on exactly one side.
    unsafe fn split(
        self,
        key_bytes: &[u8],
        stale_path_slot: Option<u8>,
        alloc: &impl Allocator,
    ) -> InnerNodeSplit<K, V, PREFIX_LEN> {
        /// Allocate the new inner node at the smallest size that will fit the given list of
        /// children, then insert those children.
        fn allocate_node_for_children<K, V, const PREFIX_LEN: usize>(
            key_bytes: &[u8],
            children: &Vec<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>,
            pos: &InnerNodeKeyPosition,
            alloc: &impl Allocator,
        ) -> ConcreteInnerNodePtr<K, V, PREFIX_LEN> {
            let [(first_byte, first_child), (second_byte, second_child), ..] = children.as_slice()
            else {
                unreachable!(
                    "children array should have at least two elements, had instead {} elements",
                    children.len()
                )
            };

            let children_rest = &children.as_slice()[2..];

            let prefix_bytes = &key_bytes
                [pos.depth_at_prefix_start..(pos.depth_at_prefix_start + pos.prefix_length)];

            macro_rules! build_inner_node {
                ($t:ident) => {{
                    let mut builder = $t::builder(prefix_bytes, pos.prefix_length)
                        .write_child(*first_byte, *first_child)
                        .write_child(*second_byte, *second_child);

                    for (byte, child) in children_rest {
                        builder = builder.write_child(*byte, *child);
                    }

                    NodePtr::allocate_node_ptr(builder.build(), alloc).into()
                }};
            }

            match InnerNodeType::inner_node_type_for(children.len()) {
                InnerNodeType::Node4 => {
                    build_inner_node!(InnerNode4)
                },
                InnerNodeType::Node16 => {
                    build_inner_node!(InnerNode16)
                },
                InnerNodeType::Node48 => {
                    build_inner_node!(InnerNode48)
                },
                InnerNodeType::Node256 => {
                    build_inner_node!(InnerNodeDirect)
                },
            }
        }

        /// Build one side of the split from `keep`, either by reusing the original inner node,
        /// collapsing to a single child, or allocating a new inner node.
        ///
        /// If the original inner node is reused, `*did_consume_parent` is set to `true`, and the
        /// node's children become exactly the entries of `keep`.
        ///
        /// # Safety
        ///  - If `*did_consume_parent` is `false`, `inner_node_ptr` must point to a live inner node
        ///    of type `N` that has not been reused for the other side. The caller must have
        ///    exclusive access to it, and no other operation may read or write it for the duration
        ///    of this function.
        ///  - `keep` and `discard` must be the two sides of an [`InnerNodePathElem`] that satisfies
        ///    its invariants for this inner node and `key_bytes`, and `stale_path_slot` must
        ///    satisfy the requirements of [`InnerNodePathElem::split`].
        ///  - Every node in `keep` must be live. The only node allowed to point to it is the inner
        ///    node, through its own slots or the stale path slot.
        #[expect(clippy::too_many_arguments)]
        unsafe fn split_side<K, V, const PREFIX_LEN: usize, N>(
            inner_node_ptr: NodePtr<PREFIX_LEN, N>,
            key_bytes: &[u8],
            keep: &Vec<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>,
            discard: &[(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)],
            stale_path_slot: Option<u8>,
            pos: &InnerNodeKeyPosition,
            did_consume_parent: &mut bool,
            alloc: &impl Allocator,
        ) -> SplitSide<K, V, PREFIX_LEN>
        where
            N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
            NodePtr<PREFIX_LEN, N>: Into<ConcreteInnerNodePtr<K, V, PREFIX_LEN>>,
        {
            if keep.is_empty() {
                SplitSide::Empty
            } else if !*did_consume_parent && N::TYPE.capacity_range().contains(&keep.len()) {
                *did_consume_parent = true;

                // we can re-use the original inner node and just remove the other side's children

                // SAFETY: `*did_consume_parent` was `false`, so `inner_node_ptr` points to a live
                // node that we have exclusive access to, covered by the safety requirements of this
                // function. The reference does not outlive this block.
                let inner_node = unsafe { inner_node_ptr.as_mut() };

                // The slot for the path child points to the child before it was split, so it is
                // stale no matter which side this is. Remove it first, so that it is gone even if
                // this side has no half of the path child, and so the loop below only has to
                // remove siblings.
                if let Some(stale_key_fragment) = stale_path_slot {
                    let removed = inner_node.remove_child(stale_key_fragment);
                    debug_assert!(removed.is_some());
                }

                // TODO(opt): optimize removal of many children
                for (key_fragment, _) in discard {
                    if Some(*key_fragment) == stale_path_slot {
                        // Already removed above
                        continue;
                    }

                    let removed = inner_node.remove_child(*key_fragment);
                    debug_assert!(removed.is_some());
                }

                // If this side has a half of the path child, write it back under the same key byte
                // in place of the stale pointer.
                if let Some(stale_key_fragment) = stale_path_slot
                    && let Some((_, child)) =
                        keep.iter().find(|(key, _)| *key == stale_key_fragment)
                {
                    inner_node.write_child(stale_key_fragment, *child);
                }

                SplitSide::Many {
                    finished: inner_node_ptr.into(),
                }
            } else if let [(key_byte, node_ptr)] = keep.as_slice() {
                SplitSide::Singleton {
                    key_byte: *key_byte,
                    node_ptr: *node_ptr,
                }
            } else {
                // we need to allocate a new inner node for these children, since the number of
                // children does not fit in the existing inner node.

                let new_inner_node = allocate_node_for_children(key_bytes, keep, pos, alloc);

                SplitSide::Many {
                    finished: new_inner_node,
                }
            }
        }

        /// Split the inner node at `inner_node_ptr`, see [`InnerNodePathElem::split`].
        ///
        /// # Safety
        ///  - Same as [`InnerNodePathElem::split`], where `inner_node_ptr`, `left_children`,
        ///    `right_children`, and `pos` are the fields of the [`InnerNodePathElem`], and
        ///    `inner_node_ptr` points to an inner node of type `N`.
        unsafe fn split_inner_node<K, V, const PREFIX_LEN: usize, N>(
            inner_node_ptr: NodePtr<PREFIX_LEN, N>,
            key_bytes: &[u8],
            left_children: Vec<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>,
            right_children: Vec<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>,
            stale_path_slot: Option<u8>,
            pos: InnerNodeKeyPosition,
            alloc: &impl Allocator,
        ) -> InnerNodeSplit<K, V, PREFIX_LEN>
        where
            N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
            NodePtr<PREFIX_LEN, N>: Into<ConcreteInnerNodePtr<K, V, PREFIX_LEN>>,
        {
            let mut did_consume_parent = false;
            // SAFETY: `did_consume_parent` is `false`, and the inner node is live and exclusively
            // accessed, covered by the safety requirements of this function. `left_children` and
            // `right_children` are the two sides of the element, and the left side's nodes are
            // live and only pointed to by the inner node.
            let left = unsafe {
                split_side(
                    inner_node_ptr,
                    key_bytes,
                    &left_children,
                    &right_children,
                    stale_path_slot,
                    &pos,
                    &mut did_consume_parent,
                    alloc,
                )
            };
            // SAFETY: If `did_consume_parent` is still `false`, the left side did not touch the
            // inner node (it built an `Empty`, a `Singleton`, or a new node from
            // `left_children`), so the inner node is still live and exclusively accessed. If it is
            // `true`, this call does not access the inner node. Either way, the left side never
            // accesses the nodes in `right_children`. The remaining requirements are the same as
            // for the left side.
            let right = unsafe {
                split_side(
                    inner_node_ptr,
                    key_bytes,
                    &right_children,
                    &left_children,
                    stale_path_slot,
                    &pos,
                    &mut did_consume_parent,
                    alloc,
                )
            };

            if !did_consume_parent {
                // If the original inner node was not used, then we need to deallocate it

                // SAFETY: Neither side reused the original inner node. By the partition invariant
                // of `InnerNodePathElem`, every child other than the stale path slot was moved to
                // one of the sides. So no returned side points to the inner node, and the caller
                // must not use `inner_node_ptr` again, which means it is only deallocated once.
                // The inner node was allocated with `alloc`, covered by the safety requirements of
                // this function.
                let _ = unsafe { NodePtr::deallocate_node_ptr(inner_node_ptr, alloc) };
            }

            InnerNodeSplit { left, right, pos }
        }

        match_concrete_inner_node_ptr!(match (self.inner_node_ptr) {
            // SAFETY: Covered by the safety requirements of this function, the arguments are the
            // fields of `self`, and `inner_node_ptr` has the concrete type of the inner node.
            InnerNode(inner_node_ptr) => unsafe {
                split_inner_node(
                    inner_node_ptr,
                    key_bytes,
                    self.left_children,
                    self.right_children,
                    stale_path_slot,
                    self.pos,
                    alloc,
                )
            },
        })
    }
}

/// The result of [`InnerNodePathElem::split`].
struct InnerNodeSplit<K, V, const PREFIX_LEN: usize> {
    left: SplitSide<K, V, PREFIX_LEN>,
    right: SplitSide<K, V, PREFIX_LEN>,
    pos: InnerNodeKeyPosition,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for InnerNodeSplit<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNodeSplit")
            .field("left", &self.left)
            .field("right", &self.right)
            .field("pos", &self.pos)
            .finish()
    }
}

/// One side of a split inner node.
enum SplitSide<K, V, const PREFIX_LEN: usize> {
    /// The side has no children
    Empty,
    /// The side has a single child, so the inner node level will be collapsed into it
    Singleton {
        key_byte: u8,
        node_ptr: OpaqueNodePtr<K, V, PREFIX_LEN>,
    },
    /// The side has enough children to need an inner node, either the reused original or a new one
    Many {
        finished: ConcreteInnerNodePtr<K, V, PREFIX_LEN>,
    },
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for SplitSide<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => f.write_str("Empty"),
            Self::Singleton { key_byte, node_ptr } => f
                .debug_struct("Singleton")
                .field("key_byte", key_byte)
                .field("node_ptr", node_ptr)
                .finish(),
            Self::Many { finished } => f.debug_struct("Many").field("finished", finished).finish(),
        }
    }
}

/// This struct represents the position of an inner node with respect to the split key.
#[derive(Debug, Copy, Clone)]
struct InnerNodeKeyPosition {
    /// Position in split key matching the start of the inner node prefix
    depth_at_prefix_start: usize,
    /// The length of the inner node prefix
    prefix_length: usize,
    /// The key byte corresponding to the next child in the split path
    next_key_fragment: u8,
}

impl<K, V, const PREFIX_LEN: usize> SplitSide<K, V, PREFIX_LEN> {
    /// Convert this split result into the node pointer that should replace the original inner
    /// node, collapsing a [`Singleton`][Self::Singleton] into its parent's position.
    ///
    /// For a [`Singleton`][Self::Singleton] child that is an inner node, its prefix is rewritten
    /// to be the parent's prefix, then `key_byte`, then its old prefix. The returned pointer takes
    /// the place of the original inner node, and the caller is responsible for linking it into
    /// exactly one parent (or using it as a root).
    ///
    /// # Safety
    ///  - For a [`Singleton`][Self::Singleton], `node_ptr` must point to a live node. For the
    ///    duration of this function, the node's memory must not be accessed (read or written)
    ///    through any other pointer, as required by [`OpaqueNodePtr::header_mut`].
    ///  - `pos` must be the position of the original inner node, from a prefix match against
    ///    `key_bytes`. So `pos.depth_at_prefix_start + pos.prefix_length <= key_bytes.len()`, and
    ///    that range of `key_bytes` is the full prefix of the original inner node.
    unsafe fn into_opaque(
        self,
        key_bytes: &[u8],
        pos: &InnerNodeKeyPosition,
    ) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        match self {
            SplitSide::Empty => None,
            SplitSide::Singleton { key_byte, node_ptr } => {
                // SAFETY: `node_ptr` is live and not accessed through any other pointer during
                // this function, covered by the safety requirements of this function. The
                // reference only lasts for the scope of this `if` block.
                if let Some(child_header) = unsafe { node_ptr.header_mut() } {
                    // The removed node's prefix matched the search key, so its full prefix (even
                    // past `PREFIX_LEN`) can be read from `key_bytes`.
                    let parent_prefix = &key_bytes[pos.depth_at_prefix_start
                        ..(pos.depth_at_prefix_start + pos.prefix_length)];

                    let (old_prefix, old_len, old_capped_len) = child_header.clear_prefix();
                    child_header.push_prefix(parent_prefix, pos.prefix_length);
                    child_header.push_prefix(&[key_byte], 1);
                    child_header.push_prefix(&old_prefix[..old_capped_len], old_len);
                }
                // the else case here is that the child does not have a header, and is a leaf

                Some(node_ptr)
            },
            SplitSide::Many { finished } => Some(finished.to_opaque()),
        }
    }
}

#[cfg(test)]
mod tests;
