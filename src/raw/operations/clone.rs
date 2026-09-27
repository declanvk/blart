//! This module contains the implementation of `clone()` for the trie.

use alloc::vec::Vec;

use crate::{
    allocator::Allocator,
    raw::{
        deallocate_tree, match_concrete_inner_node_ptr, match_concrete_node_ptr,
        ConcreteInnerNodePtr, ConcreteNodePtr, InnerNode, InnerNodeCommon, LeafNode, Node, NodePtr,
        OpaqueNodePtr,
    },
    AsBytes,
};

/// The result of cloning a trie
#[derive(Debug)]
pub struct CloneResult<K, V, const PREFIX_LEN: usize> {
    /// The new root node of the trie
    pub root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    /// The first leaf in the trie, aka the leaf with the minimum key
    pub min_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    /// The last leaf in the trie, aka the leaf with the maximum key
    pub max_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
}

/// Drop guard that deallocates a partially-cloned trie if a user-provided
/// `Clone` implementation (for `K`, `V`, or a node header) panics partway
/// through [`clone_unchecked`].
struct PartialCloneGuard<'a, K, V, A: Allocator, const PREFIX_LEN: usize> {
    /// Root of the partially-built new trie, or `None` if no node has been
    /// allocated yet.
    new_root_node: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
    /// The allocator that every node of the new trie was allocated with.
    alloc: &'a A,
}

impl<K, V, A: Allocator, const PREFIX_LEN: usize> PartialCloneGuard<'_, K, V, A, PREFIX_LEN> {
    fn into_root(mut self) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        self.new_root_node.take()
    }
}

impl<K, V, A: Allocator, const PREFIX_LEN: usize> Drop
    for PartialCloneGuard<'_, K, V, A, PREFIX_LEN>
{
    fn drop(&mut self) {
        if let Some(root) = self.new_root_node {
            // SAFETY:
            //  - This guard is the sole owner of the partially-built new trie, so this is the only
            //    call to `deallocate_tree` for these nodes; there is no double-free.
            //  - The new trie is not shared with any other thread and no references into it are
            //    live at this point, so there is no concurrent read and no use-after-free.
            //  - `alloc` is the same allocator that every node of the new trie was allocated with.
            //  - Every child pointer written into the partial trie points to a fully allocated
            //    node, so the traversal only ever visits valid nodes.
            unsafe {
                let _ = deallocate_tree(root, self.alloc);
            }
        }
    }
}

/// Clone the given trie and all the key-values paired contained.
///
/// This function does not use recursion to clone, so it should not cause stack
/// overflow when cloning a deep trie.
///
/// # Safety
///
/// This function can only be called while there are no mutable references to
/// any of the nodes in this trie.
pub unsafe fn clone_unchecked<
    K: Clone + AsBytes,
    V: Clone,
    A: Allocator,
    const PREFIX_LEN: usize,
>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    alloc: &A,
) -> CloneResult<K, V, PREFIX_LEN> {
    /// Update the current parent node with the newly cloned child, inserting it
    /// at the given key byte.
    ///
    /// If the parent is finished, meaning it has the expected number of
    /// children, this function pops that node off the unfinished stack.
    ///
    /// This function also updates the "new root node", which is inferred by
    /// recording the node that is passed when the unfinished stack is empty.
    ///
    /// # Safety
    ///
    /// This function can only be called while there are no other mutable
    /// references to the nodes of the cloned (in-progress) trie
    unsafe fn update_parent<N, K, V, const PREFIX_LEN: usize>(
        unfinished_nodes_stack: &mut Vec<(usize, ConcreteInnerNodePtr<K, V, PREFIX_LEN>)>,
        new_root_node: &mut Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
        key_byte: u8,
        new_node_ptr: NodePtr<PREFIX_LEN, N>,
    ) where
        N: Node<PREFIX_LEN, Key = K, Value = V>,
    {
        let Some((expected_num_children, parent)) = unfinished_nodes_stack.last() else {
            debug_assert!(
                new_root_node.is_none(),
                "First cloned node [{new_root_node:?}] is present while unfinished node stack is \
                 empty",
            );
            // We know this is the root node since it has no parent
            *new_root_node = Some(new_node_ptr.to_opaque());
            return;
        };

        let updated_num_children = match_concrete_inner_node_ptr!(match (parent) {
            InnerNode(inner_ptr) => {
                // SAFETY: Covered by function safety doc AND the lifetime of this mutable
                // reference is scoped to this block, and does not escape
                let inner = unsafe { inner_ptr.as_mut() };
                inner.write_child(key_byte, new_node_ptr.to_opaque());
                inner.header().num_children()
            },
        });

        debug_assert!(
            updated_num_children <= *expected_num_children,
            "should never add more [{updated_num_children}] than the expected number of children \
             [{expected_num_children}]"
        );
        if updated_num_children == *expected_num_children {
            // This inner node is finished, all the children have been added
            let _ = unfinished_nodes_stack.pop().expect("last was Some");
        }
    }

    /// This function starts cloning the inner node, and updates the various
    /// stacks so that the new node will be updated as tree traversal continues.
    ///
    /// # Safety
    ///
    ///  - This function can only be called while there are no mutable references to any of the
    ///    nodes in the trie referenced by `inner_ptr`.
    ///  - Additionally, there must not be any other mutable references to nodes in the
    ///    `unfinished_nodes_stack` stack.
    unsafe fn clone_inner_node<N, K, V, A, const PREFIX_LEN: usize>(
        unfinished_nodes_stack: &mut Vec<(usize, ConcreteInnerNodePtr<K, V, PREFIX_LEN>)>,
        dfs_stack: &mut Vec<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>,
        new_root_node: &mut Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
        key_byte: u8,
        inner_ptr: NodePtr<PREFIX_LEN, N>,
        alloc: &A,
    ) where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
        ConcreteInnerNodePtr<K, V, PREFIX_LEN>: From<NodePtr<PREFIX_LEN, N>>,
        A: Allocator,
    {
        // SAFETY: Covered by function safety comment
        let inner = unsafe { inner_ptr.as_ref() };

        // We add the node children in reverse order so that the first child lands on
        // the top of the stack. That ensures we iterate DFS and visit the nodes
        // in-order, not reversed
        dfs_stack.extend(inner.iter().rev());

        let mut header = inner.header().clone();
        header.reset_num_children();
        let new_node = N::from_header(header);
        // At this point the header records 0 children, but has a copy of the prefix
        // from the original node There are no child pointers in the node

        let new_node_ptr = NodePtr::allocate_node_ptr(new_node, alloc);

        // SAFETY: Covered by function safety doc, since there are no other mutable
        // references to nodes in the `unfinished_nodes_stack` stack.
        unsafe {
            update_parent(
                unfinished_nodes_stack,
                new_root_node,
                key_byte,
                new_node_ptr,
            )
        };

        // Get the expected number of children from the original header
        let expected_num_children = inner.header().num_children();
        unfinished_nodes_stack.push((
            expected_num_children,
            ConcreteInnerNodePtr::from(new_node_ptr),
        ));
    }

    // (expected number of children, Pointer to inner node)
    let mut unfinished_nodes_stack: Vec<(usize, ConcreteInnerNodePtr<K, V, PREFIX_LEN>)> =
        Vec::new();
    // (Key byte of this node, node pointer)
    let mut dfs_stack: Vec<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)> = Vec::new();

    // Guard deallocates partial root on unwinding
    let mut guard = PartialCloneGuard {
        new_root_node: None,
        alloc,
    };
    let mut first_leaf: Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>> = None;
    let mut previous_leaf: Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>> = None;

    // We're okay to fabricate a key_byte for the root, since it will never be
    // inserted into a parent node
    dfs_stack.push((u8::MAX, root));

    while let Some((key_byte, current_ptr)) = dfs_stack.pop() {
        match_concrete_node_ptr!(match (current_ptr.to_node_ptr()) {
            InnerNode(inner_ptr) => unsafe {
                // SAFETY: The `clone_unchecked` safety comment covers other mutable references
                // to the original trie, and we guarantee here there are no mutable references
                // to nodes in the `unfinished_node_stack`
                clone_inner_node(
                    &mut unfinished_nodes_stack,
                    &mut dfs_stack,
                    &mut guard.new_root_node,
                    key_byte,
                    inner_ptr,
                    alloc,
                );
            },
            LeafNode(leaf_ptr) => {
                // SAFETY: The `clone_unchecked` safety comment covers other mutable references
                // to the original trie
                let leaf = unsafe { leaf_ptr.as_ref() };

                let new_leaf = leaf.clone_without_siblings();
                let new_leaf_ptr = NodePtr::allocate_node_ptr(new_leaf, alloc);
                if let Some(previous_ptr) = previous_leaf {
                    // SAFETY: The `clone_unchecked` safety comment covers other mutable references
                    // to the original trie
                    unsafe { LeafNode::insert_after(new_leaf_ptr, previous_ptr) };
                }
                previous_leaf = Some(new_leaf_ptr);
                let _ = first_leaf.get_or_insert(new_leaf_ptr);

                // SAFETY: There are no mutable references to any nodes in the
                // `unfinished_nodes_stack`
                unsafe {
                    update_parent(
                        &mut unfinished_nodes_stack,
                        &mut guard.new_root_node,
                        key_byte,
                        new_leaf_ptr,
                    )
                };
            },
        });
    }

    assert!(
        unfinished_nodes_stack.is_empty(),
        "The list of unfinished nodes must be empty when exiting the loop"
    );

    let new_root_node = guard.into_root();

    CloneResult {
        root: new_root_node.expect("there should be at least one cloned node"),
        min_leaf: first_leaf.expect("should visit at least one leaf in a non-empty trie"),
        max_leaf: previous_leaf.expect("should visit at least one leaf in a non-empty trie"),
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use alloc::boxed::Box;
    use core::fmt;

    use super::*;
    use crate::{
        testing::{
            generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, swap,
            PrefixExpansion,
        },
        visitor::WellFormedChecker,
        TreeMap,
    };

    #[track_caller]
    fn check<K: AsBytes + Clone + PartialEq + fmt::Debug>(keys: impl IntoIterator<Item = K>) {
        let mut tree = TreeMap::new();
        for (key, value) in keys.into_iter().enumerate().map(swap) {
            tree.try_insert(key, value).unwrap();
        }

        let new_tree = tree.clone();

        for (key, expected_value) in &tree {
            assert_eq!(tree.get(key).unwrap(), expected_value);
        }

        assert_eq!(new_tree.len(), tree.len());
        assert_eq!(new_tree, tree);

        let _ = WellFormedChecker::check(&new_tree).expect("tree should be well-formed");
    }

    #[test]
    fn clone_small_trees() {
        check([[0u8, 0], [171, 171], [65, 229]]);
        check(generate_key_fixed_length(if cfg!(miri) {
            [3; 2]
        } else {
            [17; 2]
        }));
        check(generate_keys_skewed(if cfg!(miri) { 16 } else { 127 }));
    }

    #[test]
    fn clone_empty_tree() {
        check::<Box<[u8]>>([])
    }

    #[test]
    fn clone_singleton_tree() {
        check([[0, 0, 0, 0, 0]])
    }

    #[test]
    fn clone_tree_with_prefixes() {
        check(generate_key_with_prefix(
            [2; 3],
            [PrefixExpansion {
                base_index: 0,
                expanded_length: 3,
            }],
        ))
    }

    #[test]
    fn clone_panicking_value_does_not_leak() {
        use std::{
            panic::{catch_unwind, AssertUnwindSafe},
            sync::atomic::{AtomicUsize, Ordering},
        };

        static REMAINING_CLONES: AtomicUsize = AtomicUsize::new(0);

        #[derive(PartialEq, Eq, Debug)]
        struct PanicAfter(u32);

        impl Clone for PanicAfter {
            fn clone(&self) -> Self {
                let left = REMAINING_CLONES.fetch_sub(1, Ordering::Relaxed);
                assert!(left > 0, "boom: PanicAfter cloned too many times");
                PanicAfter(self.0)
            }
        }

        let mut tree: TreeMap<[u8; 2], PanicAfter> = TreeMap::new();
        tree.try_insert([0, 0], PanicAfter(0)).unwrap();
        for i in 1..=16u8 {
            tree.try_insert([1, i], PanicAfter(i.into())).unwrap();
        }

        // At this point the tree should be something like:
        // ```
        //         node4
        //         |   |
        //         0   node16
        //             | .. |
        //             1 - 16
        // ```
        //
        // Setting the number of remaining clones to 4 means that the first leaf is cloned and we
        // have two levels of partially constructed leaf nodes before the unwinding starts. I think
        // this should be sufficiently complicated and will exercise the deallocation with two
        // partial inner nodes of different kinds.
        REMAINING_CLONES.store(4, Ordering::Relaxed);

        let result = catch_unwind(AssertUnwindSafe(|| {
            let _ = tree.clone();
        }));
        assert!(
            result.is_err(),
            "clone should have unwound when the value `Clone` panicked"
        );

        assert_eq!(tree.get(&[0, 0]), Some(&PanicAfter(0)));
        for i in 1..=16u8 {
            assert_eq!(tree.get(&[1, i]), Some(&PanicAfter(i.into())));
        }
    }
}
