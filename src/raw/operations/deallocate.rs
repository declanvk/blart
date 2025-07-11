use crate::{
    allocator::Allocator,
    raw::{ConcreteNodePtr, InnerNode, LeafNode, NodePtr, OpaqueNodePtr, RawIterator},
};
use alloc::vec::Vec;

/// Deallocate all the leaf nodes in the linked list starting that are within
/// the given iterator.
///
/// # Safety
///  - This function must only be called once for this `start` node and all
///    following leaf nodes in the linked list, otherwise a double-free could
///    result.
///  - This function should not be called concurrently with any read of the
///    tree, otherwise it could result in a use-after-free.
///  - `alloc` must be the same allocator which was used to allocate all the
///    leaves of the tree.
pub unsafe fn deallocate_leaves<K, V, const PREFIX_LEN: usize, A: Allocator>(
    mut leaf_range: RawIterator<K, V, PREFIX_LEN>,
    alloc: &A,
) {
    // SAFETY: Covered by function safety doc
    while let Some(leaf_ptr) = unsafe { leaf_range.next() } {
        // SAFETY: Covered by function safety doc
        let _ = unsafe { NodePtr::deallocate_node_ptr(leaf_ptr, alloc) };
    }
}

/// Deallocate the given node and all children of the given node except for
/// leaf nodes.
///
/// # Safety
///  - This function must only be called once for this root node and all
///    descendants, otherwise a double-free could result.
///  - This function should not be called concurrently with any read of the
///    tree, otherwise it could result in a use-after-free.
///  - `alloc` must be the same allocator which was used to allocate all the
///    inner nodes of the tree.
pub unsafe fn deallocate_tree_non_leaves<K, V, const PREFIX_LEN: usize, A: Allocator>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    alloc: &A,
) {
    fn not_leaf<K, V, const PREFIX_LEN: usize>(node: &OpaqueNodePtr<K, V, PREFIX_LEN>) -> bool {
        !node.is::<LeafNode<K, V, PREFIX_LEN>>()
    }

    if root.is::<LeafNode<K, V, PREFIX_LEN>>() {
        return;
    }

    let mut stack = Vec::new();

    stack.push(root);

    while let Some(next_node_ptr) = stack.pop() {
        match next_node_ptr.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: Covered by function safety doc
                deallocate_inner_node(&mut stack, inner_ptr, not_leaf, alloc)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: Covered by function safety doc
                deallocate_inner_node(&mut stack, inner_ptr, not_leaf, alloc)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: Covered by function safety doc
                deallocate_inner_node(&mut stack, inner_ptr, not_leaf, alloc)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: Covered by function safety doc
                deallocate_inner_node(&mut stack, inner_ptr, not_leaf, alloc)
            },
            ConcreteNodePtr::LeafNode(_) => {
                unreachable!("should never encounter a leaf node")
            },
        }
    }
}

/// Deallocate the given node and all children of the given node.
///
/// This will also deallocate the leaf nodes with their value type data.
/// This function returns the amount of leaf nodes deallocated.
///
/// # Safety
///  - This function must only be called once for this root node and all
///    descendants, otherwise a double-free could result.
///  - This function should not be called concurrently with any read of the
///    tree, otherwise it could result in a use-after-free.
///  - `alloc` must be the same allocator which was used to allocate all the
///    nodes of the tree.
pub unsafe fn deallocate_tree<K, V, const PREFIX_LEN: usize, A: Allocator>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    alloc: &A,
) -> usize {
    fn accept_all<K, V, const PREFIX_LEN: usize>(_: &OpaqueNodePtr<K, V, PREFIX_LEN>) -> bool {
        true
    }

    let mut count = 0;
    let mut stack = Vec::new();

    stack.push(root);

    while let Some(next_node_ptr) = stack.pop() {
        match next_node_ptr.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: Covered by function safety doc
                deallocate_inner_node(&mut stack, inner_ptr, accept_all, alloc)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: Covered by function safety doc
                deallocate_inner_node(&mut stack, inner_ptr, accept_all, alloc)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: Covered by function safety doc
                deallocate_inner_node(&mut stack, inner_ptr, accept_all, alloc)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: Covered by function safety doc
                deallocate_inner_node(&mut stack, inner_ptr, accept_all, alloc)
            },
            ConcreteNodePtr::LeafNode(inner) => {
                // SAFETY: The single call per node requirement is enforced by the safety
                // requirements on this function.
                drop(unsafe { NodePtr::deallocate_node_ptr(inner, alloc) });
                count += 1;
            },
        }
    }
    count
}

/// This function will read an [`InnerNode`] and place all children that
/// satisfy the `filter_children` predicate on the `stack`. Then it will
/// deallocate the given [`InnerNode`].
///
/// # Safety
///  - This function must only be called once for this inner node
///  - This function cannot be called concurrently with any read of modification
///    of the trie.
unsafe fn deallocate_inner_node<K, V, N, A: Allocator, const PREFIX_LEN: usize>(
    stack: &mut Vec<OpaqueNodePtr<K, V, PREFIX_LEN>>,
    inner_ptr: NodePtr<PREFIX_LEN, N>,
    filter_children: for<'a> fn(&'a OpaqueNodePtr<K, V, PREFIX_LEN>) -> bool,
    alloc: &A,
) where
    N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
{
    {
        // SAFETY: The scope of this reference is bounded and we enforce that no
        // mutation of the reference memory takes place within the lifetime. The
        // deallocation of the node happens outside of this block, after the lifetime
        // ends.
        let inner_node = unsafe { inner_ptr.as_ref() };

        // SAFETY: This iterator only lives for this block, a subset of the shared
        // lifetime of the `inner_node` variable. By the safety requirements of the
        // `deallocate_inner_node` function, no other mutation of this node can happen
        // while this iterator is live.
        let iter = inner_node.iter();
        stack.extend(iter.map(|(_, child)| child).filter(filter_children));
    }

    // SAFETY: The single call per node requirement is enforced by the safety
    // requirements on this function.
    drop(unsafe { NodePtr::deallocate_node_ptr(inner_ptr, alloc) });
}
