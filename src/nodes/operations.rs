//! Trie node lookup and manipulation

use crate::{ConcreteNodePtr, InnerNode, LeafNode, NodePtr, OpaqueNodePtr};

mod insert;
pub use insert::*;

mod minmax;
pub use minmax::*;

mod lookup;

mod iterator;
pub use iterator::*;

/// Search in the given tree for the value stored with the given key.
///
/// # Safety
///
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
pub unsafe fn search_unchecked<V>(
    root: OpaqueNodePtr<V>,
    key: &[u8],
) -> Option<NodePtr<LeafNode<V>>> {
    let lookup::InsertSearchResult { insert_type, .. } =
        lookup::search_for_insert_point(root, key).ok()?;

    match insert_type {
        lookup::InsertSearchResultType::SplitLeaf { leaf_node_ptr } => {
            let leaf_node = leaf_node_ptr.read();

            // Specifically we are matching the leaf node stored key against the full search
            // key to confirm that it is the right value.
            if leaf_node.matches_key(key) {
                Some(leaf_node_ptr)
            } else {
                None
            }
        },
        _ => None,
    }
}

/// Deallocate the given node and all children of the given node.
///
/// This will also deallocate the leaf nodes with their value type data.
///
/// # Safety
///
///  - This function must only be called once for this root node and all
///    descendants, otherwise a double-free could result.
pub unsafe fn deallocate_tree<V>(root: OpaqueNodePtr<V>) {
    fn deallocate_inner_node<V, N: InnerNode<Value = V>>(
        stack: &mut Vec<OpaqueNodePtr<V>>,
        inner_ptr: NodePtr<N>,
    ) {
        {
            // SAFETY: The scope of this reference is bounded and we enforce that no
            // mutation of the reference memory takes place within the lifetime. The
            // deallocation of the node happens outside of this block, after the lifetime
            // ends.
            let inner_node = unsafe { inner_ptr.as_ref() };
            // SAFETY: This iterator only lives for this block, a subset of the shared
            // lifetime of the `inner_node` variable. By the safety requirements of the
            // `deallocate_tree` function, no other mutation of this node can happen while
            // this iterator is live.
            let iter = unsafe { inner_node.iter() };
            stack.extend(iter.map(|(_, child)| child));
        }
        // SAFETY: The single call per node requirement is enforced by the safety
        // requirements on this function.
        unsafe { NodePtr::deallocate_node(inner_ptr) }
    }

    let mut stack = Vec::new();

    stack.push(root);

    while let Some(next_node_ptr) = stack.pop() {
        match next_node_ptr.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => deallocate_inner_node(&mut stack, inner_ptr),
            ConcreteNodePtr::Node16(inner_ptr) => deallocate_inner_node(&mut stack, inner_ptr),
            ConcreteNodePtr::Node48(inner_ptr) => deallocate_inner_node(&mut stack, inner_ptr),
            ConcreteNodePtr::Node256(inner_ptr) => deallocate_inner_node(&mut stack, inner_ptr),
            ConcreteNodePtr::LeafNode(inner) => {
                // SAFETY: The single call per node requirement is enforced by the safety
                // requirements on this function.
                unsafe { NodePtr::deallocate_node(inner) }
            },
        }
    }
}
