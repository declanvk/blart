//! Trie node lookup and manipulation

use crate::{ConcreteNodePtr, InnerNode, NodePtr, OpaqueNodePtr};

mod insert;
pub use insert::*;

mod minmax;
pub use minmax::*;

mod lookup;
pub use lookup::*;

mod iterator;
pub use iterator::*;

mod delete;
pub use delete::*;

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
