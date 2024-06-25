//! Trie node lookup and manipulation

use crate::{AsBytes, ConcreteNodePtr, InnerNode, NodePtr, OpaqueNodePtr};

mod insert;
pub(crate) use insert::*;

mod minmax;
pub(crate) use minmax::*;

mod lookup;
pub(crate) use lookup::*;

mod delete;
pub(crate) use delete::*;

/// Deallocate the given node and all children of the given node.
///
/// This will also deallocate the leaf nodes with their value type data.
///
/// # Safety
///  - This function must only be called once for this root node and all
///    descendants, otherwise a double-free could result.
pub unsafe fn deallocate_tree<K: AsBytes, V, const NUM_PREFIX_BYTES: usize>(
    root: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES>,
) {
    fn deallocate_inner_node<K: AsBytes, V, N, const NUM_PREFIX_BYTES: usize>(
        stack: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES>>,
        inner_ptr: NodePtr<NUM_PREFIX_BYTES, N>,
    ) where
        N: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V>,
    {
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
            let iter = inner_node.iter();
            stack.extend(iter.map(|(_, child)| child));
        }

        // SAFETY: The single call per node requirement is enforced by the safety
        // requirements on this function.
        drop(unsafe { NodePtr::deallocate_node_ptr(inner_ptr) });
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
                drop(unsafe { NodePtr::deallocate_node_ptr(inner) })
            },
        }
    }
}
