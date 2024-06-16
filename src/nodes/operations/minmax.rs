use crate::{AsBytes, ConcreteNodePtr, InnerNode, LeafNode, NodeHeader, NodePtr, OpaqueNodePtr};

/// Search for the leaf with the minimum key, by lexicographic ordering.
///
/// # Safety
///
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
///
/// # Panics
///
///  - Panics if the tree at the root node is not well-formed. A well-formed
///    tree:
///    - Does not have any loops
///    - All inner nodes have at least one child
#[inline(always)]
pub unsafe fn minimum_unchecked<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
>(
    root: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
) -> NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>> {
    let mut current_node = root;

    loop {
        current_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => unsafe { inner_node.as_ref().min().1 },
            ConcreteNodePtr::Node16(inner_node) => unsafe { inner_node.as_ref().min().1 },
            ConcreteNodePtr::Node48(inner_node) => unsafe { inner_node.as_ref().min().1 },
            ConcreteNodePtr::Node256(inner_node) => unsafe { inner_node.as_ref().min().1 },
            ConcreteNodePtr::LeafNode(inner_node) => {
                return inner_node;
            },
        }
    }
}

/// Search for the leaf with the maximum key, by lexicographic ordering.
///
/// # Safety
///
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
///
/// # Panics
///
///  - Panics if the tree at the root node is not well-formed. A well-formed
///    tree:
///    - Does not have any loops
///    - All inner nodes have at least one child
#[inline(always)]
pub unsafe fn maximum_unchecked<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
>(
    root: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
) -> NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>> {
    let mut current_node = root;

    loop {
        current_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => unsafe { inner_node.as_ref().max().1 },
            ConcreteNodePtr::Node16(inner_node) => unsafe { inner_node.as_ref().max().1 },
            ConcreteNodePtr::Node48(inner_node) => unsafe { inner_node.as_ref().max().1 },
            ConcreteNodePtr::Node256(inner_node) => unsafe { inner_node.as_ref().max().1 },
            ConcreteNodePtr::LeafNode(inner_node) => {
                return inner_node;
            },
        }
    }
}

#[cfg(test)]
mod tests;
