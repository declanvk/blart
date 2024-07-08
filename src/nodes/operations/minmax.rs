use crate::{ConcreteNodePtr, InnerNode, LeafNode, NodePtr, OpaqueNodePtr};

/// Search for the leaf with the minimum key, by lexicographic ordering.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
#[inline(always)]
pub unsafe fn minimum_unchecked<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
) -> NodePtr<PREFIX_LEN, LeafNode<K, V>> {
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
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
#[inline(always)]
pub unsafe fn maximum_unchecked<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
) -> NodePtr<PREFIX_LEN, LeafNode<K, V>> {
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
