use crate::{ConcreteNodePtr, InnerNode, LeafNode, NodePtr, OpaqueNodePtr};

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
pub unsafe fn minimum_unchecked<V>(root: OpaqueNodePtr<V>) -> NodePtr<LeafNode<V>> {
    fn get_next_node<N: InnerNode>(inner_node: NodePtr<N>) -> OpaqueNodePtr<N::Value> {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `minimum_unchecked` function.
        let inner_node = unsafe { inner_node.as_ref() };

        // SAFETY: The iterator is limited to the lifetime of this function call and
        // does not escape. No other code mutates the referenced node, guaranteed by the
        // `minimum_unchecked` safey requirements and the reference.
        let mut iter = unsafe { inner_node.iter() };
        iter.next()
            .expect("an inner node must always have at least one child")
            .1
    }

    let mut current_node = root;

    loop {
        current_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => get_next_node(inner_node),
            ConcreteNodePtr::Node16(inner_node) => get_next_node(inner_node),
            ConcreteNodePtr::Node48(inner_node) => get_next_node(inner_node),
            ConcreteNodePtr::Node256(inner_node) => get_next_node(inner_node),
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
pub unsafe fn maximum_unchecked<V>(root: OpaqueNodePtr<V>) -> NodePtr<LeafNode<V>> {
    fn get_next_node<N: InnerNode>(inner_node: NodePtr<N>) -> OpaqueNodePtr<N::Value> {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `maximum_unchecked` function.
        let inner_node = unsafe { inner_node.as_ref() };

        // SAFETY: The iterator is limited to the lifetime of this function call and
        // does not escape. No other code mutates the referenced node, guaranteed by the
        // `minimum_unchecked` safey requirements and the reference.
        let mut iter = unsafe { inner_node.iter() };

        iter.next_back()
            .expect("an inner node must always have at least one child")
            .1
    }

    let mut current_node = root;

    loop {
        current_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => get_next_node(inner_node),
            ConcreteNodePtr::Node16(inner_node) => get_next_node(inner_node),
            ConcreteNodePtr::Node48(inner_node) => get_next_node(inner_node),
            ConcreteNodePtr::Node256(inner_node) => get_next_node(inner_node),
            ConcreteNodePtr::LeafNode(inner_node) => {
                return inner_node;
            },
        }
    }
}

#[cfg(test)]
mod tests;
