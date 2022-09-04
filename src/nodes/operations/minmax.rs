use crate::{ConcreteNodePtr, InnerNode, LeafNode, NodePtr, OpaqueNodePtr};

/// Search for the leaf with the minimum key, by lexicographic ordering.
///
/// # Safety
///
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
pub unsafe fn minimum_unchecked<V>(root: OpaqueNodePtr<V>) -> Option<NodePtr<LeafNode<V>>> {
    fn get_next_node<N: InnerNode>(inner_node: NodePtr<N>) -> Option<OpaqueNodePtr<N::Value>> {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `minimum_unchecked` function.
        let inner_node = unsafe { inner_node.as_ref() };

        // SAFETY: The iterator is limited to the lifetime of this function call and
        // does not escape. No other code mutates the referenced node, guaranteed by the
        // `minimum_unchecked` safey requirements and the reference.
        let mut iter = unsafe { inner_node.iter() };
        Some(iter.next()?.1)
    }

    let mut current_node = root;

    loop {
        match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => {
                current_node = get_next_node(inner_node)?;
            },
            ConcreteNodePtr::Node16(inner_node) => {
                current_node = get_next_node(inner_node)?;
            },
            ConcreteNodePtr::Node48(inner_node) => {
                current_node = get_next_node(inner_node)?;
            },
            ConcreteNodePtr::Node256(inner_node) => {
                current_node = get_next_node(inner_node)?;
            },
            ConcreteNodePtr::LeafNode(inner_node) => {
                return Some(inner_node);
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
pub unsafe fn maximum_unchecked<V>(root: OpaqueNodePtr<V>) -> Option<NodePtr<LeafNode<V>>> {
    fn get_next_node<N: InnerNode>(inner_node: NodePtr<N>) -> Option<OpaqueNodePtr<N::Value>> {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `maximum_unchecked` function.
        let inner_node = unsafe { inner_node.as_ref() };

        // SAFETY: The iterator is limited to the lifetime of this function call and
        // does not escape. No other code mutates the referenced node, guaranteed by the
        // `minimum_unchecked` safey requirements and the reference.
        let iter = unsafe { inner_node.iter() };
        Some(iter.last()?.1)
    }

    let mut current_node = root;

    loop {
        match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => {
                current_node = get_next_node(inner_node)?;
            },
            ConcreteNodePtr::Node16(inner_node) => {
                current_node = get_next_node(inner_node)?;
            },
            ConcreteNodePtr::Node48(inner_node) => {
                current_node = get_next_node(inner_node)?;
            },
            ConcreteNodePtr::Node256(inner_node) => {
                current_node = get_next_node(inner_node)?;
            },
            ConcreteNodePtr::LeafNode(inner_node) => {
                return Some(inner_node);
            },
        }
    }
}

#[cfg(test)]
mod tests;
