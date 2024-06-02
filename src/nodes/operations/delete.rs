use std::borrow::Borrow;

use crate::{
    nodes::operations::lookup, AsBytes, ConcreteNodePtr, InnerNode, LeafNode, NodePtr,
    OpaqueNodePtr,
};

/// Removes a key from the tree, returning the [`LeafNode`] corresponding to the
/// key if the key was previously in the tree.
///
/// # Safety
///
///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the underlying
///    tree
///  - This function cannot be called concurrently to any reads or writes of the
///    `root` node or any child node of `root`. This function will arbitrarily
///    read or write to any child in the given tree.
pub unsafe fn delete_unchecked<Q, K, V>(
    root: OpaqueNodePtr<K, V>,
    key: &Q,
) -> Option<DeleteResult<K, V>>
where
    K: Borrow<Q> + AsBytes,
    Q: AsBytes + ?Sized,
{
    // SAFETY: Requirements covered by containing function
    unsafe {
        let delete_search_result = search_for_node_to_delete(root, key)?;

        Some(inner_delete_unchecked(root, delete_search_result))
    }
}

/// Find and delete the minimum leaf in the tree, returning the minimum
/// [`LeafNode`].
///
/// A well-formed tree is always guaranteed to have a minimum leaf. A
/// well-formed tree:
///  - does not have any loops
///  - all inner nodes have at least 1 child
///
/// # Safety
///
///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the underlying
///    tree
///  - This function cannot be called concurrently to any reads or writes of the
///    `root` node or any child node of `root`. This function will arbitrarily
///    read or write to any child in the given tree.
pub unsafe fn delete_minimum_unchecked<K, V>(root: OpaqueNodePtr<K, V>) -> DeleteResult<K, V> {
    // SAFETY: Requirements covered by containing function
    unsafe {
        let delete_search_result = find_minimum_to_delete(root);

        inner_delete_unchecked(root, delete_search_result)
    }
}

/// Find and delete the maximum leaf in the tree, returning the maximum
/// [`LeafNode`].
///
/// A well-formed tree is always guaranteed to have a maximum leaf. A
/// well-formed tree:
///  - does not have any loops
///  - all inner nodes have at least 1 child
///
/// # Safety
///
///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the underlying
///    tree
///  - This function cannot be called concurrently to any reads or writes of the
///    `root` node or any child node of `root`. This function will arbitrarily
///    read or write to any child in the given tree.
pub unsafe fn delete_maximum_unchecked<K, V>(root: OpaqueNodePtr<K, V>) -> DeleteResult<K, V> {
    // SAFETY: Requirements covered by containing function
    unsafe {
        let delete_search_result = find_maximum_to_delete(root);

        inner_delete_unchecked(root, delete_search_result)
    }
}

/// Handle the logic of deleting a leaf node from the tree, after it has been
/// found.
///
/// # Safety
///
///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the underlying
///    tree
///  - This function cannot be called concurrently to any reads or writes of the
///    `root` node or any child node of `root`. This function will arbitrarily
///    read or write to any child in the given tree.
unsafe fn inner_delete_unchecked<K, V>(
    root: OpaqueNodePtr<K, V>,
    DeleteSearchResult {
        grandparent_node_ptr,
        parent_node_ptr,
        leaf_node_ptr,
    }: DeleteSearchResult<K, V>,
) -> DeleteResult<K, V> {
    match (parent_node_ptr, grandparent_node_ptr) {
        (None, None) => {
            // The leaf node was also the root node

            // SAFETY: The original `root` node pointer is a unique pointer to the tree
            // (required by safety doc), which means that leaf_node_ptr is also unique and
            // can be deallocated.
            let leaf_node = unsafe { NodePtr::deallocate_node_ptr(leaf_node_ptr) };

            DeleteResult {
                new_root: None,
                deleted_leaf: leaf_node,
            }
        },
        (None, Some(granparent_node_ptr)) => {
            // search_for_node_to_delete should maintain this invariant
            panic!(
                "This should be impossible, to have missing parent node and present grandparent \
                 node [{granparent_node_ptr:?}]",
            );
        },
        (Some(parent_node_ptr), grandparent_node_ptr) => unsafe {
            // SAFETY: `root` is a unique pointer to the tree and there will be no
            // concurrent reads or writes to any portion of the tree, so all these child
            // nodes will be unique pointers and not read/written.
            inner_delete_non_root_unchecked(
                leaf_node_ptr,
                parent_node_ptr,
                grandparent_node_ptr,
                root,
            )
        },
    }
}

/// Remove a child node from the given inner node, return the child node
/// pointer if it was compressed.
///
/// The inner node will be compressed if there was only a single child
/// remaining after the delete. Compressing the node involves prepending the
/// inner node key prefix and child key byte to the child's key prefix.
///
/// # Safety
///
///  - `inner_node_ptr` must be a unique pointer to the node and must not have
///    any other mutable references.
///  - There must not be any mutable references to the children of the given
///    inner node either.
unsafe fn remove_child_from_inner_node_and_compress<N: InnerNode>(
    inner_node_ptr: NodePtr<N>,
    key_fragment: u8,
) -> Option<OpaqueNodePtr<N::Key, N::Value>> {
    // SAFETY: The `inner_node` reference is scoped to this function and dropped
    // before cases where the inner node is deallocated. It is a unique reference,
    // by the safety requirements of the containing function.
    let inner_node = unsafe { inner_node_ptr.as_mut() };

    inner_node
        .remove_child(key_fragment)
        .expect("child should be present");

    if inner_node.header().num_children() == 1 {
        // need to compress node into child

        // SAFETY: The iterator only lasts until the remaining child is pulled out, then
        // dropped. The scope does not overlap with any mutating operations on the inner
        // node.
        let mut children = unsafe { inner_node.iter() };
        let (child_key_byte, child_node_ptr) = children.next().expect("expected single child");
        assert!(
            children.next().is_none(),
            "expected only a single child, not more"
        );
        drop(children);

        // SAFETY: By the safety requirements of the function, there are no other
        // references to this child node. The reference only lasts for the scope of this
        // `if` block.
        if let Some(child_header) = unsafe { child_node_ptr.header_mut() } {
            // This needs to go in reverse order, since prepend_prefix always writes to the
            // front
            child_header.prepend_prefix(&[child_key_byte]);
            child_header.prepend_prefix(inner_node.header().read_prefix());
        }
        // the else case here is that the child does not have a header, and
        // is a leaf

        // SAFETY: Since this function requires a unique pointer to the original
        // `inner_node_ptr`, we know that no other code will deallocate the pointer
        unsafe {
            // Do not use the `inner_node` mutable reference after this point in this block,
            // since the node has been deallocated
            drop(NodePtr::deallocate_node_ptr(inner_node_ptr));
        }

        Some(child_node_ptr)
    } else if N::TYPE.should_shrink_inner_node(inner_node.header().num_children()) {
        let new_inner_node = inner_node.shrink();

        let new_inner_node_ptr = NodePtr::allocate_node_ptr(new_inner_node).to_opaque();

        // SAFETY: Since this function requires a unique pointer to the original
        // `inner_node_ptr`, we know that no other code will deallocate the pointer
        unsafe {
            // Do not use the `inner_node` mutable reference after this point in this block,
            // since the node has been deallocated
            drop(NodePtr::deallocate_node_ptr(inner_node_ptr));
        }

        Some(new_inner_node_ptr)
    } else {
        None
    }
}

/// Delete the given non-root leaf node.
///
/// # Safety
///
///  - `parent_node_ptr` must be a unique pointer to the node and must not have
///    any other mutable references.
///  - There must not be any other mutable references to any children of the
///    `parent_node_ptr` either.
///  - `grandparent_node_ptr` must be a unique pointer to the node and must not
///    have any other mutable references.
///  - `leaf_node_ptr` must be a unique pointer to the node and not have any
///    other mutable references.
unsafe fn inner_delete_non_root_unchecked<K, V>(
    leaf_node_ptr: NodePtr<LeafNode<K, V>>,
    (parent_key_byte, parent_node_ptr): (u8, OpaqueNodePtr<K, V>),
    grandparent_node_ptr: Option<(u8, OpaqueNodePtr<K, V>)>,
    original_root: OpaqueNodePtr<K, V>,
) -> DeleteResult<K, V> {
    let new_parent_node_ptr = match parent_node_ptr.to_node_ptr() {
        ConcreteNodePtr::Node4(parent_node_ptr) => unsafe {
            // SAFETY: Covered by containing function safety doc
            remove_child_from_inner_node_and_compress(parent_node_ptr, parent_key_byte)
        },
        ConcreteNodePtr::Node16(parent_node_ptr) => unsafe {
            // SAFETY: Covered by containing function safety doc
            remove_child_from_inner_node_and_compress(parent_node_ptr, parent_key_byte)
        },
        ConcreteNodePtr::Node48(parent_node_ptr) => unsafe {
            // SAFETY: Covered by containing function safety doc
            remove_child_from_inner_node_and_compress(parent_node_ptr, parent_key_byte)
        },
        ConcreteNodePtr::Node256(parent_node_ptr) => unsafe {
            // SAFETY: Covered by containing function safety doc
            remove_child_from_inner_node_and_compress(parent_node_ptr, parent_key_byte)
        },
        ConcreteNodePtr::LeafNode(_) => panic!("Cannot have delete from leaf node"),
    };

    // If the parent node was changed to something else, we have to write the new
    // value to the grandparent
    if let Some(new_parent_node_ptr) = new_parent_node_ptr {
        if let Some((grandparent_key_byte, grandparent_node_ptr)) = grandparent_node_ptr {
            match grandparent_node_ptr.to_node_ptr() {
                ConcreteNodePtr::Node4(inner_node_ptr) => {
                    // SAFETY: The scope of the mutable reference is limited to this block, and
                    // the containing function safety requirements mean that there are no other
                    // mutable references to the same node.
                    let inner_node = unsafe { inner_node_ptr.as_mut() };
                    inner_node.write_child(grandparent_key_byte, new_parent_node_ptr);
                },
                ConcreteNodePtr::Node16(inner_node_ptr) => {
                    // SAFETY: The scope of the mutable reference is limited to this block, and
                    // the containing function safety requirements mean that there are no other
                    // mutable references to the same node.
                    let inner_node = unsafe { inner_node_ptr.as_mut() };
                    inner_node.write_child(grandparent_key_byte, new_parent_node_ptr);
                },
                ConcreteNodePtr::Node48(inner_node_ptr) => {
                    // SAFETY: The scope of the mutable reference is limited to this block, and
                    // the containing function safety requirements mean that there are no other
                    // mutable references to the same node.
                    let inner_node = unsafe { inner_node_ptr.as_mut() };
                    inner_node.write_child(grandparent_key_byte, new_parent_node_ptr);
                },
                ConcreteNodePtr::Node256(inner_node_ptr) => {
                    // SAFETY: The scope of the mutable reference is limited to this block, and
                    // the containing function safety requirements mean that there are no other
                    // mutable references to the same node.
                    let inner_node = unsafe { inner_node_ptr.as_mut() };
                    inner_node.write_child(grandparent_key_byte, new_parent_node_ptr);
                },
                ConcreteNodePtr::LeafNode(_) => {
                    panic!("Cannot modify children of a leaf node")
                },
            }
        }
    }

    // SAFETY: `leaf_node_ptr` is a unique pointer to the leaf node, no other code
    // will deallocate this
    let leaf_node = unsafe { NodePtr::deallocate_node_ptr(leaf_node_ptr) };

    let new_root = match (new_parent_node_ptr, grandparent_node_ptr) {
        (Some(new_parent_node_ptr), None) => new_parent_node_ptr,
        _ => original_root,
    };

    DeleteResult {
        new_root: Some(new_root),
        deleted_leaf: leaf_node,
    }
}

/// The results of a successful delete operation
#[derive(Debug)]
pub struct DeleteResult<K, V> {
    /// The new root node for the tree, after the delete has been applied.
    ///
    /// If `None`, that means the tree is now empty.
    pub new_root: Option<OpaqueNodePtr<K, V>>,
    /// The leaf node that was successfully deleted.
    pub deleted_leaf: LeafNode<K, V>,
}

struct DeleteSearchResult<K, V> {
    /// The grandparent node of the leaf that will be deleted and the key byte
    /// that was used to continue search.
    ///
    /// If there is no grandparent, this value is `None`.
    grandparent_node_ptr: Option<(u8, OpaqueNodePtr<K, V>)>,

    /// The parent node of the leaf that will be deleted and the key byte that
    /// was used to continue search.
    ///
    /// If the leaf node to delete is also the root, then this value is `None`.
    /// If the grandparent node is present, this value also must be present.
    parent_node_ptr: Option<(u8, OpaqueNodePtr<K, V>)>,
    /// The node to delete.
    leaf_node_ptr: NodePtr<LeafNode<K, V>>,
}

impl<K, V> std::fmt::Debug for DeleteSearchResult<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeleteSearchResult")
            .field("grandparent_node", &self.grandparent_node_ptr)
            .field("parent_node", &self.parent_node_ptr)
            .field("leaf_node", &self.leaf_node_ptr)
            .finish()
    }
}

/// Search in the given tree for the leaf node to delete, returning `None` if it
/// does not exist.
///
/// This function also returns information that will be required in the delete
/// process, like the parent and possibly grandparent nodes.
///
/// # Safety
///
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
unsafe fn search_for_node_to_delete<Q, K, V>(
    root: OpaqueNodePtr<K, V>,
    key: &Q,
) -> Option<DeleteSearchResult<K, V>>
where
    K: Borrow<Q> + AsBytes,
    Q: AsBytes + ?Sized,
{
    let mut current_grandparent = None;
    let mut current_parent = None;
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        let next_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                lookup::check_prefix_lookup_child(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                lookup::check_prefix_lookup_child(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                lookup::check_prefix_lookup_child(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                lookup::check_prefix_lookup_child(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                let leaf_node = leaf_node_ptr.read();

                // Specifically we are matching the leaf node stored key against the full search
                // key to confirm that it is the right value.
                if leaf_node.matches_full_key(key) {
                    return Some(DeleteSearchResult {
                        grandparent_node_ptr: current_grandparent,
                        parent_node_ptr: current_parent,
                        leaf_node_ptr,
                    });
                } else {
                    return None;
                }
            },
        }?;

        debug_assert!(
            current_depth > 0,
            "for a non-leaf node, there should be some amount of key"
        );

        // This should not panic because the current_depth will be greater than zero
        let last_key_byte = key.as_bytes()[current_depth - 1];

        current_grandparent = current_parent;
        current_parent = Some((last_key_byte, current_node));
        current_node = next_node;
    }
}

/// Find the minimum leaf in the tree and return the information necessary to
/// delete it.
///
/// # Safety
///
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
unsafe fn find_minimum_to_delete<K, V>(root: OpaqueNodePtr<K, V>) -> DeleteSearchResult<K, V> {
    unsafe fn get_next_node<N: InnerNode>(
        inner_node: NodePtr<N>,
        current_depth: &mut usize,
    ) -> (u8, OpaqueNodePtr<N::Key, N::Value>) {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `minimum_to_delete` function.
        let inner_node = unsafe { inner_node.as_ref() };

        // SAFETY: The iterator is limited to the lifetime of this function call and
        // does not escape. No other code mutates the referenced node, guaranteed by the
        // `minimum_to_delete` safey requirements and the reference.
        let mut iter = unsafe { inner_node.iter() };

        let child = iter
            .next()
            .expect("an inner node must always have at least one child");

        // increment current depth with header size and child key byte
        *current_depth += inner_node.header().num_children() + 1;

        child
    }

    let mut current_grandparent = None;
    let mut current_parent = None;
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        let (last_key_byte, next_node) = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                get_next_node(inner_ptr, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                get_next_node(inner_ptr, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                get_next_node(inner_ptr, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                get_next_node(inner_ptr, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                return DeleteSearchResult {
                    grandparent_node_ptr: current_grandparent,
                    parent_node_ptr: current_parent,
                    leaf_node_ptr,
                };
            },
        };

        current_grandparent = current_parent;
        current_parent = Some((last_key_byte, current_node));
        current_node = next_node;
    }
}

/// Find the maximum leaf in the tree and return the information necessary to
/// delete it.
///
/// # Safety
///
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
unsafe fn find_maximum_to_delete<K, V>(root: OpaqueNodePtr<K, V>) -> DeleteSearchResult<K, V> {
    unsafe fn get_next_node<N: InnerNode>(
        inner_node: NodePtr<N>,
        current_depth: &mut usize,
    ) -> (u8, OpaqueNodePtr<N::Key, N::Value>) {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `minimum_to_delete` function.
        let inner_node = unsafe { inner_node.as_ref() };

        // SAFETY: The iterator is limited to the lifetime of this function call and
        // does not escape. No other code mutates the referenced node, guaranteed by the
        // `minimum_to_delete` safey requirements and the reference.
        let mut iter = unsafe { inner_node.iter() };

        let child = iter
            .next_back()
            .expect("an inner node must always have at least one child");

        // increment current depth with header size and child key byte
        *current_depth += inner_node.header().num_children() + 1;

        child
    }

    let mut current_grandparent = None;
    let mut current_parent = None;
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        let (last_key_byte, next_node) = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                get_next_node(inner_ptr, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                get_next_node(inner_ptr, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                get_next_node(inner_ptr, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                get_next_node(inner_ptr, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                return DeleteSearchResult {
                    grandparent_node_ptr: current_grandparent,
                    parent_node_ptr: current_parent,
                    leaf_node_ptr,
                };
            },
        };

        current_grandparent = current_parent;
        current_parent = Some((last_key_byte, current_node));
        current_node = next_node;
    }
}

#[cfg(test)]
mod tests;
