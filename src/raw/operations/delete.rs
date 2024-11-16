use crate::{
    raw::{operations::lookup, ConcreteNodePtr, InnerNode, LeafNode, NodePtr, OpaqueNodePtr},
    AsBytes,
};

use super::PrefixMatchBehavior;

/// Remove a child node from the given inner node, return the child node
/// pointer if it was compressed.
///
/// The inner node will be compressed if there was only a single child
/// remaining after the delete. Compressing the node involves prepending the
/// inner node key prefix and child key byte to the child's key prefix.
///
/// # Safety
///  - `inner_node_ptr` must be a unique pointer to the node and must not have
///    any other mutable references.
///  - There must not be any mutable references to the children of the given
///    inner node either.
unsafe fn remove_child_from_inner_node_and_compress<
    const PREFIX_LEN: usize,
    N: InnerNode<PREFIX_LEN>,
>(
    inner_node_ptr: NodePtr<PREFIX_LEN, N>,
    key_fragment: u8,
) -> Option<OpaqueNodePtr<N::Key, N::Value, PREFIX_LEN>> {
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
        let mut children = inner_node.iter();
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
            // Construct the new prefix, by concatenating the parent header, child_key_byte,
            // child header.
            //
            // Here we can use the fact that the header of both the child and the parent can
            // hold up to PREFIX_LEN, so if for example the parent header len >=
            // PREFIX_LEN, the new child header will hold only this bytes since
            // the size is already greater than the capacity.
            //
            // so we can "clear" the child prefix, by setting the len to 0 and repopulate by
            // pushing the parent header, child_key_byte, child prefix. If the
            // header if already full we don't copy, just increment the len by
            // the size.
            let parent_header = inner_node.header();
            let parent_prefix = parent_header.read_prefix();
            let parent_len = parent_header.prefix_len();

            let (old_prefix, old_len, old_capped_len) = child_header.clear_prefix();
            child_header.push_prefix(parent_prefix, parent_len);
            child_header.push_prefix(&[child_key_byte], 1);
            child_header.push_prefix(&old_prefix[..old_capped_len], old_len);
        }
        // the else case here is that the child does not have a header, and
        // is a leaf

        // SAFETY: Since this function requires a unique pointer to the original
        // `inner_node_ptr`, we know that no other code will deallocate the pointer
        unsafe {
            drop(NodePtr::deallocate_node_ptr(inner_node_ptr));
        }

        Some(child_node_ptr)
    } else if N::TYPE.should_shrink_inner_node(inner_node.header().num_children()) {
        let new_inner_node = inner_node.shrink();

        let new_inner_node_ptr = NodePtr::allocate_node_ptr(new_inner_node).to_opaque();

        // SAFETY: Since this function requires a unique pointer to the original
        // `inner_node_ptr`, we know that no other code will deallocate the pointer
        unsafe {
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
///  - `parent_node_ptr` must be a unique pointer to the node and must not have
///    any other mutable references.
///  - There must not be any other mutable references to any children of the
///    `parent_node_ptr` either.
///  - `grandparent_node_ptr` must be a unique pointer to the node and must not
///    have any other mutable references.
///  - `leaf_node_ptr` must be a unique pointer to the node and not have any
///    other mutable references.
unsafe fn inner_delete_non_root_unchecked<K, V, const PREFIX_LEN: usize>(
    leaf_node_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    (parent_node_ptr, parent_key_byte): (OpaqueNodePtr<K, V, PREFIX_LEN>, u8),
    grandparent_node_ptr: Option<(OpaqueNodePtr<K, V, PREFIX_LEN>, u8)>,
    original_root: OpaqueNodePtr<K, V, PREFIX_LEN>,
) -> DeleteResult<K, V, PREFIX_LEN> {
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
        ConcreteNodePtr::LeafNode(_) => unreachable!("Cannot have delete from leaf node"),
    };

    // If the parent node was changed to something else, we have to write the new
    // value to the grandparent
    if let Some(new_parent_node_ptr) = new_parent_node_ptr {
        if let Some((grandparent_node_ptr, grandparent_key_byte)) = grandparent_node_ptr {
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
                    unreachable!("Cannot modify children of a leaf node")
                },
            }
        }
    }

    // SAFETY: Function safety doc covers the no concurrent read or modification of
    // this leaf node.
    unsafe { LeafNode::remove_self(leaf_node_ptr) }

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
pub struct DeleteResult<K, V, const PREFIX_LEN: usize> {
    /// The new root node for the tree, after the delete has been applied.
    ///
    /// If `None`, that means the tree is now empty.
    pub new_root: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,

    /// The leaf node that was successfully deleted.
    pub deleted_leaf: LeafNode<K, V, PREFIX_LEN>,
}

/// This struct represents a location in the trie that can be deleted.
pub struct DeletePoint<K, V, const PREFIX_LEN: usize> {
    /// The grandparent node of the leaf that will be deleted and the key byte
    /// that was used to continue search.
    ///
    /// If there is no grandparent, this value is `None`.
    pub grandparent_ptr_and_parent_key_byte: Option<(OpaqueNodePtr<K, V, PREFIX_LEN>, u8)>,

    /// The parent node of the leaf that will be deleted and the key byte that
    /// was used to continue search.
    ///
    /// If the leaf node to delete is also the root, then this value is `None`.
    /// If the grandparent node is present, this value also must be present.
    pub parent_ptr_and_child_key_byte: Option<(OpaqueNodePtr<K, V, PREFIX_LEN>, u8)>,

    /// The node to delete.
    pub leaf_node_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
}

impl<K, V, const PREFIX_LEN: usize> std::fmt::Debug for DeletePoint<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeleteSearchResult")
            .field(
                "grandparent_node",
                &self.grandparent_ptr_and_parent_key_byte,
            )
            .field("parent_node", &self.parent_ptr_and_child_key_byte)
            .field("leaf_node", &self.leaf_node_ptr)
            .finish()
    }
}

impl<K, V, const PREFIX_LEN: usize> DeletePoint<K, V, PREFIX_LEN> {
    /// Handle the logic of deleting a leaf node from the tree, after it has
    /// been found.
    ///
    /// # Safety
    ///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the
    ///    underlying tree
    ///  - This function cannot be called concurrently to any reads or writes of
    ///    the `root` node or any child node of `root`. This function will
    ///    arbitrarily read or write to any child in the given tree.
    pub unsafe fn apply(
        self,
        root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    ) -> DeleteResult<K, V, PREFIX_LEN> {
        let DeletePoint {
            grandparent_ptr_and_parent_key_byte: grandparent_node_ptr,
            parent_ptr_and_child_key_byte: parent_node_ptr,
            leaf_node_ptr,
        } = self;
        match (parent_node_ptr, grandparent_node_ptr) {
            (None, None) => {
                // The leaf node was also the root node. We don't need to remove the leaf from
                // the linked list here because the `previous` and `next` pointers should both
                // be `None`, since it is the only leaf.

                // SAFETY: The original `root` node pointer is a unique pointer to the tree
                // (required by safety doc), which means that leaf_node_ptr is also unique and
                // can be deallocated.
                let leaf_node = unsafe { NodePtr::deallocate_node_ptr(leaf_node_ptr) };

                DeleteResult {
                    new_root: None,
                    deleted_leaf: leaf_node,
                }
            },
            (None, Some(grandparent_node_ptr)) => {
                // search_for_node_to_delete should maintain this invariant
                unreachable!(
                    "This should be impossible, to have missing parent node and present \
                     grandparent node [{grandparent_node_ptr:?}]",
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
}

/// Search in the given tree for the leaf node to delete, returning `None` if it
/// does not exist.
///
/// This function also returns information that will be required in the delete
/// process, like the parent and possibly grandparent nodes.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
pub unsafe fn search_for_delete_point<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
) -> Option<DeletePoint<K, V, PREFIX_LEN>>
where
    K: AsBytes,
{
    let mut current_grandparent = None;
    let mut current_parent = None;
    let mut current_node = root;
    let mut current_depth = 0;
    let mut prefix_match_state = PrefixMatchBehavior::default();

    loop {
        let next_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                lookup::check_prefix_lookup_child(
                    inner_ptr,
                    key_bytes,
                    &mut current_depth,
                    &mut prefix_match_state,
                )
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                lookup::check_prefix_lookup_child(
                    inner_ptr,
                    key_bytes,
                    &mut current_depth,
                    &mut prefix_match_state,
                )
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                lookup::check_prefix_lookup_child(
                    inner_ptr,
                    key_bytes,
                    &mut current_depth,
                    &mut prefix_match_state,
                )
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                lookup::check_prefix_lookup_child(
                    inner_ptr,
                    key_bytes,
                    &mut current_depth,
                    &mut prefix_match_state,
                )
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                // SAFETY: The created reference doesn't escape the block and there are no
                // concurrent mutable references.
                let leaf = unsafe { leaf_node_ptr.as_ref() };

                // Specifically we are matching the leaf node stored key against the full search
                // key to confirm that it is the right value.
                if prefix_match_state.matches_leaf_key(leaf, key_bytes, current_depth) {
                    return Some(DeletePoint {
                        grandparent_ptr_and_parent_key_byte: current_grandparent,
                        parent_ptr_and_child_key_byte: current_parent,
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
        let last_key_byte = key_bytes[current_depth - 1];

        current_grandparent = current_parent;
        current_parent = Some((current_node, last_key_byte));
        current_node = next_node;
    }
}

/// Find the minimum leaf in the tree and return the information necessary to
/// delete it.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
#[inline]
pub unsafe fn find_minimum_to_delete<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
) -> DeletePoint<K, V, PREFIX_LEN> {
    let mut current_grandparent = None;
    let mut current_parent = None;
    let mut current_node = root;

    loop {
        // SAFETY: We hold a mutable reference, so creating
        // a shared reference is safe
        let (last_key_byte, next_node) = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => unsafe { inner_node.as_ref().min() },
            ConcreteNodePtr::Node16(inner_node) => unsafe { inner_node.as_ref().min() },
            ConcreteNodePtr::Node48(inner_node) => unsafe { inner_node.as_ref().min() },
            ConcreteNodePtr::Node256(inner_node) => unsafe { inner_node.as_ref().min() },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                return DeletePoint {
                    grandparent_ptr_and_parent_key_byte: current_grandparent,
                    parent_ptr_and_child_key_byte: current_parent,
                    leaf_node_ptr,
                };
            },
        };

        current_grandparent = current_parent;
        current_parent = Some((current_node, last_key_byte));
        current_node = next_node;
    }
}

/// Find the maximum leaf in the tree and return the information necessary to
/// delete it.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
#[inline]
pub unsafe fn find_maximum_to_delete<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
) -> DeletePoint<K, V, PREFIX_LEN> {
    let mut current_grandparent = None;
    let mut current_parent = None;
    let mut current_node = root;

    loop {
        // SAFETY: We hold a mutable reference, so creating
        // a shared reference is safe
        let (last_key_byte, next_node) = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => unsafe { inner_node.as_ref().max() },
            ConcreteNodePtr::Node16(inner_node) => unsafe { inner_node.as_ref().max() },
            ConcreteNodePtr::Node48(inner_node) => unsafe { inner_node.as_ref().max() },
            ConcreteNodePtr::Node256(inner_node) => unsafe { inner_node.as_ref().max() },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                return DeletePoint {
                    grandparent_ptr_and_parent_key_byte: current_grandparent,
                    parent_ptr_and_child_key_byte: current_parent,
                    leaf_node_ptr,
                };
            },
        };

        current_grandparent = current_parent;
        current_parent = Some((current_node, last_key_byte));
        current_node = next_node;
    }
}

#[cfg(test)]
mod tests;
