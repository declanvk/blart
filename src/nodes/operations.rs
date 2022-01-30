//! Trie node lookup and manipulation

use super::{InnerNode4, InnerNodePtr, LeafNode, NodePtr, OpaqueNodePtr};
use std::{error::Error, fmt::Display, mem::ManuallyDrop};

/// Search in the given tree for the value stored with the given key.
///
/// # Safety
///
///   - This function cannot be called concurrently to any reads or writes of
///     `root` or any child node of `root`. This function will arbitrarily read
///     to any child in the given tree.
pub unsafe fn search_unchecked<V>(
    root: OpaqueNodePtr<V>,
    key: &[u8],
) -> Option<NodePtr<LeafNode<V>>> {
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        if let Some(leaf_node_ptr) = current_node.cast::<LeafNode<V>>() {
            let leaf_node = leaf_node_ptr.read();

            // Specifically we are matching the leaf node stored key against the full search
            // key to confirm that it is the right value. Due to the method used for prefix
            // compression, we don't explicity store all the compressed prefixes down the
            // tree.
            if leaf_node.matches_key(key) {
                return Some(leaf_node_ptr);
            } else {
                return None;
            }
        }

        let header = current_node.read();
        if header.match_prefix(&key[current_depth..]) != header.prefix_size() {
            return None;
        }

        // Since the prefix matched, we need to advance the depth by the size
        // of the prefix
        current_depth += header.prefix_size();

        let next_key_fragment = if current_depth < key.len() {
            key[current_depth]
        } else {
            return None;
        };

        // SAFETY: We checked that the current node is not a leaf earlier in the loop
        let next_child_node = unsafe { lookup_child_unchecked(current_node, next_key_fragment) };

        current_node = next_child_node?;
        // Increment by a single byte
        current_depth += 1;
    }
}

/// Insert the given key-value pair into the tree.
///
/// Returns either a pointer to the new tree root or an error.
///
/// # Errors
///
///   - Returns a [`InsertError::EmptyKey`] if the given key is an empty array.
///   - Returns a [`InsertError::PrefixKey`] if the given key is a prefix of
///     another key that exists in the trie. Or if the given key is prefixed by
///     an existing key in the trie.
///
/// # Safety
///
///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the underlying
///    node object, otherwise a deallocation may create dangling pointers.
///  - This function cannot be called concurrently to any reads or writes of the
///    `root` node or any child node of `root`. This function will arbitrarily
///    read or write to any child in the given tree.
pub unsafe fn insert_unchecked<V>(
    root: OpaqueNodePtr<V>,
    key: Box<[u8]>,
    value: V,
) -> Result<OpaqueNodePtr<V>, InsertError> {
    // TODO: Consider an iterative solution to handle tree with long keys.
    fn insert_rec_inner<V>(
        mut root: OpaqueNodePtr<V>,
        key: Box<[u8]>,
        value: V,
        mut depth: usize,
    ) -> Result<OpaqueNodePtr<V>, InsertError> {
        if let Some(leaf_node_ptr) = root.cast::<LeafNode<V>>() {
            let leaf_node = leaf_node_ptr.read();

            let mut new_n4 = InnerNode4::empty();
            let prefix_size = leaf_node.key[depth..]
                .iter()
                .zip(key[depth..].iter())
                .take_while(|(k1, k2)| k1 == k2)
                .count();
            new_n4
                .header
                .write_prefix(&key[depth..(depth + prefix_size)]);
            depth += prefix_size;

            if depth >= key.len() || depth >= leaf_node.key.len() {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key OR an existing key is a prefix of it

                return Err(InsertError::PrefixKey(key));
            }

            let new_leaf_key_byte = key[depth];
            let new_leaf_pointer = NodePtr::allocate_node(LeafNode::new(key, value));

            new_n4.write_child(leaf_node.key[depth], root);
            new_n4.write_child(new_leaf_key_byte, new_leaf_pointer.to_opaque());

            return Ok(NodePtr::allocate_node(new_n4).to_opaque());
        }

        // since header is mutable will need to write it back
        let mut header = root.read();
        let matched_prefix_size = header.match_prefix(&(key)[depth..]);
        if matched_prefix_size != header.prefix_size() {
            // prefix mismatch, need to split prefix into two separate nodes and take the
            // common prefix into a new parent node
            let mut new_n4 = InnerNode4::empty();

            if (depth + matched_prefix_size) >= key.len() {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key

                return Err(InsertError::PrefixKey(key));
            }

            let new_leaf_key_byte = key[depth + matched_prefix_size];
            let new_leaf_pointer = NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque();

            new_n4.write_child(header.read_prefix()[matched_prefix_size], root);
            new_n4.write_child(new_leaf_key_byte, new_leaf_pointer);

            new_n4
                .header
                .write_prefix(&header.read_prefix()[..matched_prefix_size]);
            header.ltrim_prefix(matched_prefix_size + 1);

            // Updated the header information here
            root.write(ManuallyDrop::into_inner(header));
            return Ok(NodePtr::allocate_node(new_n4).to_opaque());
        }

        depth += header.prefix_size();

        let next_key_fragment = if depth < key.len() {
            key[depth]
        } else {
            return Err(InsertError::PrefixKey(key));
        };

        // SAFETY: We checked that the current node is not a leaf earlier in the loop
        let next_child_node = unsafe { lookup_child_unchecked(root, next_key_fragment) };

        match next_child_node {
            Some(next_child_node) => {
                let new_child = insert_rec_inner(next_child_node, key, value, depth + 1)?;
                // SAFETY: We determine that the current node is not a leaf by checking earlier
                // in the loop. The requirement of no other current read or write to the
                // `current_node` is carried to the caller of `insert`. From inside the `insert`
                // function, there are no other current reads or writes.
                unsafe {
                    overwrite_child_unchecked(root, next_key_fragment, new_child);
                }
            },
            None => {
                if header.is_full() {
                    // we will create a new node of the next larger type and copy all the children
                    // over.

                    // SAFETY: We determine that the current node is not a leaf by checking earlier
                    // in the loop. The uniqueness requirement for the `current_node` must be upheld
                    // at the `insert` function level. The `insert` function does not create
                    // aliasing node pointers.
                    unsafe {
                        root = grow_unchecked(root);
                    }
                }

                // SAFETY: We determine that the current node is not a leaf by checking earlier
                // in the loop. The requirement of no other current read or write to the
                // `current_node` is carried to the caller of `insert`. From inside the `insert`
                // function, there are no other current reads or writes.
                unsafe {
                    insert_child_unchecked(
                        root,
                        key[depth],
                        NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque(),
                    );
                }
            },
        }

        Ok(root)
    }

    if key.is_empty() {
        return Err(InsertError::EmptyKey);
    }

    insert_rec_inner(root, key, value, 0)
}

/// The error type for the insert operation on the tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InsertError {
    /// Attempted to insert an empty key.
    EmptyKey,
    /// Attempted to insert a key which was a prefix of an existing key in the
    /// tree.
    PrefixKey(Box<[u8]>),
}

impl Display for InsertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertError::EmptyKey => write!(f, "Key is an empty array of bytes."),
            InsertError::PrefixKey(key) => {
                write!(
                    f,
                    "Attempted to insert a key [{key:?}] which is either a prefix of an existing \
                     key or an existing key is a prefix of the new key."
                )
            },
        }
    }
}

impl Error for InsertError {}

/// Lookup the child of the current node, excluding the possibility of a
/// LeafNode.
///
/// # Safety
///
/// The current node must not be a leaf node.
unsafe fn lookup_child_unchecked<V>(
    current_node: OpaqueNodePtr<V>,
    next_key_fragment: u8,
) -> Option<OpaqueNodePtr<V>> {
    match current_node.to_node_ptr() {
        InnerNodePtr::Node4(inner_node) => inner_node.read().lookup_child(next_key_fragment),
        InnerNodePtr::Node16(inner_node) => inner_node.read().lookup_child(next_key_fragment),
        InnerNodePtr::Node48(inner_node) => inner_node.read().lookup_child(next_key_fragment),
        InnerNodePtr::Node256(inner_node) => inner_node.read().lookup_child(next_key_fragment),
        InnerNodePtr::LeafNode(_) => unreachable!(
            "This branch is not possible because of the safety invariants of the function."
        ),
    }
}

/// Grow the current node into the next larger size, excluding the possibility
/// of a LeafNode.
///
/// # Safety
///
///  - The current node must not be a leaf node.
///  - The `current_node` must be a reference to the only existing pointer to
///    the node object, otherwise the possible deallocation may create dangling
///    pointers.
///
/// # Panic
///
///  - Panics if the current node is a `InnerNode256` as this cannot grow any
///    larger.
unsafe fn grow_unchecked<V>(current_node: OpaqueNodePtr<V>) -> OpaqueNodePtr<V> {
    match current_node.to_node_ptr() {
        InnerNodePtr::Node4(old_node) => {
            let inner_node = old_node.read();
            let new_node = inner_node.grow();

            // SAFETY: The `deallocate_node` function is only called a single time. The
            // uniqueness requirement is passed up to the `grow_unchecked` safety
            // requirements.
            unsafe {
                NodePtr::deallocate_node(old_node);
            }

            NodePtr::allocate_node(new_node).to_opaque()
        },
        InnerNodePtr::Node16(old_node) => {
            let inner_node = old_node.read();
            let new_node = inner_node.grow();

            // SAFETY: The `deallocate_node` function is only called a single time. The
            // uniqueness requirement is passed up to the `grow_unchecked` safety
            // requirements.
            unsafe {
                NodePtr::deallocate_node(old_node);
            }

            NodePtr::allocate_node(new_node).to_opaque()
        },
        InnerNodePtr::Node48(old_node) => {
            let inner_node = old_node.read();
            let new_node = inner_node.grow();

            // SAFETY: The `deallocate_node` function is only called a single time. The
            // uniqueness requirement is passed up to the `grow_unchecked` safety
            // requirements.
            unsafe {
                NodePtr::deallocate_node(old_node);
            }

            NodePtr::allocate_node(new_node).to_opaque()
        },
        InnerNodePtr::Node256(_) => unreachable!("Unable to grow a Node256, something went wrong!"),
        InnerNodePtr::LeafNode(_) => unreachable!(
            "This branch is not possible because of the safety invariants of the function."
        ),
    }
}

/// Insert a new child into the current node, excluding the possibility of a
/// leaf node.
///
/// # Safety
///
///  - The current node must not be a leaf node.
///  - This function must not be called concurrently with any other read or
///    mutation of the given `current_node`.
unsafe fn insert_child_unchecked<V>(
    current_node: OpaqueNodePtr<V>,
    key_fragment: u8,
    child: OpaqueNodePtr<V>,
) {
    // SAFETY: The `update` function safety requirements are passed onto the caller.
    unsafe {
        match current_node.to_node_ptr() {
            InnerNodePtr::Node4(old_node) => old_node.update(|inner_node| {
                inner_node.write_child(key_fragment, child);
            }),
            InnerNodePtr::Node16(old_node) => old_node.update(|inner_node| {
                inner_node.write_child(key_fragment, child);
            }),
            InnerNodePtr::Node48(old_node) => old_node.update(|inner_node| {
                inner_node.write_child(key_fragment, child);
            }),
            InnerNodePtr::Node256(old_node) => old_node.update(|inner_node| {
                inner_node.write_child(key_fragment, child);
            }),
            InnerNodePtr::LeafNode(_) => unreachable!(
                "This branch is not possible because of the safety invariants of the function."
            ),
        }
    }
}

/// Overwrite a child in the current node, excluding the possibility of a
/// leaf node.
///
/// # Safety
///
///  - The current node must not be a leaf node.
///  - This function must not be called concurrently with any other read or
///    mutation of the given `current_node`.
unsafe fn overwrite_child_unchecked<V>(
    current_node: OpaqueNodePtr<V>,
    key_fragment: u8,
    child: OpaqueNodePtr<V>,
) {
    // SAFETY: The `update` function safety requirements are passed onto the caller.
    unsafe {
        match current_node.to_node_ptr() {
            InnerNodePtr::Node4(old_node) => old_node.update(|inner_node| {
                inner_node.write_child(key_fragment, child);
            }),
            InnerNodePtr::Node16(old_node) => old_node.update(|inner_node| {
                inner_node.write_child(key_fragment, child);
            }),
            InnerNodePtr::Node48(old_node) => old_node.update(|inner_node| {
                inner_node.write_child(key_fragment, child);
            }),
            InnerNodePtr::Node256(old_node) => old_node.update(|inner_node| {
                inner_node.write_child(key_fragment, child);
            }),
            InnerNodePtr::LeafNode(_) => unreachable!(
                "This branch is not possible because of the safety invariants of the function."
            ),
        }
    }
}

/// Deallocate the given node and all children of the given node.
///
/// This will also deallocate the leaf nodes with their value type data.
///
/// # Safety
///
///  - The `current_node` must be the only existing pointer to the node object
///    and all the children of the node object, otherwise the deallocation may
///    create dangling pointers.
pub unsafe fn deallocate_tree<V>(root: OpaqueNodePtr<V>) {
    // TODO: Consider an iterative solution to handle tree with long keys.

    match root.to_node_ptr() {
        InnerNodePtr::Node4(inner) => {
            {
                let inner = inner.read();
                for (_, child) in inner.iter() {
                    // SAFETY: The safety requirements of this function are already satisfied by the
                    // caller as this is a recursive call.
                    unsafe { deallocate_tree(child) }
                }
            }
            // SAFETY: The uniqueness requirement of the `deallocate_node` function is
            // satisfied by the safety requirements on the `deallocate_tree` function.
            unsafe { NodePtr::deallocate_node(inner) }
        },
        InnerNodePtr::Node16(inner) => {
            {
                let inner = inner.read();
                for (_, child) in inner.iter() {
                    // SAFETY: The safety requirements of this function are already satisfied by the
                    // caller as this is a recursive call.
                    unsafe { deallocate_tree(child) }
                }
            }
            // SAFETY: The uniqueness requirement of the `deallocate_node` function is
            // satisfied by the safety requirements on the `deallocate_tree` function.
            unsafe { NodePtr::deallocate_node(inner) }
        },
        InnerNodePtr::Node48(inner) => {
            {
                let inner = inner.read();
                for (_, child) in inner.iter() {
                    // SAFETY: The safety requirements of this function are already satisfied by the
                    // caller as this is a recursive call.
                    unsafe { deallocate_tree(child) }
                }
            }
            // SAFETY: The uniqueness requirement of the `deallocate_node` function is
            // satisfied by the safety requirements on the `deallocate_tree` function.
            unsafe { NodePtr::deallocate_node(inner) }
        },
        InnerNodePtr::Node256(inner) => {
            {
                let inner = inner.read();
                for (_, child) in inner.iter() {
                    // SAFETY: The safety requirements of this function are already satisfied by the
                    // caller as this is a recursive call.
                    unsafe { deallocate_tree(child) }
                }
            }
            // SAFETY: The uniqueness requirement of the `deallocate_node` function is
            // satisfied by the safety requirements on the `deallocate_tree` function.
            unsafe { NodePtr::deallocate_node(inner) }
        },
        InnerNodePtr::LeafNode(inner) => {
            // SAFETY: The uniqueness requirement of the `deallocate_node` function is
            // satisfied by the safety requirements on the `deallocate_tree` function.
            unsafe { NodePtr::deallocate_node(inner) }
        },
    }
}

/// Search for the leaf with the minimum key, by lexicographic ordering.
///
/// # Safety
///
///   - This function cannot be called concurrently to any reads or writes of
///     `root` or any child node of `root`. This function will arbitrarily read
///     to any child in the given tree.
pub unsafe fn minimum_unchecked<V>(root: OpaqueNodePtr<V>) -> Option<NodePtr<LeafNode<V>>> {
    let mut current_node = root;

    loop {
        match current_node.to_node_ptr() {
            InnerNodePtr::Node4(inner_node) => {
                let inner_node = inner_node.read();
                current_node = inner_node.iter().next()?.1;
            },
            InnerNodePtr::Node16(inner_node) => {
                let inner_node = inner_node.read();
                current_node = inner_node.iter().next()?.1;
            },
            InnerNodePtr::Node48(inner_node) => {
                let inner_node = inner_node.read();
                current_node = inner_node.iter().next()?.1;
            },
            InnerNodePtr::Node256(inner_node) => {
                let inner_node = inner_node.read();
                current_node = inner_node.iter().next()?.1;
            },
            InnerNodePtr::LeafNode(inner_node) => {
                return Some(inner_node);
            },
        }
    }
}

/// Search for the leaf with the maximum key, by lexicographic ordering.
///
/// # Safety
///
///   - This function cannot be called concurrently to any reads or writes of
///     `root` or any child node of `root`. This function will arbitrarily read
///     to any child in the given tree.
pub unsafe fn maximum_unchecked<V>(root: OpaqueNodePtr<V>) -> Option<NodePtr<LeafNode<V>>> {
    let mut current_node = root;

    loop {
        match current_node.to_node_ptr() {
            InnerNodePtr::Node4(inner_node) => {
                let inner_node = inner_node.read();
                current_node = inner_node.iter().last()?.1;
            },
            InnerNodePtr::Node16(inner_node) => {
                let inner_node = inner_node.read();
                current_node = inner_node.iter().last()?.1;
            },
            InnerNodePtr::Node48(inner_node) => {
                let inner_node = inner_node.read();
                current_node = inner_node.iter().last()?.1;
            },
            InnerNodePtr::Node256(inner_node) => {
                let inner_node = inner_node.read();
                current_node = inner_node.iter().last()?.1;
            },
            InnerNodePtr::LeafNode(inner_node) => {
                return Some(inner_node);
            },
        }
    }
}

#[cfg(test)]
mod lookup_tests;

#[cfg(test)]
mod insert_tests;

#[cfg(test)]
mod minmax_tests;
