use super::lookup;
use crate::{ConcreteNodePtr, InnerNode, InnerNode4, LeafNode, NodePtr, OpaqueNodePtr};
use std::{error::Error, fmt};

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
///    tree
///  - This function cannot be called concurrently to any reads or writes of the
///    `root` node or any child node of `root`. This function will arbitrarily
///    read or write to any child in the given tree.
pub unsafe fn insert_unchecked<V>(
    root: OpaqueNodePtr<V>,
    key: Box<[u8]>,
    value: V,
) -> Result<OpaqueNodePtr<V>, InsertError> {
    fn write_new_child_in_existing_node<V>(
        inner_node_ptr: OpaqueNodePtr<V>,
        new_leaf_node: LeafNode<V>,
        key_bytes_used: usize,
    ) -> OpaqueNodePtr<V> {
        fn write_new_child_in_existing_inner_node<V, N: InnerNode<Value = V>>(
            inner_node_ptr: NodePtr<N>,
            new_leaf_node: LeafNode<V>,
            key_bytes_used: usize,
        ) -> OpaqueNodePtr<V> {
            // SAFETY: The `inner_node` reference lasts only for the duration of this
            // function, and the node will not be read or written via any other source
            // because of the safety requirements on `insert_unchecked`.
            let inner_node = unsafe { inner_node_ptr.as_mut() };
            let new_leaf_key_byte = new_leaf_node.key[key_bytes_used];
            let new_leaf_ptr = NodePtr::allocate_node(new_leaf_node).to_opaque();
            if inner_node.is_full() {
                // we will create a new node of the next larger type and copy all the
                // children over.

                let mut new_node = inner_node.grow();
                new_node.write_child(new_leaf_key_byte, new_leaf_ptr);

                let new_inner_node = NodePtr::allocate_node(new_node).to_opaque();

                // SAFETY: The `deallocate_node` function is only called a
                // single time. The uniqueness requirement is passed up to the
                // `grow_unchecked` safety requirements.
                //
                // Also, the `inner_node` mutable reference is invalid in this scope after this
                // node is deallocated and must not be used.
                unsafe {
                    NodePtr::deallocate_node(inner_node_ptr);
                };

                new_inner_node
            } else {
                inner_node.write_child(new_leaf_key_byte, new_leaf_ptr);

                inner_node_ptr.to_opaque()
            }
        }

        match inner_node_ptr.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => {
                write_new_child_in_existing_inner_node(inner_ptr, new_leaf_node, key_bytes_used)
            },
            ConcreteNodePtr::Node16(inner_ptr) => {
                write_new_child_in_existing_inner_node(inner_ptr, new_leaf_node, key_bytes_used)
            },
            ConcreteNodePtr::Node48(inner_ptr) => {
                write_new_child_in_existing_inner_node(inner_ptr, new_leaf_node, key_bytes_used)
            },
            ConcreteNodePtr::Node256(inner_ptr) => {
                write_new_child_in_existing_inner_node(inner_ptr, new_leaf_node, key_bytes_used)
            },
            ConcreteNodePtr::LeafNode(_) => {
                panic!("Cannot have insert into existing with leaf node")
            },
        }
    }

    /// Write a new child node to an inner node at the specified key byte.
    fn parent_write_child<V>(
        parent_inner_node: OpaqueNodePtr<V>,
        key_byte: u8,
        new_child: OpaqueNodePtr<V>,
    ) {
        fn write_inner_node<V, N: InnerNode<Value = V>>(
            parent_inner_node: NodePtr<N>,
            key_byte: u8,
            new_child: OpaqueNodePtr<V>,
        ) {
            // SAFETY: The lifetime produced from this is bounded to this scope and does not
            // escape. Further, no other code mutates the node referenced, which is further
            // enforced the "no concurrent reads or writes" requirement on the
            // `maximum_unchecked` function.
            let parent_node = unsafe { parent_inner_node.as_mut() };

            parent_node.write_child(key_byte, new_child)
        }

        match parent_inner_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => write_inner_node(inner_ptr, key_byte, new_child),
            ConcreteNodePtr::Node16(inner_ptr) => write_inner_node(inner_ptr, key_byte, new_child),
            ConcreteNodePtr::Node48(inner_ptr) => write_inner_node(inner_ptr, key_byte, new_child),
            ConcreteNodePtr::Node256(inner_ptr) => write_inner_node(inner_ptr, key_byte, new_child),
            ConcreteNodePtr::LeafNode(_) => {
                panic!("A leaf pointer cannot be the parent of another node")
            },
        }
    }

    if key.is_empty() {
        return Err(InsertError::EmptyKey);
    }

    let lookup::InsertSearchResult {
        parent_ptr_and_child_key_byte,
        insert_type,
        mut key_bytes_used,
    } = lookup::search_for_insert_point(root, key.as_ref())?;

    let new_inner_node = match insert_type {
        lookup::InsertSearchResultType::MismatchPrefix {
            matched_prefix_size,
            mismatched_inner_node_ptr,
        } => {
            // SAFETY: The lifetime of the header reference is restricted to this block and
            // within the block no other access occurs. The requirements of
            // the "no concurrent (read or write) access" is also enforced by the
            // `insert_unchecked` caller requirements.
            //
            // PANIC SAFETY: This is guaranteed not to panic because the `MismatchPrefix`
            // variant is only returned in cases where there was a mismatch in the header
            // prefix, implying that the header is present.
            let header = unsafe { mismatched_inner_node_ptr.header_mut().unwrap() };

            if (key_bytes_used + matched_prefix_size) >= key.len() {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key

                return Err(InsertError::PrefixKey(key));
            }

            let new_leaf_key_byte = key[key_bytes_used + matched_prefix_size];

            let new_leaf_pointer = NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque();

            // prefix mismatch, need to split prefix into two separate nodes and take the
            // common prefix into a new parent node
            let mut new_n4 = InnerNode4::empty();

            new_n4.write_child(
                header.read_prefix()[matched_prefix_size],
                mismatched_inner_node_ptr,
            );
            new_n4.write_child(new_leaf_key_byte, new_leaf_pointer);

            new_n4
                .header
                .write_prefix(&header.read_prefix()[..matched_prefix_size]);
            header.ltrim_prefix(matched_prefix_size + 1);

            NodePtr::allocate_node(new_n4).to_opaque()
        },
        lookup::InsertSearchResultType::SplitLeaf { leaf_node_ptr } => {
            let leaf_node = leaf_node_ptr.read();

            let mut new_n4 = InnerNode4::empty();
            let prefix_size = leaf_node.key[key_bytes_used..]
                .iter()
                .zip(key[key_bytes_used..].iter())
                .take_while(|(k1, k2)| k1 == k2)
                .count();
            new_n4
                .header
                .write_prefix(&key[key_bytes_used..(key_bytes_used + prefix_size)]);
            key_bytes_used += prefix_size;

            if key_bytes_used >= key.len() || key_bytes_used >= leaf_node.key.len() {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key OR an existing key is a prefix of it

                return Err(InsertError::PrefixKey(key));
            }

            let new_leaf_key_byte = key[key_bytes_used];
            let new_leaf_pointer = NodePtr::allocate_node(LeafNode::new(key, value));

            new_n4.write_child(leaf_node.key[key_bytes_used], leaf_node_ptr.to_opaque());
            new_n4.write_child(new_leaf_key_byte, new_leaf_pointer.to_opaque());

            NodePtr::allocate_node(new_n4).to_opaque()
        },
        lookup::InsertSearchResultType::IntoExisting { inner_node_ptr } => {
            write_new_child_in_existing_node(
                inner_node_ptr,
                LeafNode::new(key, value),
                key_bytes_used,
            )
        },
    };

    if let Some((parent_ptr, parent_key_fragment)) = parent_ptr_and_child_key_byte {
        parent_write_child(parent_ptr, parent_key_fragment, new_inner_node);

        // If there was a parent either:
        //   1. Root was the parent, in which case it was unchanged
        //   2. Or some parent of the parent was root, in which case it was unchanged
        Ok(root)
    } else {
        // If there was no parent, then the root node was a leaf or the inner node split
        // occurred at the root, in which case return the new inner node as root
        Ok(new_inner_node)
    }
}

/// The error type for the insert operation on the tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InsertError {
    /// Attempted to insert an empty key.
    EmptyKey,
    /// Attempted to insert a key which was a prefix of an existing key in
    /// the tree.
    PrefixKey(Box<[u8]>),
}

impl fmt::Display for InsertError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

#[cfg(test)]
mod tests;
