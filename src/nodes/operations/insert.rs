use crate::{AsBytes, ConcreteNodePtr, InnerNode, InnerNode4, LeafNode, NodePtr, OpaqueNodePtr};
use std::{error::Error, fmt, ops::ControlFlow};

/// Insert the given key-value pair into the tree.
///
/// Returns either a pointer to the new tree root or an error.
///
/// If the given key already exists in the tree, the old key and value will be
/// replaced and be returned.
///
/// # Errors
///
///   - Returns a [`InsertPrefixError<K>`] if the given key is a prefix of
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
pub unsafe fn insert_unchecked<K, V>(
    root: OpaqueNodePtr<K, V>,
    key: K,
    value: V,
) -> Result<InsertResult<K, V>, InsertPrefixError>
where
    K: AsBytes,
{
    fn write_new_child_in_existing_node<K, V>(
        inner_node_ptr: OpaqueNodePtr<K, V>,
        new_leaf_node: LeafNode<K, V>,
        key_bytes_used: usize,
    ) -> OpaqueNodePtr<K, V>
    where
        K: AsBytes,
    {
        fn write_new_child_in_existing_inner_node<K, V, N>(
            inner_node_ptr: NodePtr<N>,
            new_leaf_node: LeafNode<K, V>,
            key_bytes_used: usize,
        ) -> OpaqueNodePtr<K, V>
        where
            N: InnerNode<Key = K, Value = V>,
            K: AsBytes,
        {
            // SAFETY: The `inner_node` reference lasts only for the duration of this
            // function, and the node will not be read or written via any other source
            // because of the safety requirements on `insert_unchecked`.
            let inner_node = unsafe { inner_node_ptr.as_mut() };
            let new_leaf_key_byte = new_leaf_node.key_ref().as_bytes()[key_bytes_used];
            let new_leaf_ptr = NodePtr::allocate_node_ptr(new_leaf_node).to_opaque();
            if inner_node.is_full() {
                // we will create a new node of the next larger type and copy all the
                // children over.

                let mut new_node = inner_node.grow();
                new_node.write_child(new_leaf_key_byte, new_leaf_ptr);

                let new_inner_node = NodePtr::allocate_node_ptr(new_node).to_opaque();

                // SAFETY: The `deallocate_node` function is only called a
                // single time. The uniqueness requirement is passed up to the
                // `insert_unchecked` safety requirements.
                unsafe {
                    // Do not use the `inner_node` mutable reference after this point in this block,
                    // since the node has been deallocated
                    drop(NodePtr::deallocate_node_ptr(inner_node_ptr));
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
    fn parent_write_child<K, V>(
        parent_inner_node: OpaqueNodePtr<K, V>,
        key_byte: u8,
        new_child: OpaqueNodePtr<K, V>,
    ) {
        fn write_inner_node<K, V, N>(
            parent_inner_node: NodePtr<N>,
            key_byte: u8,
            new_child: OpaqueNodePtr<K, V>,
        ) where
            N: InnerNode<Key = K, Value = V>,
        {
            // SAFETY: The lifetime produced from this is bounded to this scope and does not
            // escape. Further, no other code mutates the node referenced, which is further
            // enforced the "no concurrent reads or writes" requirement on the
            // `maximum_unchecked` function.
            let parent_node = unsafe { parent_inner_node.as_mut() };

            parent_node.write_child(key_byte, new_child);
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

    // SAFETY: Requirements covered by containing function
    let InsertSearchResult {
        parent_ptr_and_child_key_byte,
        insert_type,
        mut key_bytes_used,
    } = unsafe { search_for_insert_point(root, &key)? };

    let new_inner_node = match insert_type {
        InsertSearchResultType::MismatchPrefix {
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

            if (key_bytes_used + matched_prefix_size) >= key.as_bytes().len() {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key

                return Err(InsertPrefixError {
                    byte_repr: key.as_bytes().into(),
                });
            }

            let new_leaf_key_byte = key.as_bytes()[key_bytes_used + matched_prefix_size];

            let new_leaf_pointer =
                NodePtr::allocate_node_ptr(LeafNode::new(key, value)).to_opaque();

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
                .extend_prefix(&header.read_prefix()[..matched_prefix_size]);
            header.ltrim_prefix(matched_prefix_size + 1);

            NodePtr::allocate_node_ptr(new_n4).to_opaque()
        },
        InsertSearchResultType::SplitLeaf { leaf_node_ptr } => {
            let leaf_node = leaf_node_ptr.read();

            if leaf_node.matches_full_key(&key) {
                // This means that the key provided exactly matched the existing leaf key, so we
                // will simply replace the contents of the leaf node.

                let new_leaf_node = LeafNode::new(key, value);
                // SAFETY: The leaf node will not be accessed concurrently because of the safety
                // doc on the containing function
                let old_leaf_node = unsafe { NodePtr::replace(leaf_node_ptr, new_leaf_node) };
                return Ok(InsertResult {
                    existing_leaf: Some(old_leaf_node),
                    // Because we replaced the leaf instead of creating a new leaf, we don't have to
                    // write back to the parent. In this case, the root is guaranteed to be
                    // unchanged, even if the old leaf was the root.
                    new_root: root,
                });
            }

            let mut new_n4 = InnerNode4::empty();
            let prefix_size = leaf_node.key_ref().as_bytes()[key_bytes_used..]
                .iter()
                .zip(key.as_bytes()[key_bytes_used..].iter())
                .take_while(|(k1, k2)| k1 == k2)
                .count();
            new_n4
                .header
                .extend_prefix(&key.as_bytes()[key_bytes_used..(key_bytes_used + prefix_size)]);
            key_bytes_used += prefix_size;

            if key_bytes_used >= key.as_bytes().len()
                || key_bytes_used >= leaf_node.key_ref().as_bytes().len()
            {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key OR an existing key is a prefix of it

                return Err(InsertPrefixError {
                    byte_repr: key.as_bytes().into(),
                });
            }

            let new_leaf_key_byte = key.as_bytes()[key_bytes_used];
            let new_leaf_pointer = NodePtr::allocate_node_ptr(LeafNode::new(key, value));

            new_n4.write_child(
                leaf_node.key_ref().as_bytes()[key_bytes_used],
                leaf_node_ptr.to_opaque(),
            );
            new_n4.write_child(new_leaf_key_byte, new_leaf_pointer.to_opaque());

            NodePtr::allocate_node_ptr(new_n4).to_opaque()
        },
        InsertSearchResultType::IntoExisting { inner_node_ptr } => {
            write_new_child_in_existing_node(
                inner_node_ptr,
                LeafNode::new(key, value),
                key_bytes_used,
            )
        },
    };

    if let Some((parent_ptr, parent_key_fragment)) = parent_ptr_and_child_key_byte {
        // TODO(#14) Change this write back to parent to only happen when a new inner
        // node is created (MismatchPrefix & SplitLeaf (when it is not an overwrite of
        // the existing leaf))
        parent_write_child(parent_ptr, parent_key_fragment, new_inner_node);

        // If there was a parent either:
        //   1. Root was the parent, in which case it was unchanged
        //   2. Or some parent of the parent was root, in which case it was unchanged
        Ok(InsertResult {
            existing_leaf: None,
            new_root: root,
        })
    } else {
        // If there was no parent, then the root node was a leaf or the inner node split
        // occurred at the root, in which case return the new inner node as root
        Ok(InsertResult {
            existing_leaf: None,
            new_root: new_inner_node,
        })
    }
}

/// The results of a successful tree insert
#[derive(Debug)]
pub struct InsertResult<K, V> {
    /// The existing leaf referenced by the insert key, if present
    pub existing_leaf: Option<LeafNode<K, V>>,
    /// The new tree root after the successful insert
    pub new_root: OpaqueNodePtr<K, V>,
}

/// Attempted to insert a key which was a prefix of an existing key in
/// the tree.
#[derive(Clone, PartialEq, Eq)]
pub struct InsertPrefixError {
    /// The key that was the input to the [`insert_unchecked`] operation
    pub byte_repr: Box<[u8]>,
}

impl fmt::Debug for InsertPrefixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InsertPrefixError")
            .field("byte_repr", &self.byte_repr)
            .finish()
    }
}

impl fmt::Display for InsertPrefixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Attempted to insert a key [{:?}] which is either a prefix of an existing key or an \
             existing key is a prefix of the new key.",
            self.byte_repr
        )
    }
}

impl Error for InsertPrefixError {}

/// This struct contains the results from searching for an insert point for
/// a new node in the tree.
///
/// It contains all the relevant information needed to perform the insert
/// and update the tree.
pub struct InsertSearchResult<K, V> {
    /// The parent node pointer and key byte that points to the main node
    /// insert point.
    ///
    /// In the case that the root node is the main insert point, this will
    /// have a `None` value.
    pub parent_ptr_and_child_key_byte: Option<(OpaqueNodePtr<K, V>, u8)>,
    /// The type of operation that needs to be performed to insert the key
    pub insert_type: InsertSearchResultType<K, V>,
    /// The number of bytes that were read from the key to find the insert
    /// point.
    pub key_bytes_used: usize,
}

/// The type of insert
pub enum InsertSearchResultType<K, V> {
    /// An insert where an inner node had a differing prefix from the key.
    ///
    /// This insert type will create a new inner node with the portion of
    /// the prefix that did match, and update the existing inner node
    MismatchPrefix {
        /// The number of key bytes that did match for the mismatched prefix
        matched_prefix_size: usize,
        /// A pointer to the inner node which had a mismatched prefix
        mismatched_inner_node_ptr: OpaqueNodePtr<K, V>,
    },
    /// An insert where the node to be added matched all the way up to a
    /// leaf node.
    ///
    /// This insert type will create a new inner node, and assign the
    /// existing leaf and the new leaf as children to that node.
    SplitLeaf {
        /// A pointer to the leaf node that will be split
        leaf_node_ptr: NodePtr<LeafNode<K, V>>,
    },
    /// An insert where the search terminated at an existing inner node that
    /// did not have a child with the key byte.
    ///
    /// If the inner node is full, it will be grown to the next largest
    /// size.
    IntoExisting {
        /// A pointer to the existing inner node which will be updated to
        /// contain the new child leaf node
        inner_node_ptr: OpaqueNodePtr<K, V>,
    },
}

impl<K, V> fmt::Debug for InsertSearchResultType<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchPrefix {
                matched_prefix_size,
                mismatched_inner_node_ptr,
            } => f
                .debug_struct("MismatchPrefix")
                .field("matched_prefix_size", matched_prefix_size)
                .field("mismatched_inner_node_ptr", mismatched_inner_node_ptr)
                .finish(),
            Self::SplitLeaf { leaf_node_ptr } => f
                .debug_struct("SplitLeaf")
                .field("leaf_node_ptr", leaf_node_ptr)
                .finish(),
            Self::IntoExisting { inner_node_ptr } => f
                .debug_struct("IntoExisting")
                .field("inner_node_ptr", inner_node_ptr)
                .finish(),
        }
    }
}

/// Perform an iterative search for the insert point for the given key,
/// starting at the given root node.
///
/// # Safety
///
///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the underlying
///    tree
///  - This function cannot be called concurrently to any reads or writes of the
///    `root` node or any child node of `root`. This function will arbitrarily
///    read or write to any child in the given tree.
///
/// # Errors
///
/// If the given `key` is a prefix of an existing key, this function will return
/// an error.
pub unsafe fn search_for_insert_point<K, V>(
    root: OpaqueNodePtr<K, V>,
    key: &K,
) -> Result<InsertSearchResult<K, V>, InsertPrefixError>
where
    K: AsBytes,
{
    fn test_prefix_identify_insert<K, V, N>(
        inner_ptr: NodePtr<N>,
        key: &K,
        current_depth: &mut usize,
    ) -> Result<ControlFlow<usize, Option<OpaqueNodePtr<K, V>>>, InsertPrefixError>
    where
        N: InnerNode<Key = K, Value = V>,
        K: AsBytes,
    {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `search_unchecked` function.
        let inner_node = unsafe { inner_ptr.as_ref() };
        let header = inner_node.header();
        let matched_prefix_size = header.match_prefix(&key.as_bytes()[*current_depth..]);
        if matched_prefix_size != header.prefix_len() {
            return Ok(ControlFlow::Break(matched_prefix_size));
        }

        // Since the prefix matched, advance the depth by the size of the prefix
        *current_depth += matched_prefix_size;

        let next_key_fragment = if *current_depth < key.as_bytes().len() {
            key.as_bytes()[*current_depth]
        } else {
            // then the key has insufficient bytes to be unique. It must be
            // a prefix of an existing key

            return Err(InsertPrefixError {
                byte_repr: key.as_bytes().into(),
            });
        };

        Ok(ControlFlow::Continue(
            inner_node.lookup_child(next_key_fragment),
        ))
    }

    let mut current_parent = None;
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        let lookup_result = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                return Ok(InsertSearchResult {
                    key_bytes_used: current_depth,
                    parent_ptr_and_child_key_byte: current_parent,
                    insert_type: InsertSearchResultType::SplitLeaf { leaf_node_ptr },
                });
            },
        }?;

        match lookup_result {
            ControlFlow::Continue(next_child_node) => {
                match next_child_node {
                    Some(next_child_node) => {
                        current_parent = Some((current_node, key.as_bytes()[current_depth]));
                        current_node = next_child_node;
                        // Increment by a single byte
                        current_depth += 1;
                    },
                    None => {
                        return Ok(InsertSearchResult {
                            key_bytes_used: current_depth,
                            insert_type: InsertSearchResultType::IntoExisting {
                                inner_node_ptr: current_node,
                            },
                            parent_ptr_and_child_key_byte: current_parent,
                        })
                    },
                }
            },
            ControlFlow::Break(matched_prefix_size) => {
                return Ok(InsertSearchResult {
                    key_bytes_used: current_depth,
                    insert_type: InsertSearchResultType::MismatchPrefix {
                        matched_prefix_size,
                        mismatched_inner_node_ptr: current_node,
                    },
                    parent_ptr_and_child_key_byte: current_parent,
                })
            },
        };
    }
}

#[cfg(test)]
mod tests;
