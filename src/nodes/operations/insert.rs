use crate::{ConcreteNodePtr, InnerNode, InnerNode4, LeafNode, NodePtr, OpaqueNodePtr};
use std::{error::Error, fmt, ops::ControlFlow};

/// This struct contains the results from searching for an insert point for
/// a new node in the tree.
///
/// It contains all the relevant information needed to perform the insert
/// and update the tree.
pub(crate) struct InsertSearchResult<V> {
    /// The parent node pointer and key byte that points to the main node
    /// insert point.
    ///
    /// In the case that the root node is the main insert point, this will
    /// have a `None` value.
    pub(crate) parent_ptr_and_child_key_byte: Option<(OpaqueNodePtr<V>, u8)>,
    /// The type of operation that needs to be performed to insert the key
    pub(crate) insert_type: InsertSearchResultType<V>,
    /// The number of bytes that were read from the key to find the insert
    /// point.
    pub(crate) key_bytes_used: usize,
}

/// The type of insert
pub(crate) enum InsertSearchResultType<V> {
    /// An insert where an inner node had a differing prefix from the key.
    ///
    /// This insert type will create a new inner node with the portion of
    /// the prefix that did match, and update the existing inner node
    MismatchPrefix {
        matched_prefix_size: usize,
        mismatched_inner_node_ptr: OpaqueNodePtr<V>,
    },
    /// An insert where the node to be added matched all the way up to a
    /// leaf node.
    ///
    /// This insert type will create a new inner node, and assign the
    /// existing leaf and the new leaf as children to that node.
    SplitLeaf { leaf_node_ptr: NodePtr<LeafNode<V>> },
    /// An insert where the search terminated at an existing inner node that
    /// did not have a child with the key byte.
    ///
    /// If the inner node is full, it will be grown to the next largest
    /// size.
    IntoExisting { inner_node_ptr: OpaqueNodePtr<V> },
}

impl<V> fmt::Debug for InsertSearchResultType<V> {
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
pub(crate) fn search_for_insert_point<V>(
    root: OpaqueNodePtr<V>,
    key: &[u8],
) -> Result<InsertSearchResult<V>, InsertPrefixError> {
    fn test_prefix_identify_insert<V, N: InnerNode<Value = V>>(
        inner_ptr: NodePtr<N>,
        key: &[u8],
        current_depth: &mut usize,
    ) -> Result<ControlFlow<usize, Option<OpaqueNodePtr<V>>>, InsertPrefixError> {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `search_unchecked` function.
        let inner_node = unsafe { inner_ptr.as_ref() };
        let header = inner_node.header();
        let matched_prefix_size = header.match_prefix(&key[*current_depth..]);
        if matched_prefix_size != header.prefix_size() {
            return Ok(ControlFlow::Break(matched_prefix_size));
        }

        // Since the prefix matched, advance the depth by the size of the prefix
        *current_depth += matched_prefix_size;

        let next_key_fragment = if *current_depth < key.len() {
            key[*current_depth]
        } else {
            // then the key has insufficient bytes to be unique. It must be
            // a prefix of an existing key

            return Err(InsertPrefixError(Box::from(key)));
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
                        current_parent = Some((current_node, key[current_depth]));
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

/// Insert the given key-value pair into the tree.
///
/// Returns either a pointer to the new tree root or an error.
///
/// # Errors
///
///   - Returns a [`InsertPrefixError`] if the given key is a prefix of another
///     key that exists in the trie. Or if the given key is prefixed by an
///     existing key in the trie.
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
) -> Result<OpaqueNodePtr<V>, InsertPrefixError> {
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
            let new_leaf_ptr = NodePtr::allocate_node_ptr(new_leaf_node).to_opaque();
            if inner_node.is_full() {
                // we will create a new node of the next larger type and copy all the
                // children over.

                let mut new_node = inner_node.grow();
                new_node.write_child(new_leaf_key_byte, new_leaf_ptr);

                let new_inner_node = NodePtr::allocate_node_ptr(new_node).to_opaque();

                // SAFETY: The `deallocate_node` function is only called a
                // single time. The uniqueness requirement is passed up to the
                // `grow_unchecked` safety requirements.
                #[allow(clippy::drop_ref)]
                unsafe {
                    drop(inner_node);
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

    let InsertSearchResult {
        parent_ptr_and_child_key_byte,
        insert_type,
        mut key_bytes_used,
    } = search_for_insert_point(root, key.as_ref())?;

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

            if (key_bytes_used + matched_prefix_size) >= key.len() {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key

                return Err(InsertPrefixError(key));
            }

            let new_leaf_key_byte = key[key_bytes_used + matched_prefix_size];

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

            let mut new_n4 = InnerNode4::empty();
            let prefix_size = leaf_node.key[key_bytes_used..]
                .iter()
                .zip(key[key_bytes_used..].iter())
                .take_while(|(k1, k2)| k1 == k2)
                .count();
            new_n4
                .header
                .extend_prefix(&key[key_bytes_used..(key_bytes_used + prefix_size)]);
            key_bytes_used += prefix_size;

            if key_bytes_used >= key.len() || key_bytes_used >= leaf_node.key.len() {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key OR an existing key is a prefix of it

                return Err(InsertPrefixError(key));
            }

            let new_leaf_key_byte = key[key_bytes_used];
            let new_leaf_pointer = NodePtr::allocate_node_ptr(LeafNode::new(key, value));

            new_n4.write_child(leaf_node.key[key_bytes_used], leaf_node_ptr.to_opaque());
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

/// Attempted to insert a key which was a prefix of an existing key in
/// the tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InsertPrefixError(
    /// The key that was the input to the [`insert_unchecked`] operation
    pub Box<[u8]>,
);

impl fmt::Display for InsertPrefixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Attempted to insert a key [{:?}] which is either a prefix of an existing key or an \
             existing key is a prefix of the new key.",
            self.0
        )
    }
}

impl Error for InsertPrefixError {}

#[cfg(test)]
mod tests;
