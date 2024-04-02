use crate::{
    AsBytes, ConcreteNodePtr, Header, InnerNode, InnerNode4, LeafNode, MatchPrefix, Mismatch,
    NodePtr, OpaqueNodePtr, TreeMap,
};
use std::{
    borrow::Borrow,
    error::Error,
    fmt,
    intrinsics::{assume, likely, unlikely},
    mem::ManuallyDrop,
    ops::ControlFlow,
};

/// The results of a successful tree insert
#[derive(Debug)]
pub struct InsertResult<'a, K: AsBytes, V> {
    /// Mutable reference for the newly inserted value
    pub new_value_ref: &'a mut V,
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
pub struct InsertPoint<K: AsBytes, V> {
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
    /// Current root of the tree, used in the apply
    pub root: OpaqueNodePtr<K, V>,
}

impl<K: AsBytes, V> InsertPoint<K, V> {
    pub fn apply<'a>(self, key: K, value: V) -> InsertResult<'a, K, V>
    where
        K: AsBytes,
    {
        unsafe fn create_value_ref<'a, 'b, K: AsBytes, V>(
            leaf: NodePtr<LeafNode<K, V>>,
        ) -> &'b mut V {
            unsafe { &mut *(leaf.as_value_mut() as *mut _) }
        }

        fn write_new_child_in_existing_node<'a, K, V>(
            inner_node_ptr: OpaqueNodePtr<K, V>,
            new_leaf_node: LeafNode<K, V>,
            key_bytes_used: usize,
        ) -> (OpaqueNodePtr<K, V>, &'a mut V)
        where
            K: AsBytes,
        {
            fn write_new_child_in_existing_inner_node<'a, K, V, N>(
                inner_node_ptr: NodePtr<N>,
                new_leaf_node: LeafNode<K, V>,
                key_bytes_used: usize,
            ) -> (OpaqueNodePtr<K, V>, &'a mut V)
            where
                N: InnerNode<Key = K, Value = V>,
                K: AsBytes,
            {
                // SAFETY: The `inner_node` reference lasts only for the duration of this
                // function, and the node will not be read or written via any other source
                // because of the safety requirements on `insert_unchecked`.
                let inner_node = unsafe { inner_node_ptr.as_mut() };
                let new_leaf_key_byte = new_leaf_node.key_ref().as_bytes()[key_bytes_used];
                let new_leaf_ptr = NodePtr::allocate_node_ptr(new_leaf_node);
                let new_value_ref = unsafe { create_value_ref(new_leaf_ptr) };
                let new_leaf_ptr = new_leaf_ptr.to_opaque();
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
                        #[allow(clippy::drop_ref)]
                        drop(inner_node);
                        drop(NodePtr::deallocate_node_ptr(inner_node_ptr));
                    };

                    (new_inner_node, new_value_ref)
                } else {
                    inner_node.write_child(new_leaf_key_byte, new_leaf_ptr);

                    (inner_node_ptr.to_opaque(), new_value_ref)
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
        fn parent_write_child<K: AsBytes, V>(
            parent_inner_node: OpaqueNodePtr<K, V>,
            key_byte: u8,
            new_child: OpaqueNodePtr<K, V>,
        ) {
            fn write_inner_node<K: AsBytes, V, N>(
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
                ConcreteNodePtr::Node4(inner_ptr) => {
                    write_inner_node(inner_ptr, key_byte, new_child)
                },
                ConcreteNodePtr::Node16(inner_ptr) => {
                    write_inner_node(inner_ptr, key_byte, new_child)
                },
                ConcreteNodePtr::Node48(inner_ptr) => {
                    write_inner_node(inner_ptr, key_byte, new_child)
                },
                ConcreteNodePtr::Node256(inner_ptr) => {
                    write_inner_node(inner_ptr, key_byte, new_child)
                },
                ConcreteNodePtr::LeafNode(_) => {
                    panic!("A leaf pointer cannot be the parent of another node")
                },
            }
        }

        let InsertPoint {
            parent_ptr_and_child_key_byte,
            insert_type,
            key_bytes_used,
            root,
        } = self;

        let (new_inner_node, new_value_ref) = match insert_type {
            InsertSearchResultType::MismatchPrefix {
                mismatch,
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
                let header = unsafe { mismatched_inner_node_ptr.header_mut_uncheked() };
                let key_byte = key.as_bytes()[key_bytes_used + mismatch.matched_bytes];

                let new_leaf_pointer = NodePtr::allocate_node_ptr(LeafNode::new(key, value));
                let new_value_ref = unsafe { create_value_ref(new_leaf_pointer) };
                let new_leaf_pointer = new_leaf_pointer.to_opaque();

                // prefix mismatch, need to split prefix into two separate nodes and take the
                // common prefix into a new parent node
                let prefix = &header.read_prefix();
                let prefix = &prefix[..prefix.len().min(mismatch.matched_bytes)];
                let mut new_n4 =
                    InnerNode4::from_prefix(prefix, mismatch.matched_bytes);

                unsafe {
                    // write the old node and new leaf in order
                    if mismatch.prefix_byte < key_byte {
                        new_n4.write_child_unchecked(mismatch.prefix_byte, mismatched_inner_node_ptr);
                        new_n4.write_child_unchecked(key_byte, new_leaf_pointer);
                    } else {
                        new_n4.write_child_unchecked(key_byte, new_leaf_pointer);
                        new_n4.write_child_unchecked(mismatch.prefix_byte, mismatched_inner_node_ptr);
                    }
                }
                // In this case we trim the current prefix, by skipping the matched bytes + 1
                // This + 1 is due to that one extra byte is used as key in the new node, so
                // we also need to remove it from the prefix
                let shrink_len = mismatch.matched_bytes + 1;
                match mismatch.leaf_ptr {
                    Some(leaf_ptr) => {
                        header.ltrim_by_with_leaf(shrink_len, key_bytes_used, leaf_ptr)
                    },
                    None => {
                        header.ltrim_by(shrink_len);
                    },
                }

                (
                    NodePtr::allocate_node_ptr(new_n4).to_opaque(),
                    new_value_ref,
                )
            },
            InsertSearchResultType::Exact { leaf_node_ptr } => {
                let new_leaf_node = LeafNode::new(key, value);
                // SAFETY: The leaf node will not be accessed concurrently because of the safety
                // doc on the containing function
                // TODO: Is this right ?
                let old_leaf_node = unsafe { NodePtr::replace(leaf_node_ptr, new_leaf_node) };
                return InsertResult {
                    new_value_ref: unsafe { create_value_ref(leaf_node_ptr) },
                    existing_leaf: Some(old_leaf_node),
                    // Because we replaced the leaf instead of creating a new leaf, we don't
                    // have to write back to the parent. In this case,
                    // the root is guaranteed to be unchanged, even if
                    // the old leaf was the root.
                    new_root: root,
                };
            },
            InsertSearchResultType::SplitLeaf {
                leaf_node_ptr,
                new_key_bytes_used,
            } => {
                let key_bytes = key.as_bytes();
                let leaf_bytes = unsafe { leaf_node_ptr.as_key_ref().as_bytes() };
                unsafe {
                    // SAFETY: When reaching this point in the insertion proccess this invarants
                    // should always be true, due to the check of [`InsertPrefixError`] which 
                    // guarantees that the amount of bytes used is always < len of the key or key in the leaf
                    // if this was not true, then a [`InsertPrefixError`] would already be triggered
                    assume(key_bytes_used < leaf_bytes.len());
                    assume(key_bytes_used < key_bytes.len());
                    assume(new_key_bytes_used < leaf_bytes.len());
                    assume(new_key_bytes_used < key_bytes.len());

                    // SAFETY: This is safe by construction, since new_key_bytes_used = key_bytes_used + x
                    assume(key_bytes_used <= new_key_bytes_used);
                }

                let mut new_n4 =
                    InnerNode4::from_prefix(&key_bytes[key_bytes_used..new_key_bytes_used], new_key_bytes_used - key_bytes_used);

                let leaf_node_key_byte = leaf_bytes[new_key_bytes_used];
                let new_leaf_node_key_byte = key_bytes[new_key_bytes_used];
                let new_leaf_node_pointer = NodePtr::allocate_node_ptr(LeafNode::new(key, value));
                let new_value_ref = unsafe { create_value_ref(new_leaf_node_pointer) };

                unsafe {
                    if leaf_node_key_byte < new_leaf_node_key_byte {
                        new_n4.write_child_unchecked(leaf_node_key_byte, leaf_node_ptr.to_opaque());
                        new_n4.write_child_unchecked(
                            new_leaf_node_key_byte,
                            new_leaf_node_pointer.to_opaque(),
                        );
                    } else {
                        new_n4.write_child_unchecked(
                            new_leaf_node_key_byte,
                            new_leaf_node_pointer.to_opaque(),
                        );
                        new_n4.write_child_unchecked(leaf_node_key_byte, leaf_node_ptr.to_opaque());
                    }
                }

                (
                    NodePtr::allocate_node_ptr(new_n4).to_opaque(),
                    new_value_ref,
                )
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
            InsertResult {
                new_value_ref,
                existing_leaf: None,
                new_root: root,
            }
        } else {
            // If there was no parent, then the root node was a leaf or the inner node split
            // occurred at the root, in which case return the new inner node as root
            InsertResult {
                new_value_ref,
                existing_leaf: None,
                new_root: new_inner_node,
            }
        }
    }
}

/// The type of insert
pub enum InsertSearchResultType<K: AsBytes, V> {
    /// An insert where an inner node had a differing prefix from the key.
    ///
    /// This insert type will create a new inner node with the portion of
    /// the prefix that did match, and update the existing inner node
    MismatchPrefix {
        /// Data about the matching if the prefix
        mismatch: Mismatch<K, V>,
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
        new_key_bytes_used: usize,
    },
    /// Exact match of the leaf was found
    ///
    /// This insert type will replace the older leaf with a new one
    Exact {
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

impl<K: AsBytes, V> fmt::Debug for InsertSearchResultType<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchPrefix {
                mismatch,
                mismatched_inner_node_ptr,
            } => f
                .debug_struct("MismatchPrefix")
                // TODO: Fix this
                // .field("mismatch", mismatch)
                .field("mismatched_inner_node_ptr", mismatched_inner_node_ptr)
                .finish(),
            Self::SplitLeaf {
                leaf_node_ptr,
                new_key_bytes_used,
            } => f
                .debug_struct("SplitLeaf")
                .field("leaf_node_ptr", leaf_node_ptr)
                .field("new_key_bytes_used", new_key_bytes_used)
                .finish(),
            Self::Exact { leaf_node_ptr } => f
                .debug_struct("Exact")
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
pub unsafe fn search_for_insert_point<K, V, Q>(
    root: OpaqueNodePtr<K, V>,
    key: &Q,
) -> Result<InsertPoint<K, V>, InsertPrefixError>
where
    K: AsBytes + Borrow<Q>,
    Q: AsBytes + ?Sized,
{
    fn test_prefix_identify_insert<K, V, N, Q>(
        inner_ptr: NodePtr<N>,
        key: &Q,
        current_depth: &mut usize,
    ) -> Result<ControlFlow<Mismatch<K, V>, Option<OpaqueNodePtr<K, V>>>, InsertPrefixError>
    where
        N: InnerNode<Key = K, Value = V>,
        K: AsBytes + Borrow<Q>,
        Q: AsBytes + ?Sized,
    {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `search_unchecked` function.
        let inner_node = unsafe { inner_ptr.as_ref() };
        let match_prefix = inner_node.match_prefix(key.as_bytes(), *current_depth);
        match match_prefix {
            MatchPrefix::Mismatch { mismatch } => Ok(ControlFlow::Break(mismatch)),
            MatchPrefix::Match { matched_bytes } => {
                // Since the prefix matched, advance the depth by the size of the prefix
                *current_depth += matched_bytes;

                if likely(*current_depth < key.as_bytes().len()) {
                    let next_key_fragment =
                        unsafe { *key.as_bytes().get_unchecked(*current_depth) };
                    Ok(ControlFlow::Continue(
                        inner_node.lookup_child(next_key_fragment),
                    ))
                } else {
                    // then the key has insufficient bytes to be unique. It must be
                    // a prefix of an existing key
                    Err(InsertPrefixError {
                        byte_repr: key.as_bytes().into(),
                    })
                }
            },
        }
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
                let leaf_node = leaf_node_ptr.read();

                if leaf_node.matches_full_key(&key) {
                    return Ok(InsertPoint {
                        key_bytes_used: current_depth,
                        parent_ptr_and_child_key_byte: current_parent,
                        insert_type: InsertSearchResultType::Exact { leaf_node_ptr },
                        root,
                    });
                }

                let key_bytes = key.as_bytes();
                let leaf_bytes = leaf_node.key_ref().as_bytes();
                unsafe {
                    // SAFETY: The [`test_prefix_identify_insert`] checks for [`InsertPrefixError`]
                    // which would lead to this not holding, but since it already checked we know
                    // that current_depth < len of the key and the key in the leaf. But there is an
                    // edge case, if the root of the tree is a leaf than the depth can be = len
                    assume(current_depth <= leaf_bytes.len());
                    assume(current_depth <= key_bytes.len());
                }

                let prefix_size = leaf_bytes[current_depth..]
                    .iter()
                    .zip(key_bytes[current_depth..].iter())
                    .take_while(|(k1, k2)| k1 == k2)
                    .count();

                let new_key_bytes_used = current_depth + prefix_size;

                if unlikely(
                    new_key_bytes_used >= key_bytes.len()
                        || new_key_bytes_used >= leaf_bytes.len(),
                ) {
                    // then the key has insufficient bytes to be unique. It must be
                    // a prefix of an existing key OR an existing key is a prefix of it
                    // println!("{key_bytes:?}");
                    return Err(InsertPrefixError {
                        byte_repr: key_bytes.into(),
                    });
                }

                return Ok(InsertPoint {
                    key_bytes_used: current_depth,
                    parent_ptr_and_child_key_byte: current_parent,
                    insert_type: InsertSearchResultType::SplitLeaf {
                        leaf_node_ptr,
                        new_key_bytes_used,
                    },
                    root,
                });
            },
        }?;

        unsafe {
            // SAFETY: The [`test_prefix_identify_insert`] checks for [`InsertPrefixError`]
            // which would lead to this not holding, but since it already checked we know
            // that current_depth < len of the key and the key in the leaf. And also the
            // only edge case can occur in the Leaf node, but if we reach a leaf not the
            // function returns early, so it's impossible to be <=
            assume(current_depth < key.as_bytes().len());
        }
        match lookup_result {
            ControlFlow::Continue(next_child_node) => {
                match next_child_node {
                    Some(next_child_node) => {
                        let byte = key.as_bytes()[current_depth];
                        current_parent = Some((current_node, byte));
                        current_node = next_child_node;
                        // Increment by a single byte
                        current_depth += 1;
                    },
                    None => {
                        return Ok(InsertPoint {
                            key_bytes_used: current_depth,
                            insert_type: InsertSearchResultType::IntoExisting {
                                inner_node_ptr: current_node,
                            },
                            parent_ptr_and_child_key_byte: current_parent,
                            root,
                        })
                    },
                }
            },
            ControlFlow::Break(mismatch) => {
                if unlikely((current_depth + mismatch.matched_bytes) >= key.as_bytes().len()) {
                    // then the key has insufficient bytes to be unique. It must be
                    // a prefix of an existing key

                    return Err(InsertPrefixError {
                        byte_repr: key.as_bytes().into(),
                    });
                }

                return Ok(InsertPoint {
                    key_bytes_used: current_depth,
                    insert_type: InsertSearchResultType::MismatchPrefix {
                        mismatch,
                        mismatched_inner_node_ptr: current_node,
                    },
                    parent_ptr_and_child_key_byte: current_parent,
                    root,
                });
            },
        };
    }
}

#[cfg(test)]
mod tests;
