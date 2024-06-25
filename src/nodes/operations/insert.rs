use crate::{
    rust_nightly_apis::{assume, likely, unlikely},
    AsBytes, ConcreteNodePtr, InnerNode, InnerNode4, LeafNode, MatchPrefixResult, Mismatch,
    NodeHeader, NodePtr, OpaqueNodePtr,
};
use std::{borrow::Borrow, error::Error, fmt, marker::PhantomData, ops::ControlFlow};

/// The results of a successful tree insert
#[derive(Debug)]
pub struct InsertResult<
    'a,
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
> {
    /// Pointer to the leaf
    pub leaf_node_ptr: NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>,
    /// The existing leaf referenced by the insert key, if present
    pub existing_leaf: Option<LeafNode<K, V, NUM_PREFIX_BYTES, H>>,
    /// The new tree root after the successful insert
    pub new_root: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,

    pub marker: PhantomData<(&'a mut K, &'a V)>,
}

/// Attempted to insert a key which was a prefix of an existing key in
/// the tree.
#[derive(Clone, PartialEq, Eq)]
pub struct InsertPrefixError {
    /// The inserted key
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
pub struct InsertPoint<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
> {
    /// The grandparent node pointer and key byte that points to the parent node
    /// insert point.
    ///
    /// In the case that the root node is the main insert point, this will
    /// have a `None` value.
    ///
    /// # Note
    ///
    /// This is only used during the removal in the entry, and it's not a lot
    /// extra work or space to keep track
    pub grandparent_ptr_and_parent_key_byte: Option<(OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>, u8)>,
    /// The parent node pointer and key byte that points to the main node
    /// insert point.
    ///
    /// In the case that the root node is the main insert point, this will
    /// have a `None` value.
    pub parent_ptr_and_child_key_byte: Option<(OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>, u8)>,
    /// The type of operation that needs to be performed to insert the key
    pub insert_type: InsertSearchResultType<K, V, NUM_PREFIX_BYTES, H>,
    /// The number of bytes that were read from the key to find the insert
    /// point.
    pub key_bytes_used: usize,
    /// Current root of the tree, used in the apply
    pub root: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    InsertPoint<K, V, NUM_PREFIX_BYTES, H>
{
    pub fn apply<'a>(self, key: K, value: V) -> InsertResult<'a, K, V, NUM_PREFIX_BYTES, H>
    where
        K: AsBytes + 'a,
        V: 'a,
    {
        fn write_new_child_in_existing_node<
            'a,
            K,
            V,
            const NUM_PREFIX_BYTES: usize,
            H: NodeHeader<NUM_PREFIX_BYTES>,
        >(
            inner_node_ptr: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
            new_leaf_node: LeafNode<K, V, NUM_PREFIX_BYTES, H>,
            key_bytes_used: usize,
        ) -> (
            OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
            NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>,
        )
        where
            K: AsBytes + 'a,
            V: 'a,
        {
            fn write_new_child_in_existing_inner_node<
                'a,
                K,
                V,
                N,
                const NUM_PREFIX_BYTES: usize,
                H: NodeHeader<NUM_PREFIX_BYTES>,
            >(
                inner_node_ptr: NodePtr<NUM_PREFIX_BYTES, N>,
                new_leaf_node: LeafNode<K, V, NUM_PREFIX_BYTES, H>,
                key_bytes_used: usize,
            ) -> (
                OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
                NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>,
            )
            where
                N: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V, Header = H>,
                K: AsBytes + 'a,
                V: 'a,
            {
                // SAFETY: The `inner_node` reference lasts only for the duration of this
                // function, and the node will not be read or written via any other source.
                let inner_node = unsafe { inner_node_ptr.as_mut() };
                let new_leaf_key_byte = new_leaf_node.key_ref().as_bytes()[key_bytes_used];
                let new_leaf_ptr = NodePtr::allocate_node_ptr(new_leaf_node);
                let new_leaf_ptr_opaque = new_leaf_ptr.to_opaque();
                if inner_node.is_full() {
                    // we will create a new node of the next larger type and copy all the
                    // children over.

                    let mut new_node = inner_node.grow();
                    new_node.write_child(new_leaf_key_byte, new_leaf_ptr_opaque);

                    let new_inner_node = NodePtr::allocate_node_ptr(new_node).to_opaque();

                    // SAFETY: The `deallocate_node_ptr` function is only called a
                    // single time.
                    unsafe {
                        #[allow(dropping_references)]
                        drop(inner_node);
                        drop(NodePtr::deallocate_node_ptr(inner_node_ptr));
                    };

                    (new_inner_node, new_leaf_ptr)
                } else {
                    inner_node.write_child(new_leaf_key_byte, new_leaf_ptr_opaque);

                    (inner_node_ptr.to_opaque(), new_leaf_ptr)
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
                    panic!("Cannot have insert into existing with leaf node");
                    // unsafe {
                    //     unreachable_unchecked();
                    // }
                },
            }
        }

        /// Write a new child node to an inner node at the specified key byte.
        fn parent_write_child<
            K: AsBytes,
            V,
            const NUM_PREFIX_BYTES: usize,
            H: NodeHeader<NUM_PREFIX_BYTES>,
        >(
            parent_inner_node: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
            key_byte: u8,
            new_child: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
        ) {
            fn write_inner_node<
                K: AsBytes,
                V,
                N,
                const NUM_PREFIX_BYTES: usize,
                H: NodeHeader<NUM_PREFIX_BYTES>,
            >(
                parent_inner_node: NodePtr<NUM_PREFIX_BYTES, N>,
                key_byte: u8,
                new_child: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
            ) where
                N: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V, Header = H>,
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
                    panic!("A leaf pointer cannot be the parent of another node");
                    // unsafe {
                    //     unreachable_unchecked();
                    // }
                },
            }
        }

        let InsertPoint {
            parent_ptr_and_child_key_byte,
            insert_type,
            key_bytes_used,
            root,
            ..
        } = self;

        let (new_inner_node, leaf_node_ptr) = match insert_type {
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
                let key_bytes = key.as_bytes();

                #[allow(unused_unsafe)]
                unsafe {
                    // SAFETY: Since we are iterating the key and prefixes, we
                    // expect that the depth never exceeds the key len.
                    // Because if this happens we ran out of bytes in the key to match
                    // and the whole process should be already finished
                    assume!(key_bytes_used + mismatch.matched_bytes < key_bytes.len());
                }
                // SAFETY: We hold a mutable reference, so creating
                // a mutable reference is safe
                let header = unsafe { mismatched_inner_node_ptr.header_mut_uncheked() };
                let key_byte = key_bytes[key_bytes_used + mismatch.matched_bytes];

                let new_leaf_pointer = NodePtr::allocate_node_ptr(LeafNode::new(key, value));
                let new_leaf_pointer_opaque = new_leaf_pointer.to_opaque();

                // prefix mismatch, need to split prefix into two separate nodes and take the
                // common prefix into a new parent node
                let prefix = &header.read_prefix();
                let prefix = &prefix[..prefix.len().min(mismatch.matched_bytes)];
                let mut new_n4 = InnerNode4::from_prefix(prefix, mismatch.matched_bytes);

                unsafe {
                    // SAFETY: This is a new node 4 so it's empty and we have
                    // space for writing new children. We also check the order
                    // of the keys before writing
                    if mismatch.prefix_byte < key_byte {
                        new_n4
                            .write_child_unchecked(mismatch.prefix_byte, mismatched_inner_node_ptr);
                        new_n4.write_child_unchecked(key_byte, new_leaf_pointer_opaque);
                    } else {
                        new_n4.write_child_unchecked(key_byte, new_leaf_pointer_opaque);
                        new_n4
                            .write_child_unchecked(mismatch.prefix_byte, mismatched_inner_node_ptr);
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
                    new_leaf_pointer,
                )
            },
            InsertSearchResultType::Exact { leaf_node_ptr } => {
                let new_leaf_node = LeafNode::new(key, value);
                // SAFETY: The leaf node will not be accessed concurrently because of the safety
                // doc on the containing function
                let old_leaf_node = unsafe { NodePtr::replace(leaf_node_ptr, new_leaf_node) };
                return InsertResult {
                    leaf_node_ptr,
                    existing_leaf: Some(old_leaf_node),
                    // Because we replaced the leaf instead of creating a new leaf, we don't
                    // have to write back to the parent. In this case,
                    // the root is guaranteed to be unchanged, even if
                    // the old leaf was the root.
                    new_root: root,
                    marker: PhantomData,
                };
            },
            InsertSearchResultType::SplitLeaf {
                leaf_node_ptr,
                new_key_bytes_used,
            } => {
                let key_bytes = key.as_bytes();
                // SAFETY: We hold a mutable reference, so creating a shared reference is safe
                let leaf_bytes = unsafe { leaf_node_ptr.as_key_ref().as_bytes() };

                #[allow(unused_unsafe)]
                unsafe {
                    // SAFETY: When reaching this point in the insertion proccess this invarants
                    // should always be true, due to the check of [`InsertPrefixError`] which
                    // guarantees that the amount of bytes used is always < len of the key or key in
                    // the leaf if this was not true, then a
                    // [`InsertPrefixError`] would already be triggered
                    assume!(key_bytes_used < leaf_bytes.len());
                    assume!(key_bytes_used < key_bytes.len());
                    assume!(new_key_bytes_used < leaf_bytes.len());
                    assume!(new_key_bytes_used < key_bytes.len());

                    // SAFETY: This is safe by construction, since new_key_bytes_used =
                    // key_bytes_used + x
                    assume!(key_bytes_used <= new_key_bytes_used);
                }

                let mut new_n4 = InnerNode4::from_prefix(
                    &key_bytes[key_bytes_used..new_key_bytes_used],
                    new_key_bytes_used - key_bytes_used,
                );

                let leaf_node_key_byte = leaf_bytes[new_key_bytes_used];
                let new_leaf_node_key_byte = key_bytes[new_key_bytes_used];
                let new_leaf_node_pointer = NodePtr::allocate_node_ptr(LeafNode::new(key, value));

                unsafe {
                    // SAFETY: This is a new node 4 so it's empty and we have
                    // space for writing new children. We also check the order
                    // of the keys before writing
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
                    new_leaf_node_pointer,
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
                leaf_node_ptr,
                existing_leaf: None,
                new_root: root,
                marker: PhantomData,
            }
        } else {
            // If there was no parent, then the root node was a leaf or the inner node split
            // occurred at the root, in which case return the new inner node as root
            InsertResult {
                leaf_node_ptr,
                existing_leaf: None,
                new_root: new_inner_node,
                marker: PhantomData,
            }
        }
    }
}

/// The type of insert
pub enum InsertSearchResultType<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
> {
    /// An insert where an inner node had a differing prefix from the key.
    ///
    /// This insert type will create a new inner node with the portion of
    /// the prefix that did match, and update the existing inner node
    MismatchPrefix {
        /// Data about the matching if the prefix
        mismatch: Mismatch<K, V, NUM_PREFIX_BYTES, H>,
        /// A pointer to the inner node which had a mismatched prefix
        mismatched_inner_node_ptr: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    },
    /// An insert where the node to be added matched all the way up to a
    /// leaf node.
    ///
    /// This insert type will create a new inner node, and assign the
    /// existing leaf and the new leaf as children to that node.
    SplitLeaf {
        /// A pointer to the leaf node that will be split
        leaf_node_ptr: NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>,
        new_key_bytes_used: usize,
    },
    /// Exact match of the leaf was found
    ///
    /// This insert type will replace the older leaf with a new one
    Exact {
        /// A pointer to the leaf node that will be split
        leaf_node_ptr: NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>,
    },
    /// An insert where the search terminated at an existing inner node that
    /// did not have a child with the key byte.
    ///
    /// If the inner node is full, it will be grown to the next largest
    /// size.
    IntoExisting {
        /// A pointer to the existing inner node which will be updated to
        /// contain the new child leaf node
        inner_node_ptr: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    },
}

/// Perform an iterative search for the insert point for the given key,
/// starting at the given root node.
///
/// # Safety
///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the underlying
///    tree
///  - This function cannot be called concurrently to any reads or writes of the
///    `root` node or any child node of `root`. This function will arbitrarily
///    read or write to any child in the given tree.
///
/// # Errors
///  - If the given `key` is a prefix of an existing key, this function will
///    return an error.
pub unsafe fn search_for_insert_point<K, V, Q, const NUM_PREFIX_BYTES: usize, H>(
    root: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    key: &Q,
) -> Result<InsertPoint<K, V, NUM_PREFIX_BYTES, H>, InsertPrefixError>
where
    K: AsBytes + Borrow<Q>,
    Q: AsBytes + ?Sized,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    #[allow(clippy::type_complexity)]
    fn test_prefix_identify_insert<K, V, N, const NUM_PREFIX_BYTES: usize, H>(
        inner_ptr: NodePtr<NUM_PREFIX_BYTES, N>,
        key: &[u8],
        current_depth: &mut usize,
    ) -> Result<
        ControlFlow<
            Mismatch<K, V, NUM_PREFIX_BYTES, H>,
            Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
        >,
        InsertPrefixError,
    >
    where
        N: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V, Header = H>,
        K: AsBytes,
        H: NodeHeader<NUM_PREFIX_BYTES>,
    {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `search_unchecked` function.
        let inner_node = unsafe { inner_ptr.as_ref() };
        let match_prefix = inner_node.match_prefix(key, *current_depth);
        match match_prefix {
            MatchPrefixResult::Mismatch { mismatch } => Ok(ControlFlow::Break(mismatch)),
            MatchPrefixResult::Match { matched_bytes } => {
                // Since the prefix matched, advance the depth by the size of the prefix
                *current_depth += matched_bytes;

                if likely!(*current_depth < key.len()) {
                    let next_key_fragment = key[*current_depth];
                    Ok(ControlFlow::Continue(
                        inner_node.lookup_child(next_key_fragment),
                    ))
                } else {
                    // then the key has insufficient bytes to be unique. It must be
                    // a prefix of an existing key
                    Err(InsertPrefixError {
                        byte_repr: key.into(),
                    })
                }
            },
        }
    }

    // We keep track of the grandparent because when dealing with
    // entry api we want to be able to remove the entry if it's
    // occupied, since the entry api works by searching the insertion
    // point we do similar work to the delete process by keeping track
    // of the grandparent. Of course this is not as efficient as deleting
    // directly since we are doing a ton of extra work. But this will
    // only be used during the remove in the entry api. It's also not a
    // lot of extra work to keep track of the grandparent since it's just
    // a copy of a ptr and u8
    let mut current_grandparent = None;
    let mut current_parent = None;
    let mut current_node = root;
    let mut current_depth = 0;
    let key_bytes = key.as_bytes();

    loop {
        let lookup_result = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                let leaf_node = leaf_node_ptr.read();

                if leaf_node.matches_full_key(key) {
                    return Ok(InsertPoint {
                        key_bytes_used: current_depth,
                        grandparent_ptr_and_parent_key_byte: current_grandparent,
                        parent_ptr_and_child_key_byte: current_parent,
                        insert_type: InsertSearchResultType::Exact { leaf_node_ptr },
                        root,
                    });
                }

                let leaf_bytes = leaf_node.key_ref().as_bytes();

                #[allow(unused_unsafe)]
                unsafe {
                    // SAFETY: The [`test_prefix_identify_insert`] checks for [`InsertPrefixError`]
                    // which would lead to this not holding, but since it already checked we know
                    // that current_depth < len of the key and the key in the leaf. But there is an
                    // edge case, if the root of the tree is a leaf than the depth can be = len
                    assume!(current_depth <= leaf_bytes.len());
                    assume!(current_depth <= key_bytes.len());
                }

                let prefix_size = leaf_bytes[current_depth..]
                    .iter()
                    .zip(key_bytes[current_depth..].iter())
                    .take_while(|(k1, k2)| k1 == k2)
                    .count();

                let new_key_bytes_used = current_depth + prefix_size;

                if unlikely!(
                    new_key_bytes_used >= key_bytes.len() || new_key_bytes_used >= leaf_bytes.len()
                ) {
                    // then the key has insufficient bytes to be unique. It must be
                    // a prefix of an existing key OR an existing key is a prefix of it
                    return Err(InsertPrefixError {
                        byte_repr: key_bytes.into(),
                    });
                }

                return Ok(InsertPoint {
                    key_bytes_used: current_depth,
                    grandparent_ptr_and_parent_key_byte: current_grandparent,
                    parent_ptr_and_child_key_byte: current_parent,
                    insert_type: InsertSearchResultType::SplitLeaf {
                        leaf_node_ptr,
                        new_key_bytes_used,
                    },
                    root,
                });
            },
        }?;

        match lookup_result {
            ControlFlow::Continue(next_child_node) => {
                #[allow(unused_unsafe)]
                unsafe {
                    // SAFETY: The [`test_prefix_identify_insert`] checks for [`InsertPrefixError`]
                    // which would lead to this not holding, but since it already checked we know
                    // that current_depth < len of the key and the key in the leaf. And also the
                    // only edge case can occur in the Leaf node, but if we reach a leaf not the
                    // function returns early, so it's impossible to be <=
                    assume!(current_depth < key_bytes.len());
                }

                match next_child_node {
                    Some(next_child_node) => {
                        current_grandparent = current_parent;
                        let byte = key_bytes[current_depth];
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
                            grandparent_ptr_and_parent_key_byte: current_grandparent,
                            parent_ptr_and_child_key_byte: current_parent,
                            root,
                        })
                    },
                }
            },
            ControlFlow::Break(mismatch) => {
                if unlikely!((current_depth + mismatch.matched_bytes) >= key_bytes.len()) {
                    // then the key has insufficient bytes to be unique. It must be
                    // a prefix of an existing key

                    return Err(InsertPrefixError {
                        byte_repr: key_bytes.into(),
                    });
                }

                return Ok(InsertPoint {
                    key_bytes_used: current_depth,
                    insert_type: InsertSearchResultType::MismatchPrefix {
                        mismatch,
                        mismatched_inner_node_ptr: current_node,
                    },
                    grandparent_ptr_and_parent_key_byte: current_grandparent,
                    parent_ptr_and_child_key_byte: current_parent,
                    root,
                });
            },
        };
    }
}

#[cfg(test)]
mod tests;
