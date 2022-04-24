//! Trie node lookup and manipulation

use crate::{
    ConcreteNodePtr, InnerNode, InnerNode4, InnerNodeIter, LeafNode, NodePtr, OpaqueNodePtr,
};
use std::{
    collections::VecDeque,
    error::Error,
    fmt::{self, Display},
    iter,
    ops::ControlFlow,
};

/// Search in the given tree for the value stored with the given key.
///
/// # Safety
///
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
pub unsafe fn search_unchecked<V>(
    root: OpaqueNodePtr<V>,
    key: &[u8],
) -> Option<NodePtr<LeafNode<V>>> {
    fn test_prefix_continue_search<N: InnerNode>(
        inner_ptr: NodePtr<N>,
        key: &[u8],
        current_depth: &mut usize,
    ) -> Option<OpaqueNodePtr<N::Value>> {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `search_unchecked` function.
        let inner_node = unsafe { inner_ptr.as_ref() };
        let header = inner_node.header();
        if header.match_prefix(&key[*current_depth..]) != header.prefix_size() {
            return None;
        }

        // Since the prefix matched, advance the depth by the size of the prefix
        *current_depth += header.prefix_size();

        let next_key_fragment = if *current_depth < key.len() {
            key[*current_depth]
        } else {
            return None;
        };

        inner_node.lookup_child(next_key_fragment)
    }

    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        let next_child_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => {
                test_prefix_continue_search(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => {
                test_prefix_continue_search(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => {
                test_prefix_continue_search(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => {
                test_prefix_continue_search(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                let leaf_node = leaf_node_ptr.read();

                // Specifically we are matching the leaf node stored key against the full search
                // key to confirm that it is the right value.
                if leaf_node.matches_key(key) {
                    return Some(leaf_node_ptr);
                } else {
                    return None;
                }
            },
        };

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
///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the underlyin
///  - This function cannot be called concurrently to any reads or writes of the
///    `root` node or any child node of `root`. This function will arbitrarily
///    read or write to any child in the given tree.
pub unsafe fn insert_unchecked<V>(
    root: OpaqueNodePtr<V>,
    key: Box<[u8]>,
    value: V,
) -> Result<OpaqueNodePtr<V>, InsertError> {
    /// This struct contains the results from searching for an insert point for
    /// a new node in the tree.
    ///
    /// It contains all the relevant information needed to perform the insert
    /// and update the tree.
    struct InsertSearchResult<V> {
        parent_ptr_and_child_key_byte: Option<(OpaqueNodePtr<V>, u8)>,
        insert_type: InsertSearchResultType<V>,
        key_bytes_used: usize,
    }

    /// The type of insert
    enum InsertSearchResultType<V> {
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
    fn search_for_insert_point<V>(
        root: OpaqueNodePtr<V>,
        key: &[u8],
    ) -> Result<InsertSearchResult<V>, InsertError> {
        fn test_prefix_identify_insert<V, N: InnerNode<Value = V>>(
            inner_ptr: NodePtr<N>,
            key: &[u8],
            current_depth: &mut usize,
        ) -> Result<ControlFlow<usize, Option<OpaqueNodePtr<V>>>, InsertError> {
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

                return Err(InsertError::PrefixKey(Box::from(key)));
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
            // SAFETY:
            // You must enforce Rust’s aliasing rules, since the returned lifetime
            // 'a is arbitrarily chosen and does not necessarily reflect the actual lifetime
            // of the node. In particular, for the duration of this lifetime, the node the
            // pointer points to must not get accessed (read or written) through any other
            // pointer.
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
                // Also, the `inner_node` mutable reference is invalid after this pointer and
                // must not be used.
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

            // prefix mismatch, need to split prefix into two separate nodes and take the
            // common prefix into a new parent node
            let mut new_n4 = InnerNode4::empty();

            if (key_bytes_used + matched_prefix_size) >= key.len() {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key

                return Err(InsertError::PrefixKey(key));
            }

            let new_leaf_key_byte = key[key_bytes_used + matched_prefix_size];

            let new_leaf_pointer = NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque();

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

/// Deallocate the given node and all children of the given node.
///
/// This will also deallocate the leaf nodes with their value type data.
///
/// # Safety
///
///  - This function must only be called once for this root node and all
///    descendants, otherwise a double-free could result.
pub unsafe fn deallocate_tree<V>(root: OpaqueNodePtr<V>) {
    fn deallocate_inner_node<V, N: InnerNode<Value = V>>(
        stack: &mut Vec<OpaqueNodePtr<V>>,
        inner_ptr: NodePtr<N>,
    ) {
        {
            // SAFETY: The scope of this reference is bounded and we enforce that no
            // mutation of the reference memory takes place within the lifetime. The
            // deallocation of the node happens outside of this block, after the lifetime
            // ends.
            let inner_node = unsafe { inner_ptr.as_ref() };
            // SAFETY: This iterator only lives for this block, a subset of the shared
            // lifetime of the `inner_node` variable. By the safety requirements of the
            // `deallocate_tree` function, no other mutation of this node can happen while
            // this iterator is live.
            let iter = unsafe { inner_node.iter() };
            stack.extend(iter.map(|(_, child)| child));
        }
        // SAFETY: The single call per node requirement is enforced by the safety
        // requirements on this function.
        unsafe { NodePtr::deallocate_node(inner_ptr) }
    }

    let mut stack = Vec::new();

    stack.push(root);

    while let Some(next_node_ptr) = stack.pop() {
        match next_node_ptr.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => deallocate_inner_node(&mut stack, inner_ptr),
            ConcreteNodePtr::Node16(inner_ptr) => deallocate_inner_node(&mut stack, inner_ptr),
            ConcreteNodePtr::Node48(inner_ptr) => deallocate_inner_node(&mut stack, inner_ptr),
            ConcreteNodePtr::Node256(inner_ptr) => deallocate_inner_node(&mut stack, inner_ptr),
            ConcreteNodePtr::LeafNode(inner) => {
                // SAFETY: The single call per node requirement is enforced by the safety
                // requirements on this function.
                unsafe { NodePtr::deallocate_node(inner) }
            },
        }
    }
}

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

/// An iterator over all the entries in a tree.
///
/// # Safety
///
/// This iterator maintains pointers to internal nodes from the trie. No
/// mutating operation can occur while this an instance of the iterator is live.
pub struct TrieRangeFullIter<V> {
    node_iters: VecDeque<InnerNodeIter<V>>,
}

impl<V> TrieRangeFullIter<V> {
    /// Create a new iterator that will visit all leaf nodes descended from the
    /// given node.
    ///
    /// # Safety
    ///
    /// See safety requirements on type [`TrieRangeFullIter`].
    pub unsafe fn new(root: OpaqueNodePtr<V>) -> Result<Self, iter::Once<(*const [u8], *const V)>> {
        let mut trie_full_iter = TrieRangeFullIter {
            node_iters: VecDeque::new(),
        };

        match root.to_node_ptr() {
            ConcreteNodePtr::Node4(inner) => {
                trie_full_iter.update_iters_front(inner);
            },
            ConcreteNodePtr::Node16(inner) => {
                trie_full_iter.update_iters_front(inner);
            },
            ConcreteNodePtr::Node48(inner) => {
                trie_full_iter.update_iters_front(inner);
            },
            ConcreteNodePtr::Node256(inner) => {
                trie_full_iter.update_iters_front(inner);
            },
            ConcreteNodePtr::LeafNode(inner) => {
                return Err(iter::once(Self::leaf_to_item(inner)));
            },
        }

        Ok(trie_full_iter)
    }

    fn update_iters_front<N: InnerNode<Value = V>>(&mut self, inner: NodePtr<N>) {
        // SAFETY: The lifetime of the returned reference is restricted to this
        // function, during which it is turned into an owned iterator which uses
        // pointers. The safety requirements on the `TrieRangeFullIter` type ensure that
        // no other mutation of the tree happens while the iterator is live.
        self.node_iters
            .push_front(unsafe { inner.as_ref().iter().into() })
    }

    fn update_iters_back<N: InnerNode<Value = V>>(&mut self, inner: NodePtr<N>) {
        // SAFETY: The lifetime of the returned reference is restricted to this
        // function, during which it is turned into an owned iterator which uses
        // pointers. The safety requirements on the `TrieRangeFullIter` type ensure that
        // no other mutation of the tree happens while the iterator is live.
        self.node_iters
            .push_back(unsafe { inner.as_ref().iter().into() })
    }

    fn leaf_to_item(node: NodePtr<LeafNode<V>>) -> (*const [u8], *const V) {
        // SAFETY: The lifetime of the returned reference is restricted to this
        // function. The safety requirements on the `TrieRangeFullIter` type ensure that
        // no other mutation of the pointers returned from this function happens while
        let leaf = unsafe { node.as_ref() };

        (leaf.key.as_ref() as *const _, (&leaf.value) as *const _)
    }
}

impl<V> Iterator for TrieRangeFullIter<V> {
    type Item = (*const [u8], *const V);

    fn next(&mut self) -> Option<Self::Item> {
        while !self.node_iters.is_empty() {
            if let Some((_, child)) = self.node_iters.front_mut().unwrap().next() {
                match child.to_node_ptr() {
                    ConcreteNodePtr::Node4(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::Node16(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::Node48(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::Node256(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::LeafNode(inner) => {
                        return Some(Self::leaf_to_item(inner));
                    },
                }
            } else {
                self.node_iters.pop_front();
            }
        }

        None
    }
}

impl<V> DoubleEndedIterator for TrieRangeFullIter<V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while !self.node_iters.is_empty() {
            if let Some((_, child)) = self.node_iters.back_mut().unwrap().next_back() {
                match child.to_node_ptr() {
                    ConcreteNodePtr::Node4(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::Node16(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::Node48(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::Node256(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::LeafNode(inner) => {
                        return Some(Self::leaf_to_item(inner));
                    },
                }
            } else {
                self.node_iters.pop_back();
            }
        }

        None
    }
}

#[cfg(test)]
mod lookup_tests;

#[cfg(test)]
mod insert_tests;

#[cfg(test)]
mod minmax_tests;

#[cfg(test)]
mod iterator_tests;
