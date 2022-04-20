//! Trie node lookup and manipulation

use crate::{
    ConcreteNodePtr, Header, InnerNode, InnerNode256Iter, InnerNode4, InnerNode48Iter,
    InnerNodeCompressedIter, InnerNodeIter, LeafNode, NodePtr, OpaqueNodePtr,
};
use std::{collections::VecDeque, error::Error, fmt::Display, iter};

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
    enum TestResult<V> {
        MismatchPrefix(OpaqueNodePtr<V>),
        Error(InsertError),
        Continue(u8, Box<[u8]>, V),
    }

    fn test_prefix_update_depth_split_mismatch<V>(
        root: OpaqueNodePtr<V>,
        header: &mut Header,
        key: Box<[u8]>,
        value: V,
        depth: &mut usize,
    ) -> TestResult<V> {
        // since header is mutable will need to write it back
        let matched_prefix_size = header.match_prefix(&key[*depth..]);
        if matched_prefix_size != header.prefix_size() {
            // prefix mismatch, need to split prefix into two separate nodes and take the
            // common prefix into a new parent node
            let mut new_n4 = InnerNode4::empty();

            if (*depth + matched_prefix_size) >= key.len() {
                // then the key has insufficient bytes to be unique. It must be
                // a prefix of an existing key

                return TestResult::Error(InsertError::PrefixKey(key));
            }

            let new_leaf_key_byte = key[*depth + matched_prefix_size];
            let new_leaf_pointer = NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque();

            new_n4.write_child(header.read_prefix()[matched_prefix_size], root);
            new_n4.write_child(new_leaf_key_byte, new_leaf_pointer);

            new_n4
                .header
                .write_prefix(&header.read_prefix()[..matched_prefix_size]);
            header.ltrim_prefix(matched_prefix_size + 1);

            // Updated the header information here
            return TestResult::MismatchPrefix(NodePtr::allocate_node(new_n4).to_opaque());
        }

        *depth += header.prefix_size();

        if *depth < key.len() {
            TestResult::Continue(key[*depth], key, value)
        } else {
            TestResult::Error(InsertError::PrefixKey(key))
        }
    }

    // TODO: Consider an iterative solution to handle tree with long keys.
    fn insert_rec_inner<V>(
        mut root: OpaqueNodePtr<V>,
        key: Box<[u8]>,
        value: V,
        mut depth: usize,
    ) -> Result<OpaqueNodePtr<V>, InsertError> {
        match root.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => {
                // SAFETY: The lifetime produced from this is bounded to this scope and does not
                // escape. Further, no other code mutates or reads the node referenced, which is
                // further enforced the "no concurrent reads or writes"
                // requirement on the `insert_unchecked` function.
                let inner_node = unsafe { inner_ptr.as_mut() };
                let (next_key_fragment, key, value) = match test_prefix_update_depth_split_mismatch(
                    root,
                    &mut inner_node.header,
                    key,
                    value,
                    &mut depth,
                ) {
                    TestResult::MismatchPrefix(new_node) => {
                        return Ok(new_node);
                    },
                    TestResult::Error(error) => {
                        return Err(error);
                    },
                    TestResult::Continue(next_key_fragment, key, value) => {
                        (next_key_fragment, key, value)
                    },
                };

                match inner_node.lookup_child(next_key_fragment) {
                    Some(next_child_node) => {
                        let new_child = insert_rec_inner(next_child_node, key, value, depth + 1)?;

                        inner_node.write_child(next_key_fragment, new_child);
                    },
                    None => {
                        if inner_node.is_full() {
                            // we will create a new node of the next larger type and copy all the
                            // children over.

                            let mut new_node = inner_node.grow();
                            new_node.write_child(
                                key[depth],
                                NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque(),
                            );

                            root = NodePtr::allocate_node(new_node).to_opaque();
                            // SAFETY: The `deallocate_node` function is only called a
                            // single time. The uniqueness requirement is passed up to the
                            // `grow_unchecked` safety requirements.
                            unsafe {
                                NodePtr::deallocate_node(inner_ptr);
                            }
                        } else {
                            inner_node.write_child(
                                key[depth],
                                NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque(),
                            )
                        }
                    },
                }
            },
            ConcreteNodePtr::Node16(inner_ptr) => {
                // SAFETY: The lifetime produced from this is bounded to this scope and does not
                // escape. Further, no other code mutates or reads the node referenced, which is
                // further enforced the "no concurrent reads or writes"
                // requirement on the `insert_unchecked` function.
                let inner_node = unsafe { inner_ptr.as_mut() };
                let (next_key_fragment, key, value) = match test_prefix_update_depth_split_mismatch(
                    root,
                    &mut inner_node.header,
                    key,
                    value,
                    &mut depth,
                ) {
                    TestResult::MismatchPrefix(new_node) => {
                        return Ok(new_node);
                    },
                    TestResult::Error(error) => {
                        return Err(error);
                    },
                    TestResult::Continue(next_key_fragment, key, value) => {
                        (next_key_fragment, key, value)
                    },
                };

                match inner_node.lookup_child(next_key_fragment) {
                    Some(next_child_node) => {
                        let new_child = insert_rec_inner(next_child_node, key, value, depth + 1)?;

                        inner_node.write_child(next_key_fragment, new_child);
                    },
                    None => {
                        if inner_node.is_full() {
                            // we will create a new node of the next larger type and copy all the
                            // children over.

                            let mut new_node = inner_node.grow();
                            new_node.write_child(
                                key[depth],
                                NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque(),
                            );

                            root = NodePtr::allocate_node(new_node).to_opaque();
                            // SAFETY: The `deallocate_node` function is only called a
                            // single time. The uniqueness requirement is passed up to the
                            // `grow_unchecked` safety requirements.
                            unsafe {
                                NodePtr::deallocate_node(inner_ptr);
                            }
                        } else {
                            inner_node.write_child(
                                key[depth],
                                NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque(),
                            )
                        }
                    },
                }
            },
            ConcreteNodePtr::Node48(inner_ptr) => {
                // SAFETY: The lifetime produced from this is bounded to this scope and does not
                // escape. Further, no other code mutates or reads the node referenced, which is
                // further enforced the "no concurrent reads or writes"
                // requirement on the `insert_unchecked` function.
                let inner_node = unsafe { inner_ptr.as_mut() };
                let (next_key_fragment, key, value) = match test_prefix_update_depth_split_mismatch(
                    root,
                    &mut inner_node.header,
                    key,
                    value,
                    &mut depth,
                ) {
                    TestResult::MismatchPrefix(new_node) => {
                        return Ok(new_node);
                    },
                    TestResult::Error(error) => {
                        return Err(error);
                    },
                    TestResult::Continue(next_key_fragment, key, value) => {
                        (next_key_fragment, key, value)
                    },
                };

                match inner_node.lookup_child(next_key_fragment) {
                    Some(next_child_node) => {
                        let new_child = insert_rec_inner(next_child_node, key, value, depth + 1)?;

                        inner_node.write_child(next_key_fragment, new_child);
                    },
                    None => {
                        if inner_node.is_full() {
                            // we will create a new node of the next larger type and copy all the
                            // children over.

                            let mut new_node = inner_node.grow();
                            new_node.write_child(
                                key[depth],
                                NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque(),
                            );

                            root = NodePtr::allocate_node(new_node).to_opaque();
                            // SAFETY: The `deallocate_node` function is only called a
                            // single time. The uniqueness requirement is passed up to the
                            // `grow_unchecked` safety requirements.
                            unsafe {
                                NodePtr::deallocate_node(inner_ptr);
                            }
                        } else {
                            inner_node.write_child(
                                key[depth],
                                NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque(),
                            )
                        }
                    },
                }
            },
            ConcreteNodePtr::Node256(inner_ptr) => {
                // SAFETY: The lifetime produced from this is bounded to this scope and does not
                // escape. Further, no other code mutates or reads the node referenced, which is
                // further enforced the "no concurrent reads or writes"
                // requirement on the `insert_unchecked` function.
                let inner_node = unsafe { inner_ptr.as_mut() };
                let (next_key_fragment, key, value) = match test_prefix_update_depth_split_mismatch(
                    root,
                    &mut inner_node.header,
                    key,
                    value,
                    &mut depth,
                ) {
                    TestResult::MismatchPrefix(new_node) => {
                        return Ok(new_node);
                    },
                    TestResult::Error(error) => {
                        return Err(error);
                    },
                    TestResult::Continue(next_key_fragment, key, value) => {
                        (next_key_fragment, key, value)
                    },
                };

                match inner_node.lookup_child(next_key_fragment) {
                    Some(next_child_node) => {
                        let new_child = insert_rec_inner(next_child_node, key, value, depth + 1)?;

                        inner_node.write_child(next_key_fragment, new_child);
                    },
                    None => inner_node.write_child(
                        key[depth],
                        NodePtr::allocate_node(LeafNode::new(key, value)).to_opaque(),
                    ),
                }
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
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

/// Deallocate the given node and all children of the given node.
///
/// This will also deallocate the leaf nodes with their value type data.
///
/// # Safety
///
///  - This function must only be called once for this root node and all
///    descendants, otherwise a double-free could result.
pub unsafe fn deallocate_tree<V>(root: OpaqueNodePtr<V>) {
    let mut stack = Vec::new();

    stack.push(root);

    while let Some(next_node_ptr) = stack.pop() {
        match next_node_ptr.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => {
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
                    let iter = unsafe { InnerNodeCompressedIter::new(inner_node) };
                    stack.extend(iter.map(|(_, child)| child));
                }
                // SAFETY: The single call per node requirement is enforced by the safety
                // requirements on this function.
                unsafe { NodePtr::deallocate_node(inner_ptr) }
            },
            ConcreteNodePtr::Node16(inner_ptr) => {
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
                    let iter = unsafe { InnerNodeCompressedIter::new(inner_node) };
                    stack.extend(iter.map(|(_, child)| child));
                }
                // SAFETY: The single call per node requirement is enforced by the safety
                // requirements on this function.
                unsafe { NodePtr::deallocate_node(inner_ptr) }
            },
            ConcreteNodePtr::Node48(inner_ptr) => {
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
                    let iter = unsafe { InnerNode48Iter::new(inner_node) };
                    stack.extend(iter.map(|(_, child)| child));
                }
                // SAFETY: The single call per node requirement is enforced by the safety
                // requirements on this function.
                unsafe { NodePtr::deallocate_node(inner_ptr) }
            },
            ConcreteNodePtr::Node256(inner_ptr) => {
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
                    let iter = unsafe { InnerNode256Iter::new(inner_node) };
                    stack.extend(iter.map(|(_, child)| child));
                }
                // SAFETY: The single call per node requirement is enforced by the safety
                // requirements on this function.
                unsafe { NodePtr::deallocate_node(inner_ptr) }
            },
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
///  - This function cannot be called concurrently to any reads or writes of
///    `root` or any child node of `root`. This function will arbitrarily read
///    to any child in the given tree.
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
        let mut iter = unsafe { inner_node.into_iter() };
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
///  - This function cannot be called concurrently to any reads or writes of
///    `root` or any child node of `root`. This function will arbitrarily read
///    to any child in the given tree.
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
        let iter = unsafe { inner_node.into_iter() };
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
            .push_front(unsafe { inner.as_ref().into_iter().into() })
    }

    fn update_iters_back<N: InnerNode<Value = V>>(&mut self, inner: NodePtr<N>) {
        // SAFETY: The lifetime of the returned reference is restricted to this
        // function, during which it is turned into an owned iterator which uses
        // pointers. The safety requirements on the `TrieRangeFullIter` type ensure that
        // no other mutation of the tree happens while the iterator is live.
        self.node_iters
            .push_back(unsafe { inner.as_ref().into_iter().into() })
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
