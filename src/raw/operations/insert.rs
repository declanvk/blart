use crate::{
    alloc::Allocator,
    raw::{
        deallocate_tree, maximum_unchecked, minimum_unchecked, ConcreteNodePtr, ExplicitMismatch,
        InnerNode, InnerNode4, LeafNode, NodePtr, OpaqueNodePtr, PrefixMatch, TreePath,
        TreePathSearch,
    },
    rust_nightly_apis::{assume, likely, unlikely},
    AsBytes,
};
use std::{
    error::Error,
    fmt,
    marker::PhantomData,
    ops::{Bound, ControlFlow},
};

/// The results of a successful tree insert
#[derive(Debug)]
pub struct InsertResult<'a, K, V, const PREFIX_LEN: usize> {
    /// Pointer to the leaf
    pub leaf_node_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,

    /// The existing leaf referenced by the insert key, if present
    pub existing_leaf: Option<LeafNode<K, V, PREFIX_LEN>>,

    /// The new tree root after the successful insert
    pub new_root: OpaqueNodePtr<K, V, PREFIX_LEN>,

    /// This field details what kind of changes happened to the parent node.
    pub parent_node_change: InsertParentNodeChange<K, V, PREFIX_LEN>,

    marker: PhantomData<(&'a mut K, &'a V)>,
}

pub enum InsertParentNodeChange<K, V, const PREFIX_LEN: usize> {
    /// This variant indicates that a new parent node was allocated, either
    /// because:
    ///  - The old parent node was too small
    ///  - The old parent node had a mismatch with the key
    ///  - The [`InsertKind`] was [`InsertKind::SplitLeaf`]
    NewParent {
        /// A pointer to the newly allocated parent node.
        new_parent_node: OpaqueNodePtr<K, V, PREFIX_LEN>,
        /// The key byte used to select the newly inserted leaf node
        leaf_node_key_byte: u8,
    },
    /// This variant indicates that there was no replacement of
    /// the parent node during the inert.
    NoChange,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for InsertParentNodeChange<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NewParent {
                new_parent_node,
                leaf_node_key_byte,
            } => f
                .debug_struct("NewParent")
                .field("new_parent_node", new_parent_node)
                .field("leaf_node_key_byte", leaf_node_key_byte)
                .finish(),
            Self::NoChange => write!(f, "NoChange"),
        }
    }
}

/// Attempted to insert a key which was a prefix of an existing key in
/// the tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InsertPrefixError {
    /// The inserted key
    pub byte_repr: Box<[u8]>,
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
pub struct InsertPoint<K, V, const PREFIX_LEN: usize> {
    /// The path to point where the new leaf will be inserted.
    pub path: TreePath<K, V, PREFIX_LEN>,
    /// The kind of operation that needs to be performed to insert the key
    pub insert_kind: InsertKind<K, V, PREFIX_LEN>,
    /// The number of bytes that were read from the key to find the insert
    /// point.
    pub key_bytes_used: usize,
    /// Current root of the tree, used in the apply
    pub root: OpaqueNodePtr<K, V, PREFIX_LEN>,
}

impl<K, V, const PREFIX_LEN: usize> Copy for InsertPoint<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> Clone for InsertPoint<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for InsertPoint<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InsertPoint")
            .field("path", &self.path)
            .field("insert_kind", &self.insert_kind)
            .field("key_bytes_used", &self.key_bytes_used)
            .field("root", &self.root)
            .finish()
    }
}

/// Write a new child node to an inner node at the specified key byte.
///
/// # Panics
/// Panics if the node pointer given is not an inner node.
///
/// # Safety
///
///  - This function must not be called concurrently with and other read or
///    modification of the trie.
unsafe fn parent_write_child<K: AsBytes, V, const PREFIX_LEN: usize>(
    parent_inner_node: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_byte: u8,
    new_child: OpaqueNodePtr<K, V, PREFIX_LEN>,
) {
    fn write_inner_node<K: AsBytes, V, N, const PREFIX_LEN: usize>(
        parent_inner_node: NodePtr<PREFIX_LEN, N>,
        key_byte: u8,
        new_child: OpaqueNodePtr<K, V, PREFIX_LEN>,
    ) where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
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
            unreachable!("A leaf pointer cannot be the parent of another node");
        },
    }
}

impl<K, V, const PREFIX_LEN: usize> InsertPoint<K, V, PREFIX_LEN> {
    /// This function will use [`InsertPoint`] information to insert the given
    /// key-value pair into the trie.
    ///
    /// # Safety
    ///
    ///  - This function must not be called concurrently with and other read or
    ///    modification of the trie.
    ///  - The given allocator must be the same one that was used to allocate
    ///    the nodes of this trie.
    ///  - This function may invalidate existing pointers into the trie when
    ///    inner nodes are grown. Callers must ensure that they delete
    ///    invalidated pointers, the new pointers are returned in
    ///    [`InsertResult`].
    pub unsafe fn apply<'a, A>(
        self,
        key: K,
        value: V,
        alloc: &A,
    ) -> InsertResult<'a, K, V, PREFIX_LEN>
    where
        K: AsBytes + 'a,
        V: 'a,
        A: Allocator,
    {
        fn write_new_child_in_existing_node<'a, K, V, A, const PREFIX_LEN: usize>(
            inner_node_ptr: OpaqueNodePtr<K, V, PREFIX_LEN>,
            new_leaf_node: LeafNode<K, V, PREFIX_LEN>,
            key_bytes_used: usize,
            alloc: &A,
        ) -> (
            OpaqueNodePtr<K, V, PREFIX_LEN>,
            NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
            u8,
        )
        where
            K: AsBytes + 'a,
            V: 'a,
            A: Allocator,
        {
            fn write_new_child_in_existing_inner_node<'a, K, V, N, A, const PREFIX_LEN: usize>(
                inner_node_ptr: NodePtr<PREFIX_LEN, N>,
                new_leaf_node: LeafNode<K, V, PREFIX_LEN>,
                key_bytes_used: usize,
                alloc: &A,
            ) -> (
                OpaqueNodePtr<K, V, PREFIX_LEN>,
                NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
                u8,
            )
            where
                N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
                K: AsBytes + 'a,
                V: 'a,
                A: Allocator,
            {
                /// This function will:
                ///   1. Find the nearest (previous or next) sibling leaf for
                ///      the new leaf pointer
                ///   2. Use that sibling leaf node to add the new leaf pointer
                ///      into the linked list of leaves
                fn insert_new_leaf_in_linked_list<'a, K, V, N, const PREFIX_LEN: usize>(
                    new_leaf_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
                    inner_node: &mut N,
                    new_leaf_key_byte: u8,
                ) where
                    N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
                    K: AsBytes + 'a,
                    V: 'a,
                {
                    if let Some((_, next_node)) = inner_node
                        .range((Bound::Excluded(new_leaf_key_byte), Bound::Unbounded))
                        .next()
                    {
                        // in this branch we're looking for the next larger leaf node, which we'll
                        // get by iterating over the inner node starting from the excluded new leaf
                        // key byte. Then we find the minimum leaf of that next node to be the
                        // `next` sibling

                        // SAFETY: There are no concurrent modifications, the `apply` safety doc
                        // covers this
                        let next_leaf = unsafe { minimum_unchecked(next_node) };

                        // SAFETY: There is no concurrent modification of the new leaf node, the
                        // existing leaf node, or its siblings because of the safety requirements of
                        // the `apply` function.
                        unsafe { LeafNode::insert_before(new_leaf_ptr, next_leaf) };
                    } else if let Some((_, previous_node)) = inner_node
                        .range((Bound::Unbounded, Bound::Excluded(new_leaf_key_byte)))
                        .next_back()
                    {
                        // in this branch we're looking for the next smaller leaf node, which we'll
                        // get by iterating over the inner node ending with the excluded new leaf
                        // key byte. Then we find the maximum leaf of that next node to be the
                        // `previous` sibling

                        // SAFETY: There are no concurrent modifications, the `apply` safety doc
                        // covers this
                        let previous_leaf = unsafe { maximum_unchecked(previous_node) };

                        // SAFETY: There is no concurrent modification of the new leaf node, the
                        // existing leaf node, or its siblings because of the safety requirements of
                        // the `apply` function.
                        unsafe { LeafNode::insert_after(new_leaf_ptr, previous_leaf) };
                    } else {
                        unreachable!("the inner node should have at least one other child");
                    }
                }

                // SAFETY: The `inner_node` reference lasts only for the duration of this
                // function, and the node will not be read or written via any other source.
                let inner_node = unsafe { inner_node_ptr.as_mut() };

                let new_leaf_key_byte = new_leaf_node.key_ref().as_bytes()[key_bytes_used];
                let new_leaf_ptr = NodePtr::allocate_node_ptr(new_leaf_node, alloc);
                let new_leaf_ptr_opaque = new_leaf_ptr.to_opaque();
                if inner_node.is_full() {
                    // we will create a new node of the next larger type and copy all the
                    // children over.

                    let mut new_node = inner_node.grow();
                    new_node.write_child(new_leaf_key_byte, new_leaf_ptr_opaque);

                    insert_new_leaf_in_linked_list(new_leaf_ptr, &mut new_node, new_leaf_key_byte);

                    let new_inner_node = NodePtr::allocate_node_ptr(new_node, alloc).to_opaque();

                    // SAFETY: The `deallocate_node_ptr` function is only called a
                    // single time.
                    unsafe {
                        drop(NodePtr::deallocate_node_ptr(inner_node_ptr, alloc));
                    };

                    (new_inner_node, new_leaf_ptr, new_leaf_key_byte)
                } else {
                    inner_node.write_child(new_leaf_key_byte, new_leaf_ptr_opaque);

                    insert_new_leaf_in_linked_list(new_leaf_ptr, inner_node, new_leaf_key_byte);

                    (inner_node_ptr.to_opaque(), new_leaf_ptr, new_leaf_key_byte)
                }
            }

            match inner_node_ptr.to_node_ptr() {
                ConcreteNodePtr::Node4(inner_ptr) => write_new_child_in_existing_inner_node(
                    inner_ptr,
                    new_leaf_node,
                    key_bytes_used,
                    alloc,
                ),
                ConcreteNodePtr::Node16(inner_ptr) => write_new_child_in_existing_inner_node(
                    inner_ptr,
                    new_leaf_node,
                    key_bytes_used,
                    alloc,
                ),
                ConcreteNodePtr::Node48(inner_ptr) => write_new_child_in_existing_inner_node(
                    inner_ptr,
                    new_leaf_node,
                    key_bytes_used,
                    alloc,
                ),
                ConcreteNodePtr::Node256(inner_ptr) => write_new_child_in_existing_inner_node(
                    inner_ptr,
                    new_leaf_node,
                    key_bytes_used,
                    alloc,
                ),
                ConcreteNodePtr::LeafNode(_) => {
                    unreachable!("Cannot have insert into existing with leaf node");
                },
            }
        }

        let InsertPoint {
            path,
            insert_kind: insert_type,
            key_bytes_used,
            root,
            ..
        } = self;

        let (new_inner_node, leaf_node_ptr, leaf_node_key_byte) = match insert_type {
            InsertKind::MismatchPrefix {
                mismatch,
                mismatched_inner_node_ptr,
            } => {
                // SAFETY: The lifetime of the header reference is restricted to this block and
                // within the block no other access occurs. The requirements of
                // the "no concurrent (read or write) access" is also enforced by the
                // `apply` caller requirements.
                let key_bytes = key.as_bytes();

                #[allow(unused_unsafe)]
                unsafe {
                    // SAFETY: Since we are iterating the key and prefixes, we
                    // expect that the depth never exceeds the key len.
                    // Because if this happens we ran out of bytes in the key to match
                    // and the whole process should be already finished
                    assume!(key_bytes_used + mismatch.matched_bytes < key_bytes.len());
                }

                let key_byte = key_bytes[key_bytes_used + mismatch.matched_bytes];

                let new_leaf_pointer =
                    NodePtr::allocate_node_ptr(LeafNode::with_no_siblings(key, value), alloc);
                let new_leaf_pointer_opaque = new_leaf_pointer.to_opaque();

                let mut new_n4 = {
                    // SAFETY: The lifetime of the header reference is bounded to this block and no
                    // current mutation happens. Also, we know this is an inner node pointer because
                    // of the specific insert case
                    let header = unsafe { mismatched_inner_node_ptr.header_ref_unchecked() };

                    // prefix mismatch, need to split prefix into two separate nodes and take the
                    // common prefix into a new parent node
                    let prefix = header.read_prefix();
                    let prefix = &prefix[..prefix.len().min(mismatch.matched_bytes)];
                    InnerNode4::from_prefix(prefix, mismatch.matched_bytes)
                };

                unsafe {
                    // SAFETY: This is a new node 4 so it's empty and we have
                    // space for writing new children. We also check the order
                    // of the keys before writing
                    if mismatch.prefix_byte < key_byte {
                        new_n4
                            .write_child_unchecked(mismatch.prefix_byte, mismatched_inner_node_ptr);
                        new_n4.write_child_unchecked(key_byte, new_leaf_pointer_opaque);

                        // SAFETY: There are no concurrent modifications, the `apply` safety doc
                        // covers this
                        let previous_leaf_ptr = maximum_unchecked(mismatched_inner_node_ptr);

                        // SAFETY: There is no concurrent modification of the new leaf node, the
                        // the `apply` function.
                        LeafNode::insert_after(new_leaf_pointer, previous_leaf_ptr);
                    } else {
                        new_n4.write_child_unchecked(key_byte, new_leaf_pointer_opaque);
                        new_n4
                            .write_child_unchecked(mismatch.prefix_byte, mismatched_inner_node_ptr);

                        // SAFETY: There are no concurrent modifications, the `apply` safety doc
                        // covers this
                        let next_leaf_ptr = minimum_unchecked(mismatched_inner_node_ptr);

                        // SAFETY: There is no concurrent modification of the new leaf node, the
                        // existing leaf node, or its siblings because of the safety requirements of
                        // the `apply` function.
                        LeafNode::insert_before(new_leaf_pointer, next_leaf_ptr);
                    }
                }

                {
                    // Scope header mutation so that the mutable reference is held for the minimum
                    // time required

                    // SAFETY: We hold a mutable reference, so creating a mutable reference is safe.
                    // We also know for certain that this is an inner node pointer, because of the
                    // insert case we're in
                    let header = unsafe { mismatched_inner_node_ptr.header_mut_unchecked() };

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
                }

                (
                    NodePtr::allocate_node_ptr(new_n4, alloc).to_opaque(),
                    new_leaf_pointer,
                    key_byte,
                )
            },
            InsertKind::Exact { leaf_node_ptr } => {
                let new_leaf_node = LeafNode::with_no_siblings(key, value);

                // SAFETY: The leaf node will not be accessed concurrently because of the safety
                // doc on the containing function
                let mut old_leaf_node = unsafe { NodePtr::replace(leaf_node_ptr, new_leaf_node) };

                // SAFETY: There is no concurrent modification of the new leaf node, old leaf
                // node, or its siblings because of the safety requirements of the `apply`
                // function
                unsafe { LeafNode::replace(leaf_node_ptr, &mut old_leaf_node, false) };

                return InsertResult {
                    leaf_node_ptr,
                    existing_leaf: Some(old_leaf_node),
                    // Because we replaced the leaf instead of creating a new leaf, we don't
                    // have to write back to the parent. In this case,
                    // the root is guaranteed to be unchanged, even if
                    // the old leaf was the root.
                    new_root: root,
                    parent_node_change: InsertParentNodeChange::NoChange,
                    marker: PhantomData,
                };
            },
            InsertKind::SplitLeaf {
                leaf_node_ptr,
                new_key_bytes_used,
            } => {
                let key_bytes = key.as_bytes();
                // SAFETY: We hold a mutable reference, so creating a shared reference is safe
                let leaf_bytes = unsafe { leaf_node_ptr.as_key_ref().as_bytes() };

                #[allow(unused_unsafe)]
                unsafe {
                    // SAFETY: When reaching this point in the insertion process this invariant
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
                let new_leaf_node_pointer =
                    NodePtr::allocate_node_ptr(LeafNode::with_no_siblings(key, value), alloc);

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

                        // SAFETY: There is no concurrent modification of the new leaf node, the
                        // existing leaf node, or its siblings because of the safety requirements of
                        // the `apply` function.
                        LeafNode::insert_after(new_leaf_node_pointer, leaf_node_ptr);
                    } else {
                        new_n4.write_child_unchecked(
                            new_leaf_node_key_byte,
                            new_leaf_node_pointer.to_opaque(),
                        );
                        new_n4.write_child_unchecked(leaf_node_key_byte, leaf_node_ptr.to_opaque());

                        // SAFETY: There is no concurrent modification of the new leaf node, the
                        // existing leaf node, or its siblings because of the safety requirements of
                        // the `apply` function.
                        LeafNode::insert_before(new_leaf_node_pointer, leaf_node_ptr);
                    }
                }

                (
                    NodePtr::allocate_node_ptr(new_n4, alloc).to_opaque(),
                    new_leaf_node_pointer,
                    new_leaf_node_key_byte,
                )
            },
            InsertKind::IntoExisting { inner_node_ptr } => write_new_child_in_existing_node(
                inner_node_ptr,
                LeafNode::with_no_siblings(key, value),
                key_bytes_used,
                alloc,
            ),
        };

        match path {
            TreePath::Root => {
                // If there was no parent, then the root node was a leaf or the inner node split
                // occurred at the root, in which case return the new inner node as root
                InsertResult {
                    leaf_node_ptr,
                    existing_leaf: None,
                    new_root: new_inner_node,
                    parent_node_change: InsertParentNodeChange::NewParent {
                        new_parent_node: new_inner_node,
                        leaf_node_key_byte,
                    },
                    marker: PhantomData,
                }
            },
            TreePath::ChildOfRoot {
                parent,
                child_key_byte,
            }
            | TreePath::Normal {
                parent,
                child_key_byte,
                ..
            } => {
                // TODO(#14) Change this write back to parent to only happen when a new inner
                // node is created (MismatchPrefix & SplitLeaf (when it is not an overwrite of
                // the existing leaf))
                unsafe {
                    parent_write_child(parent, child_key_byte, new_inner_node);
                }

                // If there was a parent either:
                //   1. Root was the parent, in which case it was unchanged
                //   2. Or some parent of the parent was root, in which case it was unchanged
                InsertResult {
                    leaf_node_ptr,
                    existing_leaf: None,
                    new_root: root,
                    parent_node_change: InsertParentNodeChange::NewParent {
                        new_parent_node: new_inner_node,
                        leaf_node_key_byte,
                    },
                    marker: PhantomData,
                }
            },
        }
    }
}

/// The type of insert
pub enum InsertKind<K, V, const PREFIX_LEN: usize> {
    /// An insert where an inner node had a differing prefix from the key.
    ///
    /// This insert type will create a new inner node with the portion of
    /// the prefix that did match, and update the existing inner node
    MismatchPrefix {
        /// Data about the matching if the prefix
        mismatch: ExplicitMismatch<K, V, PREFIX_LEN>,
        /// A pointer to the inner node which had a mismatched prefix
        mismatched_inner_node_ptr: OpaqueNodePtr<K, V, PREFIX_LEN>,
    },
    /// An insert where the node to be added matched all the way up to a
    /// leaf node.
    ///
    /// This insert type will create a new inner node, and assign the
    /// existing leaf and the new leaf as children to that node.
    SplitLeaf {
        /// A pointer to the leaf node that will be split
        leaf_node_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
        new_key_bytes_used: usize,
    },
    /// Exact match of the leaf was found
    ///
    /// This insert type will replace the older leaf with a new one
    Exact {
        /// A pointer to the leaf node that will be split
        leaf_node_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    },
    /// An insert where the search terminated at an existing inner node that
    /// did not have a child with the key byte.
    ///
    /// If the inner node is full, it will be grown to the next largest
    /// size.
    IntoExisting {
        /// A pointer to the existing inner node which will be updated to
        /// contain the new child leaf node
        inner_node_ptr: OpaqueNodePtr<K, V, PREFIX_LEN>,
    },
}

impl<K, V, const PREFIX_LEN: usize> Copy for InsertKind<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> Clone for InsertKind<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for InsertKind<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchPrefix {
                mismatch,
                mismatched_inner_node_ptr,
            } => f
                .debug_struct("MismatchPrefix")
                .field("mismatch", mismatch)
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

/// This enum contains the results from searching for an forced insert point for
/// a new node in the trie.
///
/// It contains all the relevant information needed to perform the insert
/// and update the tree.
///
/// A forced insert is either a normal insert, or a node that must be completely
/// overwritten.
pub enum ForceInsertPoint<K, V, const PREFIX_LEN: usize> {
    InsertPoint(InsertPoint<K, V, PREFIX_LEN>),
    OverwritePoint(OverwritePoint<K, V, PREFIX_LEN>),
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for ForceInsertPoint<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InsertPoint(insert_point) => f
                .debug_tuple("ForceInsertPoint::InsertPoint")
                .field(insert_point)
                .finish(),
            Self::OverwritePoint(overwrite_point) => f
                .debug_tuple("ForceInsertPoint::OverwritePoint")
                .field(overwrite_point)
                .finish(),
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> ForceInsertPoint<K, V, PREFIX_LEN> {
    /// This function will use [`ForceInsertPoint`] information to insert the
    /// given key-value pair into the trie.
    ///
    /// # Safety
    ///
    ///  - This function must not be called concurrently with and other read or
    ///    modification of the trie.
    ///  - The given allocator must be the same one that was used to allocate
    ///    the nodes of this trie.
    pub unsafe fn apply<'a, A>(
        self,
        key: K,
        value: V,
        alloc: &A,
    ) -> ForceInsertResult<'a, K, V, PREFIX_LEN>
    where
        K: AsBytes + 'a,
        V: 'a,
        A: Allocator,
    {
        match self {
            Self::InsertPoint(insert_point) => ForceInsertResult {
                // Safety: covered by function doc comment.
                insert_result: unsafe { insert_point.apply(key, value, alloc) },
                leafs_removed: 0,
            },
            Self::OverwritePoint(overwrite_point) =>
            // Safety: covered by function doc comment.
            unsafe { overwrite_point.apply(key, value, alloc) },
        }
    }
}

/// Contains all the information needed to overwrite a certain node.
pub struct OverwritePoint<K, V, const PREFIX_LEN: usize> {
    /// The path to point where the new leaf will be inserted.
    pub path: TreePath<K, V, PREFIX_LEN>,
    /// The pointer to the node that will be overwritten.
    pub overwrite_point: OpaqueNodePtr<K, V, PREFIX_LEN>,
    /// The number of bytes that were read from the key to find the insert
    /// point.
    pub key_bytes_used: usize,
    /// Current root of the tree, used in the apply
    pub root: OpaqueNodePtr<K, V, PREFIX_LEN>,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for OverwritePoint<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OverwritePoint")
            .field("path", &self.path)
            .field("overwrite_point", &self.overwrite_point)
            .field("key_bytes_used", &self.key_bytes_used)
            .field("root", &self.root)
            .finish()
    }
}

/// The results of a successful force insert.
#[derive(Debug)]
pub struct ForceInsertResult<'a, K, V, const PREFIX_LEN: usize> {
    pub insert_result: InsertResult<'a, K, V, PREFIX_LEN>,
    pub leafs_removed: usize,
}

impl<K, V, const PREFIX_LEN: usize> OverwritePoint<K, V, PREFIX_LEN> {
    /// This function will use [`OverwritePoint`] information to remove a set of
    /// node and insert the given key-value pair into the correct spot of
    /// the trie.
    ///
    /// # Safety
    ///
    ///  - This function must not be called concurrently with and other read or
    ///    modification of the trie.
    ///  - The given allocator must be the same one that was used to allocate
    ///    the nodes of this trie.
    pub unsafe fn apply<'a, A>(
        self,
        key: K,
        value: V,
        alloc: &A,
    ) -> ForceInsertResult<'a, K, V, PREFIX_LEN>
    where
        K: AsBytes + 'a,
        V: 'a,
        A: Allocator,
    {
        fn set_leaf_siblings<K: AsBytes, V, const PREFIX_LEN: usize>(
            parent_inner_node: OpaqueNodePtr<K, V, PREFIX_LEN>,
            overwrite_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
        ) {
            /// Write a new child node to an inner node at the specified key
            /// byte.
            fn set_single_leaf_siblings<K: AsBytes, V, const PREFIX_LEN: usize>(
                parent_inner_node: OpaqueNodePtr<K, V, PREFIX_LEN>,
                overwrite_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
                previous: bool,
            ) {
                match parent_inner_node.to_node_ptr() {
                    ConcreteNodePtr::Node4(inner_ptr) => {
                        // Safety: covered by parents parent function doc comment.
                        let inner_ref = unsafe { inner_ptr.as_ref() };
                        let next_node = if previous {
                            inner_ref.min().1
                        } else {
                            inner_ref.max().1
                        };
                        set_single_leaf_siblings(next_node, overwrite_leaf, previous);
                    },
                    ConcreteNodePtr::Node16(inner_ptr) => {
                        // Safety: covered by parents parent function doc comment.
                        let inner_ref = unsafe { inner_ptr.as_ref() };
                        let next_node = if previous {
                            inner_ref.min().1
                        } else {
                            inner_ref.max().1
                        };
                        set_single_leaf_siblings(next_node, overwrite_leaf, previous);
                    },
                    ConcreteNodePtr::Node48(inner_ptr) => {
                        // Safety: covered by parents parent function doc comment.
                        let inner_ref = unsafe { inner_ptr.as_ref() };
                        let next_node = if previous {
                            inner_ref.min().1
                        } else {
                            inner_ref.max().1
                        };
                        set_single_leaf_siblings(next_node, overwrite_leaf, previous);
                    },
                    ConcreteNodePtr::Node256(inner_ptr) => {
                        // Safety: covered by parents parent function doc comment.
                        let inner_ref = unsafe { inner_ptr.as_ref() };
                        let next_node = if previous {
                            inner_ref.min().1
                        } else {
                            inner_ref.max().1
                        };
                        set_single_leaf_siblings(next_node, overwrite_leaf, previous);
                    },
                    ConcreteNodePtr::LeafNode(leaf) => {
                        if previous {
                            // Safety: covered by parents parent function doc comment.
                            let previous_node = unsafe { leaf.as_mut() }.previous;
                            if let Some(previous_node) = previous_node {
                                // Safety: covered by parents parent function doc comment.
                                unsafe { previous_node.as_mut() }.next = Some(overwrite_leaf);
                            }
                            // Safety: covered by parents parent function doc comment.
                            unsafe { overwrite_leaf.as_mut() }.previous = previous_node;
                        } else {
                            // Safety: covered by parents parent function doc comment.
                            let next_node = unsafe { leaf.as_mut() }.next;
                            if let Some(previous_node) = next_node {
                                // Safety: covered by parents parent function doc comment.
                                unsafe { previous_node.as_mut() }.previous = Some(overwrite_leaf);
                            }
                            // Safety: covered by parents parent function doc comment.
                            unsafe { overwrite_leaf.as_mut() }.next = next_node;
                        }
                    },
                }
            }
            set_single_leaf_siblings(parent_inner_node, overwrite_leaf, true);
            set_single_leaf_siblings(parent_inner_node, overwrite_leaf, false);
        }
        let OverwritePoint {
            path,
            overwrite_point,
            root,
            ..
        } = self;
        let overwrite_leaf = LeafNode::with_no_siblings(key, value);

        let (overwrite_ptr, leafs_removed) = match overwrite_point.to_node_ptr() {
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                // SAFETY: Covered by safety doc of this function
                let mut old_leaf_node = unsafe { NodePtr::replace(leaf_node_ptr, overwrite_leaf) };

                // SAFETY: Covered by safety doc of this function
                unsafe { LeafNode::replace(leaf_node_ptr, &mut old_leaf_node, true) };
                return ForceInsertResult {
                    insert_result: InsertResult {
                        leaf_node_ptr,
                        existing_leaf: Some(old_leaf_node),
                        // Because we replaced the leaf instead of creating a new leaf, we don't
                        // have to write back to the parent. In this case,
                        // the root is guaranteed to be unchanged, even if
                        // the old leaf was the root.
                        new_root: root,
                        parent_node_change: InsertParentNodeChange::NoChange,
                        marker: PhantomData,
                    },
                    leafs_removed: 0,
                };
            },
            ConcreteNodePtr::Node4(old_inner) => {
                let overwrite_ptr = NodePtr::allocate_node_ptr(overwrite_leaf, alloc);
                set_leaf_siblings(old_inner.to_opaque(), overwrite_ptr);
                // SAFETY: We never use `old_inner` after this call again.
                // The rest is covered by the doc comment.
                let removed = unsafe { deallocate_tree(old_inner.to_opaque(), alloc) };
                (overwrite_ptr, removed)
            },
            ConcreteNodePtr::Node16(old_inner) => {
                let overwrite_ptr = NodePtr::allocate_node_ptr(overwrite_leaf, alloc);
                set_leaf_siblings(old_inner.to_opaque(), overwrite_ptr);
                // SAFETY: We never use `old_inner` after this call again.
                // The rest is covered by the doc comment.
                let removed = unsafe { deallocate_tree(old_inner.to_opaque(), alloc) };
                (overwrite_ptr, removed)
            },
            ConcreteNodePtr::Node48(old_inner) => {
                let overwrite_ptr = NodePtr::allocate_node_ptr(overwrite_leaf, alloc);
                set_leaf_siblings(old_inner.to_opaque(), overwrite_ptr);
                // SAFETY: We never use `old_inner` after this call again.
                // The rest is covered by the doc comment.
                let removed = unsafe { deallocate_tree(old_inner.to_opaque(), alloc) };
                (overwrite_ptr, removed)
            },
            ConcreteNodePtr::Node256(old_inner) => {
                let overwrite_ptr = NodePtr::allocate_node_ptr(overwrite_leaf, alloc);
                set_leaf_siblings(old_inner.to_opaque(), overwrite_ptr);
                // SAFETY: We never use `old_inner` after this call again.
                // The rest is covered by the doc comment.
                let removed = unsafe { deallocate_tree(old_inner.to_opaque(), alloc) };
                (overwrite_ptr, removed)
            },
        };
        match path {
            TreePath::Root => {
                // If there was no parent, we overwrote the root leaf.
                ForceInsertResult {
                    insert_result: InsertResult {
                        leaf_node_ptr: overwrite_ptr,
                        existing_leaf: None,
                        new_root: overwrite_ptr.to_opaque(),
                        parent_node_change: InsertParentNodeChange::NoChange,
                        marker: PhantomData,
                    },
                    leafs_removed,
                }
            },
            TreePath::ChildOfRoot {
                parent,
                child_key_byte,
            }
            | TreePath::Normal {
                parent,
                child_key_byte,
                ..
            } => {
                unsafe { parent_write_child(parent, child_key_byte, overwrite_ptr.to_opaque()) };

                // If there was a parent we will have written a different pointer to the
                // `child_key_byte`, but the parent never changed.
                ForceInsertResult {
                    insert_result: InsertResult {
                        leaf_node_ptr: overwrite_ptr,
                        existing_leaf: None,
                        new_root: root,
                        parent_node_change: InsertParentNodeChange::NoChange,
                        marker: PhantomData,
                    },
                    leafs_removed,
                }
            },
        }
    }
}

/// Check that the given inner node's prefix matches the relevant subslice of
/// the given key.
///
/// # Safety
///  - This function cannot be called concurrently to any writes of the `root`
///    node or any child node of `root`. This function will arbitrarily read to
///    any child in the given tree.
///  - `current_depth` must be less than or equal to `key.len()`
    #[inline]
unsafe fn test_prefix_identify_insert<K, V, N, const PREFIX_LEN: usize>(
        inner_ptr: NodePtr<PREFIX_LEN, N>,
        key: &[u8],
        current_depth: &mut usize,
    ) -> Result<
        ControlFlow<ExplicitMismatch<K, V, PREFIX_LEN>, Option<OpaqueNodePtr<K, V, PREFIX_LEN>>>,
        InsertPrefixError,
    >
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
        K: AsBytes,
    {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `search_unchecked` function.
        let inner_node = unsafe { inner_ptr.as_ref() };
// SAFETY: Covered by caller safety requirements on `current_depth` and
    // `key.len()`
        let match_prefix = unsafe { inner_node.match_full_prefix(key, *current_depth) };
        match match_prefix {
            Err(mismatch) => Ok(ControlFlow::Break(mismatch)),
            Ok(PrefixMatch { matched_bytes }) => {
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

    /// Perform an iterative search for the insert point for the given key,
/// starting at the given root node.
///
/// # Safety
///  - This function cannot be called concurrently to any writes of the `root`
///    node or any child node of `root`. This function will arbitrarily read to
///    any child in the given tree.
///
/// # Errors
///  - If the given `key` is a prefix of an existing key, this function will
///    return an error.
pub unsafe fn search_for_insert_point<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
) -> Result<InsertPoint<K, V, PREFIX_LEN>, InsertPrefixError>
where
    K: AsBytes,
{
    let mut path = TreePathSearch::default();
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
// SAFETY (covering all `test_prefix_identify_insert` function calls):
        //  1. Concurrent read/write overed by caller safety requirements
        //  2. `current_depth` can never be greater than `key_bytes.len()` because of
        //     loop invariant assertion
        assert!(current_depth <= key_bytes.len());

        let lookup_result = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
// SAFETY: comment and assert at top of loop
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
// SAFETY: comment and assert at top of loop
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
// SAFETY: comment and assert at top of loop
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
// SAFETY: comment and assert at top of loop
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                let leaf_node = leaf_node_ptr.read();

                if leaf_node.matches_full_key(key_bytes) {
                    return Ok(InsertPoint {
                        key_bytes_used: current_depth,
                        path: path.finish(),
                        insert_kind: InsertKind::Exact { leaf_node_ptr },
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
                    path: path.finish(),
                    insert_kind: InsertKind::SplitLeaf {
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
                        let byte = key_bytes[current_depth];
                        path.visit_inner_node(current_node, byte);
                        current_node = next_child_node;
                        // Increment by a single byte
                        current_depth += 1;
                    },
                    None => {
                        return Ok(InsertPoint {
                            key_bytes_used: current_depth,
                            insert_kind: InsertKind::IntoExisting {
                                inner_node_ptr: current_node,
                            },
                            path: path.finish(),
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
                    insert_kind: InsertKind::MismatchPrefix {
                        mismatch,
                        mismatched_inner_node_ptr: current_node,
                    },
                    path: path.finish(),
                    root,
                });
            },
        };
    }
}

/// Perform an iterative search for the insert point for the given key,
/// starting at the given root node.
///
/// # Safety
///  - This function cannot be called concurrently to any writes of the `root`
///    node or any child node of `root`. This function will arbitrarily read to
///    any child in the given tree.
///
/// # Errors
///  - If the given `key` is a prefix of an existing key, this function will
///    return an error.
pub unsafe fn search_for_force_insert_point<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
) -> ForceInsertPoint<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    let mut path = TreePathSearch::default();
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
// SAFETY (covering all `test_prefix_identify_insert` function calls):
        //  1. Concurrent read/write overed by caller safety requirements
        //  2. `current_depth` can never be greater than `key_bytes.len()` because of
        //     loop invariant assertion
        assert!(current_depth <= key_bytes.len());

        let lookup_result = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
// SAFETY: comment and assert at top of loop
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
// SAFETY: comment and assert at top of loop
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
// SAFETY: comment and assert at top of loop
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
// SAFETY: comment and assert at top of loop
                test_prefix_identify_insert(inner_ptr, key_bytes, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                let leaf_node = leaf_node_ptr.read();

                if leaf_node.matches_full_key(key_bytes) {
                    return ForceInsertPoint::InsertPoint(InsertPoint {
                        key_bytes_used: current_depth,
                        path: path.finish(),
                        insert_kind: InsertKind::Exact { leaf_node_ptr },
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

                if new_key_bytes_used >= key_bytes.len() || new_key_bytes_used >= leaf_bytes.len() {
                    // then the key has insufficient bytes to be unique. It must be
                    // a prefix of an existing key OR an existing key is a prefix of it
                    return ForceInsertPoint::OverwritePoint(OverwritePoint {
                        key_bytes_used: current_depth,
                        path: path.finish(),
                        overwrite_point: leaf_node_ptr.to_opaque(),
                        root,
                    });
                }

                return ForceInsertPoint::InsertPoint(InsertPoint {
                    key_bytes_used: current_depth,
                    path: path.finish(),
                    insert_kind: InsertKind::SplitLeaf {
                        leaf_node_ptr,
                        new_key_bytes_used,
                    },
                    root,
                });
            },
        };

        let lookup_result = match lookup_result {
            Ok(value) => value,
            Err(_inner_node_ptr) => {
                return ForceInsertPoint::OverwritePoint(OverwritePoint {
                    key_bytes_used: current_depth.saturating_sub(1),
                    path: path.finish(),
                    overwrite_point: current_node,
                    root,
                });
            },
        };

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
                        let byte = key_bytes[current_depth];
                        path.visit_inner_node(current_node, byte);
                        current_node = next_child_node;
                        // Increment by a single byte
                        current_depth += 1;
                    },
                    None => {
                        return ForceInsertPoint::InsertPoint(InsertPoint {
                            key_bytes_used: current_depth,
                            insert_kind: InsertKind::IntoExisting {
                                inner_node_ptr: current_node,
                            },
                            path: path.finish(),
                            root,
                        })
                    },
                }
            },
            ControlFlow::Break(mismatch) => {
                if (current_depth + mismatch.matched_bytes) >= key_bytes.len() {
                    // then the key has insufficient bytes to be unique. It must be
                    // a prefix of an existing key

                    return ForceInsertPoint::OverwritePoint(OverwritePoint {
                        key_bytes_used: current_depth,
                        path: path.finish(),
                        overwrite_point: current_node,
                        root,
                    });
                }

                return ForceInsertPoint::InsertPoint(InsertPoint {
                    key_bytes_used: current_depth,
                    insert_kind: InsertKind::MismatchPrefix {
                        mismatch,
                        mismatched_inner_node_ptr: current_node,
                    },
                    path: path.finish(),
                    root,
                });
            },
        };
    }
}

#[cfg(test)]
mod tests;
