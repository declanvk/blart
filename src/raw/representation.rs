//! Trie node representation

use core::{
    cmp::Ordering,
    fmt,
    iter::FusedIterator,
    marker::PhantomData,
    ops::{Bound, RangeBounds, RangeInclusive},
};

use crate::{rust_nightly_apis::likely, AsBytes};

mod header;
pub use header::*;

mod inner_node_direct;
pub use inner_node_direct::*;

mod inner_node_indirect;
pub use inner_node_indirect::*;

mod inner_node_sorted;
pub use inner_node_sorted::*;

mod leaf_node;
pub use leaf_node::*;

mod pointers;
pub use pointers::*;

/// The representation of inner nodes
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum NodeType {
    /// Node that references between 2 and 4 children
    Node4 = 0b000,
    /// Node that references between 5 and 16 children
    Node16 = 0b001, // 0b001
    /// Node that references between 17 and 48 children
    Node48 = 0b010, // 0b010
    /// Node that references between 49 and 256 children
    Node256 = 0b011, // 0b011
    /// Node that contains a single value
    Leaf = 0b100, // 0b100
}

impl NodeType {
    /// Converts a u8 value to a [`NodeType`]
    ///
    /// # Safety
    ///  - `src` must be a valid variant from the enum
    const unsafe fn from_u8(src: u8) -> NodeType {
        // SAFETY: `NodeType` is repr(u8)
        unsafe { core::mem::transmute::<u8, NodeType>(src) }
    }

    /// Return true if an [`InnerNode`] with the given [`NodeType`] and
    /// specified number of children should be shrunk.
    ///
    /// # Panics
    ///  - Panics if `node_type` equals [`NodeType::Leaf`]
    pub fn should_shrink_inner_node(self, num_children: usize) -> bool {
        match self {
            NodeType::Node4 => false,
            NodeType::Leaf => panic!("cannot shrink leaf"),
            _ => num_children < *self.capacity_range().start(),
        }
    }

    /// Return the range of number of children that each node type accepts.
    pub const fn capacity_range(self) -> RangeInclusive<usize> {
        match self {
            NodeType::Node4 => 2..=4,
            NodeType::Node16 => 5..=16,
            NodeType::Node48 => 17..=48,
            NodeType::Node256 => 49..=256,
            NodeType::Leaf => 0..=0,
        }
    }
}

pub(crate) mod private {
    /// This trait is used to seal other traits, such that they cannot be
    /// implemented outside of the crate.
    pub trait Sealed {}

    impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> Sealed
        for super::InnerNodeSorted<K, V, PREFIX_LEN, SIZE>
    {
    }
    impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> Sealed
        for super::InnerNodeIndirect<K, V, PREFIX_LEN, SIZE>
    {
    }
    impl<K, V, const PREFIX_LEN: usize> Sealed for super::InnerNodeDirect<K, V, PREFIX_LEN> {}
    impl<K, V, const PREFIX_LEN: usize> Sealed for super::LeafNode<K, V, PREFIX_LEN> {}

    /// Internal construction trait for inner nodes.
    ///
    /// This is `pub(crate)` so external users cannot access `from_header`,
    /// `empty`, or `from_prefix` directly — use [`super::InnerNodeBuilder`]
    /// from the public API instead.
    pub trait InnerNodeInit<const PREFIX_LEN: usize>: Sealed + Sized {
        fn from_header(header: super::Header<PREFIX_LEN>) -> Self;

        fn from_prefix(prefix: &[u8], prefix_len: usize) -> Self {
            Self::from_header(super::Header::new(prefix, prefix_len))
        }
    }

    impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> InnerNodeInit<PREFIX_LEN>
        for super::InnerNodeSorted<K, V, PREFIX_LEN, SIZE>
    {
        fn from_header(header: super::Header<PREFIX_LEN>) -> Self {
            use core::mem::MaybeUninit;
            Self {
                header,
                child_pointers: [MaybeUninit::uninit(); SIZE],
                keys: [0; SIZE],
            }
        }
    }

    impl<K, V, const PREFIX_LEN: usize, const SIZE: usize> InnerNodeInit<PREFIX_LEN>
        for super::InnerNodeIndirect<K, V, PREFIX_LEN, SIZE>
    {
        fn from_header(header: super::Header<PREFIX_LEN>) -> Self {
            use core::mem::MaybeUninit;
            super::InnerNodeIndirect {
                header,
                child_indices: [None; 256],
                child_pointers: [MaybeUninit::uninit(); SIZE],
            }
        }
    }

    impl<K, V, const PREFIX_LEN: usize> InnerNodeInit<PREFIX_LEN>
        for super::InnerNodeDirect<K, V, PREFIX_LEN>
    {
        fn from_header(header: super::Header<PREFIX_LEN>) -> Self {
            super::InnerNodeDirect {
                header,
                child_pointers: [None; 256],
            }
        }
    }
}

/// All nodes which contain a runtime tag that validates their type.
pub trait Node<const PREFIX_LEN: usize>: private::Sealed {
    // TODO: See if possible to remove PREFIX_LEN generic from this trait

    /// The runtime type of the node.
    const TYPE: NodeType;

    /// The key type carried by the leaf nodes
    type Key;

    /// The value type carried by the leaf nodes
    type Value;
}

/// This struct represents a successful match against a prefix using either the
/// [`InnerNodeCommon::optimistic_match_prefix`] or
/// [`InnerNodeCommon::match_full_prefix`] functions.
#[derive(Debug)]
pub struct PrefixMatch {
    /// How many bytes were matched
    pub matched_bytes: usize,
}

/// This struct represents a successful match against a prefix using the
/// [`InnerNodeCommon::attempt_pessimistic_match_prefix`] function.
#[derive(Debug)]
pub struct AttemptOptimisticPrefixMatch {
    /// How many bytes were matched
    pub matched_bytes: usize,
    /// This flag will be true if the `attempt_pessimistic_match_prefix`
    /// function fell back to an optimistic mode, and assumed prefix match by
    /// key length.
    pub any_implicit_bytes: bool,
}

/// Represents a prefix mismatch when looking at the entire prefix, including in
/// cases where it is read from a child leaf node.
pub struct ExplicitMismatch<K, V, const PREFIX_LEN: usize> {
    /// How many bytes were matched
    pub matched_bytes: usize,
    /// Value of the byte that made it not match
    pub prefix_byte: u8,
    /// Pointer to the leaf if the prefix was reconstructed
    pub leaf_ptr: OptionalLeafPtr<K, V, PREFIX_LEN>,
    /// Comparison between the full prefix and the relevant key segment
    pub node_prefix_comparison_to_search_key_segment: Ordering,
}

impl<K, V, const PREFIX_LEN: usize> Clone for ExplicitMismatch<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PREFIX_LEN: usize> Copy for ExplicitMismatch<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for ExplicitMismatch<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Mismatch")
            .field("matched_bytes", &self.matched_bytes)
            .field("prefix_byte", &self.prefix_byte)
            .field("leaf_ptr", &self.leaf_ptr)
            .finish()
    }
}

/// Represents a prefix mismatch when looking only at the prefix content present
/// in an [`InnerNode`] header.
#[derive(Debug)]
pub struct PessimisticMismatch {
    /// How many bytes were matched
    pub matched_bytes: usize,
    /// Value of the byte that made it not match.
    ///
    /// If this field is `None`, then the mismatch happened in the implicit
    /// prefix bytes.
    pub prefix_byte: Option<u8>,
}

impl From<OptimisticMismatch> for PessimisticMismatch {
    fn from(value: OptimisticMismatch) -> Self {
        Self {
            matched_bytes: value.matched_bytes,
            prefix_byte: None,
        }
    }
}

/// Represents a prefix mismatch when looking only at the prefix content present
/// in an [`InnerNode`] header.
#[derive(Debug)]
pub struct OptimisticMismatch {
    /// How many bytes were matched
    pub matched_bytes: usize,
}

/// This trait contains all the functions/types that every inner node must
/// implement.
///
/// This doesn't necessarily mean that the specific type will be used as an
/// inner node, since that requires assigning it a [`NodeType`] and determining
/// its "grow"/"shrink" order. See [`InnerNode`] for those details.
///
/// # Safety
///
/// All structures that implement this trait must be `repr(C)` and have a
/// [`Header`] as the first field of the struct.
pub unsafe trait InnerNodeCommon<K, V, const PREFIX_LEN: usize>:
    Sized + private::InnerNodeInit<PREFIX_LEN>
{
    /// The type of the iterator over all children of the inner node
    type Iter<'a>: Iterator<Item = (u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>
        + DoubleEndedIterator
        + FusedIterator
    where
        Self: 'a;

    /// Create a builder for constructing an inner node with at least one child.
    ///
    /// The builder uses the typestate pattern to ensure
    /// [`InnerNodeBuilder::build`] cannot be called until at least one
    /// child has been added via [`InnerNodeBuilder::write_child`].
    fn builder(
        prefix: &[u8],
        prefix_len: usize,
    ) -> InnerNodeBuilder<K, V, PREFIX_LEN, Self, NoChild> {
        InnerNodeBuilder {
            node: <Self as private::InnerNodeInit<PREFIX_LEN>>::from_prefix(prefix, prefix_len),
            _state: PhantomData,
        }
    }

    /// Get the `Header` from the [`InnerNode`]
    fn header(&self) -> &Header<PREFIX_LEN>;

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>>;

    /// Write a child pointer with key fragment to this inner node.
    ///
    /// If the key fragment already exists in the node, overwrite the existing
    /// child pointer.
    ///
    /// # Panics
    ///  - Panics when the node is full.
    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>);

    /// Attempt to remove a child pointer at the key fragment from this inner
    /// node.
    ///
    /// If the key fragment does not exist in this node, return `None`.
    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>>;

    /// Create an iterator over all `(key bytes, child pointers)` in this inner
    /// node.
    fn iter(&self) -> Self::Iter<'_>;

    /// Create an iterator over a subset of `(key bytes, child pointers)`, using
    /// the given `bound` as a restriction on the set of key bytes.
    fn range(
        &self,
        bound: impl RangeBounds<u8>,
    ) -> impl DoubleEndedIterator<Item = (u8, OpaqueNodePtr<K, V, PREFIX_LEN>)> + FusedIterator;

    /// Test the given key against the inner node header prefix by checking that
    /// the key length is greater than or equal to the length of the header
    /// prefix.
    ///
    /// The `truncated_key` argument should be the overall key bytes shortened
    /// to the current depth.
    ///
    /// This is called "optimistic" matching, because it assumes that there will
    /// not be a mismatch in the contents of the header prefix when compared to
    /// the key. The caller who uses this function must perform a final check
    /// against the leaf key bytes to make sure that the search key matches the
    /// found key.
    ///
    /// # Errors
    /// This function returns an error if there is a mismatch between the
    /// partial stored prefix and the given truncated key.
    #[inline]
    fn optimistic_match_prefix(
        &self,
        truncated_key: &[u8],
    ) -> Result<PrefixMatch, OptimisticMismatch> {
        if truncated_key.len() < self.header().prefix_len() {
            Err(OptimisticMismatch {
                matched_bytes: truncated_key.len(),
            })
        } else {
            Ok(PrefixMatch {
                matched_bytes: self.header().prefix_len(),
            })
        }
    }

    /// Test the given key against the inner node header prefix by comparing the
    /// bytes.
    ///
    /// The `truncated_key` argument should be the overall key bytes shortened
    /// to the current depth.
    ///
    /// If the length of the header prefix is greater than the number of bytes
    /// stored (there are implicit bytes), then this falls back to using
    /// [`optimistic_match_prefix`][InnerNodeCommon::optimistic_match_prefix].
    ///
    /// If this function fell into that condition, then the `any_implicit_bytes`
    /// flag will be set to `true` in the `Ok` case and `prefix_byte` will be
    /// set to `None` in the `Err` case.
    ///
    /// If either of those conditions are true, and the caller of this function
    /// reaches a leaf node using these results, then the caller must perform a
    /// final check against the leaf key bytes to make sure that the search
    /// key matches the found key.
    ///
    /// # Errors
    /// This function returns an error if there is a mismatch between the given
    /// truncated key and the stored (implicit or full) prefix.
    #[inline]
    fn attempt_pessimistic_match_prefix(
        &self,
        truncated_key: &[u8],
    ) -> Result<AttemptOptimisticPrefixMatch, PessimisticMismatch> {
        if PREFIX_LEN < self.header().prefix_len() {
            let PrefixMatch { matched_bytes } = self.optimistic_match_prefix(truncated_key)?;

            Ok(AttemptOptimisticPrefixMatch {
                matched_bytes,
                any_implicit_bytes: true,
            })
        } else {
            // All bytes are explicit, this can proceed as normal

            let prefix = self.header().read_prefix();

            let matched_bytes = prefix
                .iter()
                .zip(truncated_key)
                .take_while(|(a, b)| **a == **b)
                .count();
            if matched_bytes < self.header().prefix_len() {
                Err(PessimisticMismatch {
                    matched_bytes,
                    prefix_byte: Some(prefix[matched_bytes]),
                })
            } else {
                Ok(AttemptOptimisticPrefixMatch {
                    matched_bytes,
                    any_implicit_bytes: false,
                })
            }
        }
    }

    /// Compares the compressed path of a node with the key and returns the
    /// number of equal bytes.
    ///
    /// This function will read the full prefix for this inner node, even if it
    /// needs to search a descendant leaf node to find implicit bytes.
    ///
    /// # Safety
    /// `current_depth` must be less than or equal to `key.len()`
    ///
    /// # Errors
    /// This function returns an error if there is a mismatch between the
    /// provided key and the full prefix.
    #[inline]
    unsafe fn match_full_prefix(
        &self,
        key: &[u8],
        current_depth: usize,
    ) -> Result<PrefixMatch, ExplicitMismatch<K, V, PREFIX_LEN>>
    where
        K: AsBytes,
    {
        unsafe {
            // SAFETY: Since we are iterating the key and prefixes, we
            // expect that the depth never exceeds the key len.
            // Because if this happens we ran out of bytes in the key to match
            // and the whole process should be already finished
            core::hint::assert_unchecked(current_depth <= key.len());
        }

        let (prefix, leaf_ptr) = self.read_full_prefix(current_depth);

        let matched_bytes = prefix
            .iter()
            .zip(&key[current_depth..])
            .take_while(|(a, b)| **a == **b)
            .count();
        if matched_bytes < prefix.len() {
            let upper_bound = (current_depth + prefix.len()).min(key.len());
            let key_segment = &key[current_depth..upper_bound];
            let node_prefix_comparison_to_search_key_segment = prefix.cmp(key_segment);

            debug_assert_ne!(
                node_prefix_comparison_to_search_key_segment,
                Ordering::Equal,
                "if there was a mismatch, the prefix must not be equal"
            );

            Err(ExplicitMismatch {
                matched_bytes,
                prefix_byte: prefix[matched_bytes],
                leaf_ptr,
                node_prefix_comparison_to_search_key_segment,
            })
        } else {
            Ok(PrefixMatch { matched_bytes })
        }
    }

    /// Read the prefix as a whole, by reconstructing it if necessary from a
    /// leaf
    #[inline]
    fn read_full_prefix<'b>(&'b self, current_depth: usize) -> NodePrefix<'b, K, V, PREFIX_LEN>
    where
        K: AsBytes + 'b,
        V: 'b,
    {
        let header = &self.header();
        let len = header.prefix_len();
        if likely!(len <= PREFIX_LEN) {
            (header.read_prefix(), None)
        } else {
            // SAFETY: Given we have a shared reference to this leaf node, there must be no
            // concurrent mutation on this node or any child node of this node.
            let leaf_ptr = unsafe { any_subtree_leaf(self) };

            // SAFETY: Since have a shared reference is safe to create a shared reference
            // from it
            let leaf = unsafe { leaf_ptr.as_ref() };
            let leaf = leaf.key_ref().as_bytes();

            assert!(
                current_depth <= leaf.len(),
                "current_depth [{current_depth}] must not exceed leaf key length [{}]; leaf must \
                 be a descendant of this node",
                leaf.len()
            );
            assert!(
                current_depth + len <= leaf.len(),
                "current_depth [{current_depth}] + prefix_len [{len}] must not exceed leaf key \
                 length [{}]; leaf must be a descendant of this node",
                leaf.len()
            );
            let leaf = &leaf[current_depth..(current_depth + len)];
            (leaf, Some(leaf_ptr))
        }
    }

    /// Returns the minimum child pointer from this node and it's key
    ///
    /// Since this is a [`InnerNode`] we assume that the we have at least one
    /// child, (more strictly we have 2, because with one child the node would
    /// have collapsed) so in this way we can avoid the [`Option`]. This is safe
    /// because if we had no children this current node should have been
    /// deleted.
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>);

    /// Returns the maximum child pointer from this node and it's key
    ///
    /// Since this is a [`InnerNode`] we assume that the we have at least one
    /// child, (more strictly we have 2, because with one child the node would
    /// have collapsed) so in this way we can avoid the [`Option`]. This is safe
    /// because if we had, no children this current node should have been
    /// deleted.
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>);

    /// Returns any child pointer from this node, preferring children that are
    /// pointers to leaf nodes.
    ///
    /// This function is useful in context where we need to quickly find a leaf
    /// of a subtree, but don't care how we get there.
    fn any_child_prefer_leaf(&self) -> OpaqueNodePtr<K, V, PREFIX_LEN> {
        // The minimum child is a valid choice
        self.min().1
    }
}

/// Common methods implemented by all inner nodes that will be used in the tree.
///
/// To contrast with [`InnerNodeCommon`], this trait:
///   - Incorporates a set value of [`NodeType`], accessible via [`Node::TYPE`].
///   - Specifies where the inner node sits in the "growth order", via
///     [`InnerNode::GrownNode`] and [`InnerNode::ShrunkNode`].
pub trait InnerNode<const PREFIX_LEN: usize>:
    Node<PREFIX_LEN> + Sized + fmt::Debug + InnerNodeCommon<Self::Key, Self::Value, PREFIX_LEN>
{
    /// The type of the next larger node type.
    type GrownNode: InnerNode<PREFIX_LEN, Key = Self::Key, Value = Self::Value>;

    /// The type of the next smaller node type.
    type ShrunkNode: InnerNode<PREFIX_LEN, Key = Self::Key, Value = Self::Value>;

    /// Grow this node into the next larger class, copying over children and
    /// prefix information.
    fn grow(&self) -> Self::GrownNode;

    /// Shrink this node into the next smaller class, copying over children and
    /// prefix information.
    ///
    /// # Panics
    ///  - Panics if the new, smaller node size does not have enough capacity to
    ///    hold all the children.
    fn shrink(&self) -> Self::ShrunkNode;

    /// Returns true if this node has no more space to store children.
    fn is_full(&self) -> bool {
        self.header().num_children() >= *Self::TYPE.capacity_range().end()
    }
}

/// Marker type for [`InnerNodeBuilder`]: no children have been added yet.
pub struct NoChild;

/// Marker type for [`InnerNodeBuilder`]: at least one child has been added.
pub struct HasChild;

/// Typestate builder for inner nodes that enforces the non-empty invariant.
///
/// The only way to call [`build`][InnerNodeBuilder::build] is to first add at
/// least one child via
/// [`write_child`][InnerNodeBuilder::write_child]. This is checked at
/// compile time via the `S` typestate parameter.
///
/// Obtain a builder via [`InnerNodeCommon::builder`].
#[expect(clippy::type_complexity)]
pub struct InnerNodeBuilder<K, V, const PREFIX_LEN: usize, N, S = NoChild> {
    node: N,
    _state: PhantomData<fn() -> (K, V, S)>,
}

impl<K, V, const PREFIX_LEN: usize, N> InnerNodeBuilder<K, V, PREFIX_LEN, N, NoChild>
where
    N: InnerNodeCommon<K, V, PREFIX_LEN>,
{
    /// Add the first child, transitioning the builder to the [`HasChild`] state
    /// and enabling [`build`][InnerNodeBuilder::build].
    pub fn write_child(
        mut self,
        key_byte: u8,
        child: OpaqueNodePtr<K, V, PREFIX_LEN>,
    ) -> InnerNodeBuilder<K, V, PREFIX_LEN, N, HasChild> {
        self.node.write_child(key_byte, child);
        InnerNodeBuilder {
            node: self.node,
            _state: PhantomData,
        }
    }
}

impl<K, V, const PREFIX_LEN: usize>
    InnerNodeBuilder<K, V, PREFIX_LEN, InnerNode4<K, V, PREFIX_LEN>, NoChild>
{
    /// Add the first child to the node without bounds check or order.
    ///
    /// This function transitions the build to the [`HasChild`] state and
    /// enabling [`build`][InnerNodeBuilder::build].
    ///
    /// # Safety
    /// - This functions assumes that the write is gonna be inbound (i.e the
    ///   check for a full node is done previously to the call of this function)
    pub unsafe fn write_child_unchecked(
        mut self,
        key_byte: u8,
        child: OpaqueNodePtr<K, V, PREFIX_LEN>,
    ) -> InnerNodeBuilder<K, V, PREFIX_LEN, InnerNode4<K, V, PREFIX_LEN>, HasChild> {
        // SAFETY: Covered by function safety requirements
        unsafe { self.node.write_child_unchecked(key_byte, child) };
        InnerNodeBuilder {
            node: self.node,
            _state: PhantomData,
        }
    }
}

impl<K, V, const PREFIX_LEN: usize, N> InnerNodeBuilder<K, V, PREFIX_LEN, N, HasChild>
where
    N: InnerNodeCommon<K, V, PREFIX_LEN>,
{
    /// Add another child to the node being built.
    pub fn write_child(mut self, key_byte: u8, child: OpaqueNodePtr<K, V, PREFIX_LEN>) -> Self {
        self.node.write_child(key_byte, child);
        self
    }

    /// Consume the builder and return the finished inner node.
    ///
    /// Only callable after at least one child has been added.
    pub fn build(self) -> N {
        self.node
    }
}

impl<K, V, const PREFIX_LEN: usize>
    InnerNodeBuilder<K, V, PREFIX_LEN, InnerNode4<K, V, PREFIX_LEN>, HasChild>
{
    /// Add a child to the node without bounds check or order.
    ///
    /// # Safety
    /// - This functions assumes that the write is gonna be inbound (i.e the
    ///   check for a full node is done previously to the call of this function)
    pub unsafe fn write_child_unchecked(
        mut self,
        key_byte: u8,
        child: OpaqueNodePtr<K, V, PREFIX_LEN>,
    ) -> Self {
        // SAFETY: Covered by function safety requirements
        unsafe { self.node.write_child_unchecked(key_byte, child) };
        self
    }
}

/// This type represents the contents of an [`InnerNode`] prefix, either read
/// directly from the prefix or fetched from a leaf node descendant.
///
/// The second value is the tuple will be `Some(_)` if the value was fetched
/// from a leaf node.
pub type NodePrefix<'a, K, V, const PREFIX_LEN: usize> = (
    &'a [u8],
    Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>>,
);

/// This enum represents different kinds of tree paths pointing to a leaf node.
///
/// Each variant contains information that is useful when inserting or deleting
/// a leaf at the implied location.
pub enum TreePath<K, V, const PREFIX_LEN: usize> {
    /// This variant indicates a tree with only a single leaf node as root.
    ///
    /// It has no grandparent or parent node.
    Root,
    /// This variant indicates a tree with a non-leaf root, and the leaf node
    /// we're pointed to is a direct child of the root.
    ///
    /// The leaf has no grandparent node.
    ChildOfRoot {
        /// A pointer to the root node of the tree.
        parent: OpaqueNodePtr<K, V, PREFIX_LEN>,
        /// The key byte which selects the leaf node when used as lookup in
        /// the root parent.
        child_key_byte: u8,
    },
    /// This variant covers all other tree cases, where the leaf node has both a
    /// parent and a grandparent node.
    Normal {
        /// A pointer to the grandparent node.
        grandparent: OpaqueNodePtr<K, V, PREFIX_LEN>,
        /// The key byte which selects the parent node when used as lookup in
        /// the grandparent.
        parent_key_byte: u8,
        /// A pointer to the parent node.
        parent: OpaqueNodePtr<K, V, PREFIX_LEN>,
        /// The key byte which selects the leaf node when used as lookup in
        /// the parent.
        child_key_byte: u8,
    },
}

impl<K, V, const PREFIX_LEN: usize> Copy for TreePath<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> Clone for TreePath<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for TreePath<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Root => write!(f, "Root"),
            Self::ChildOfRoot {
                parent,
                child_key_byte,
            } => f
                .debug_struct("ChildOfRoot")
                .field("parent", parent)
                .field("child_key_byte", child_key_byte)
                .finish(),
            Self::Normal {
                grandparent,
                parent_key_byte,
                parent,
                child_key_byte,
            } => f
                .debug_struct("Normal")
                .field("grandparent", grandparent)
                .field("parent_key_byte", parent_key_byte)
                .field("parent", parent)
                .field("child_key_byte", child_key_byte)
                .finish(),
        }
    }
}

/// This type is used to track the parent and grandparent when searching down
/// the tree.
#[derive(Debug)]
pub struct TreePathSearch<K, V, const PREFIX_LEN: usize> {
    current_grandparent: Option<(OpaqueNodePtr<K, V, PREFIX_LEN>, u8)>,
    current_parent: Option<(OpaqueNodePtr<K, V, PREFIX_LEN>, u8)>,
}

impl<K, V, const PREFIX_LEN: usize> Default for TreePathSearch<K, V, PREFIX_LEN> {
    fn default() -> Self {
        Self {
            current_grandparent: None,
            current_parent: None,
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> TreePathSearch<K, V, PREFIX_LEN> {
    /// Register that the search procedure passed an inner node, and update the
    /// current parent and grandparent.
    pub fn visit_inner_node(&mut self, inner_node: OpaqueNodePtr<K, V, PREFIX_LEN>, key_byte: u8) {
        self.current_grandparent = self.current_parent;
        self.current_parent = Some((inner_node, key_byte));
    }

    /// Complete the tree search and return a [`TreePath`] which has the parent
    /// + grandparent information.
    pub fn finish(self) -> TreePath<K, V, PREFIX_LEN> {
        match (self.current_grandparent, self.current_parent) {
            (None, None) => TreePath::Root,
            (None, Some((parent, child_key_byte))) => TreePath::ChildOfRoot {
                parent,
                child_key_byte,
            },
            (Some((grandparent, parent_key_byte)), Some((parent, child_key_byte))) => {
                TreePath::Normal {
                    grandparent,
                    parent_key_byte,
                    parent,
                    child_key_byte,
                }
            },
            (Some(_), None) => {
                unreachable!("Impossible for grandparent to present while parent is not")
            },
        }
    }
}

/// Check that the given range bounds are valid, if not then panic.
///
/// Validity means:
///  1. Range bounds are not completely empty
///  2. Start bound is not greater than end bound
fn assert_valid_range_bounds(bound: &impl RangeBounds<u8>) {
    {
        match (bound.start_bound(), bound.end_bound()) {
            (Bound::Excluded(s), Bound::Excluded(e)) if s == e => {
                panic!("range start and end are equal and excluded: ({s:?})")
            },
            (Bound::Included(s) | Bound::Excluded(s), Bound::Included(e) | Bound::Excluded(e))
                if s > e =>
            {
                panic!("range start ({s:?}) is greater than range end ({e:?})")
            },
            _ => {},
        }
    }
}

/// Find any leaf in the subtree rooted by `root`.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
#[inline]
unsafe fn any_subtree_leaf<N, K, V, const PREFIX_LEN: usize>(
    root: &N,
) -> NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>
where
    N: InnerNodeCommon<K, V, PREFIX_LEN>,
{
    let mut current_node = root.any_child_prefer_leaf();

    loop {
        current_node = match_concrete_node_ptr!(match (current_node.to_node_ptr()) {
            // SAFETY: No other concurrent mutation will happen, the reference returned from
            // `as_ref` is also bounded to this loop, not returned outside.
            InnerNode(inner_node) => unsafe { inner_node.as_ref().any_child_prefer_leaf() },
            LeafNode(leaf_node) => {
                return leaf_node;
            },
        });
    }
}

#[cfg(test)]
mod tests {
    use alloc::{boxed::Box, vec::Vec};
    use core::mem;

    use super::*;
    use crate::rust_nightly_apis::ptr::const_addr;

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn node_sizes() {
        const DEFAULT_PREFIX_LEN: usize = 16;
        assert_eq!(mem::size_of::<Header<DEFAULT_PREFIX_LEN>>(), 24);

        const EXPECTED_HEADER_SIZE: usize = DEFAULT_PREFIX_LEN.next_multiple_of(4) + 8;
        assert_eq!(EXPECTED_HEADER_SIZE, 24);

        // key map: 4 * (1 byte) = 4 bytes
        // child map: 4 * (8 bytes (on 64-bit platform)) = 32
        //
        // 4 bytes of padding are inserted after the `keys` field to align the field to
        // an 8 byte boundary.
        assert_eq!(
            mem::size_of::<InnerNode4<Box<[u8]>, usize, DEFAULT_PREFIX_LEN>>(),
            EXPECTED_HEADER_SIZE + 40
        );
        // key map: 16 * (1 byte) = 16 bytes
        // child map: 16 * (8 bytes (on 64-bit platform)) = 128
        assert_eq!(
            mem::size_of::<InnerNode16<Box<[u8]>, usize, DEFAULT_PREFIX_LEN>>(),
            EXPECTED_HEADER_SIZE + 144
        );
        // key map: 256 * (1 byte) = 256 bytes
        // child map: 48 * (8 bytes (on 64-bit platform)) = 384
        assert_eq!(
            mem::size_of::<InnerNode48<Box<[u8]>, usize, DEFAULT_PREFIX_LEN>>(),
            EXPECTED_HEADER_SIZE + 640
        );
        // child & key map: 256 * (8 bytes (on 64-bit platform)) = 2048
        assert_eq!(
            mem::size_of::<InnerNodeDirect<Box<[u8]>, usize, DEFAULT_PREFIX_LEN>>(),
            EXPECTED_HEADER_SIZE + 2048
        );

        // Assert that pointer is expected size and has non-null optimization
        assert_eq!(
            mem::size_of::<Option<OpaqueNodePtr<Box<[u8]>, (), DEFAULT_PREFIX_LEN>>>(),
            8
        );
        assert_eq!(
            mem::size_of::<OpaqueNodePtr<Box<[u8]>, (), DEFAULT_PREFIX_LEN>>(),
            8
        );
    }

    #[test]
    fn node_alignment() {
        assert_eq!(mem::align_of::<InnerNode4<Box<[u8]>, u8, 16>>(), 8);
        assert_eq!(mem::align_of::<InnerNode16<Box<[u8]>, u8, 16>>(), 8);
        assert_eq!(mem::align_of::<InnerNode48<Box<[u8]>, u8, 16>>(), 8);
        assert_eq!(mem::align_of::<InnerNodeDirect<Box<[u8]>, u8, 16>>(), 8);
        assert_eq!(mem::align_of::<LeafNode<Box<[u8]>, u8, 16>>(), 8);
        assert_eq!(mem::align_of::<Header<16>>(), 4);

        assert_eq!(
            mem::align_of::<InnerNode4<Box<[u8]>, u8, 16>>(),
            mem::align_of::<OpaqueValue>()
        );
        assert_eq!(
            mem::align_of::<InnerNode16<Box<[u8]>, u8, 16>>(),
            mem::align_of::<OpaqueValue>()
        );
        assert_eq!(
            mem::align_of::<InnerNode48<Box<[u8]>, u8, 16>>(),
            mem::align_of::<OpaqueValue>()
        );
        assert_eq!(
            mem::align_of::<InnerNodeDirect<Box<[u8]>, u8, 16>>(),
            mem::align_of::<OpaqueValue>()
        );
        assert_eq!(
            mem::align_of::<LeafNode<Box<[u8]>, u8, 16>>(),
            mem::align_of::<OpaqueValue>()
        );

        let mut leaf = LeafNode::<Box<[u8]>, (), 16>::with_no_siblings(vec![].into(), ());
        let leaf_ptr = NodePtr::from(&mut leaf).to_opaque();

        let n4 = InnerNode4::<Box<[u8]>, (), 16>::builder(&[], 0)
            .write_child(0, leaf_ptr)
            .build();
        let n16 = InnerNode4::<Box<[u8]>, (), 16>::builder(&[], 0)
            .write_child(0, leaf_ptr)
            .build();
        let n48 = InnerNode4::<Box<[u8]>, (), 16>::builder(&[], 0)
            .write_child(0, leaf_ptr)
            .build();
        let n256 = InnerNode4::<Box<[u8]>, (), 16>::builder(&[], 0)
            .write_child(0, leaf_ptr)
            .build();

        let n4_ptr = const_addr(&n4 as *const InnerNode4<Box<[u8]>, (), 16>);
        let n16_ptr = const_addr(&n16 as *const InnerNode4<Box<[u8]>, (), 16>);
        let n48_ptr = const_addr(&n48 as *const InnerNode4<Box<[u8]>, (), 16>);
        let n256_ptr = const_addr(&n256 as *const InnerNode4<Box<[u8]>, (), 16>);

        // Ensure that there are 3 bits of unused space in the node pointer because of
        // the alignment.
        assert!(n4_ptr.trailing_zeros() >= 3);
        assert!(n16_ptr.trailing_zeros() >= 3);
        assert!(n48_ptr.trailing_zeros() >= 3);
        assert!(n256_ptr.trailing_zeros() >= 3);
    }

    pub(crate) fn inner_node_write_child_test<const PREFIX_LEN: usize, N>(num_children: usize)
    where
        N: InnerNode<PREFIX_LEN, Key = Box<[u8]>, Value = ()>,
    {
        let mut leaves: Vec<LeafNode<Box<[u8]>, (), PREFIX_LEN>> = (0..num_children)
            .map(|_| LeafNode::with_no_siblings(vec![].into(), ()))
            .collect();

        let leaf_pointers: Vec<OpaqueNodePtr<Box<[u8]>, (), PREFIX_LEN>> = leaves
            .iter_mut()
            .map(|leaf| NodePtr::from(leaf).to_opaque())
            .collect();

        let mut node = N::builder(&[], 0).write_child(0, leaf_pointers[0]).build();

        assert!(!node.is_full());

        for (idx, leaf_pointer) in leaf_pointers[1..].iter().copied().enumerate() {
            node.write_child(u8::try_from(idx + 1).unwrap(), leaf_pointer);
        }

        for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
            assert_eq!(
                node.lookup_child(u8::try_from(idx).unwrap()),
                Some(leaf_pointer)
            );
        }

        assert!(node.is_full());
    }

    pub fn inner_node_remove_child_test<const PREFIX_LEN: usize, N>(num_children: usize)
    where
        N: InnerNode<PREFIX_LEN, Key = Box<[u8]>, Value = ()>,
    {
        let mut leaves: Vec<LeafNode<Box<[u8]>, (), PREFIX_LEN>> = (0..num_children)
            .map(|_| LeafNode::with_no_siblings(vec![].into(), ()))
            .collect();

        let leaf_pointers: Vec<OpaqueNodePtr<Box<[u8]>, (), PREFIX_LEN>> = leaves
            .iter_mut()
            .map(|leaf| NodePtr::from(leaf).to_opaque())
            .collect();

        let mut node = N::builder(&[], 0).write_child(0, leaf_pointers[0]).build();

        assert!(!node.is_full());

        for (idx, leaf_pointer) in leaf_pointers[1..].iter().copied().enumerate() {
            node.write_child(u8::try_from(idx + 1).unwrap(), leaf_pointer);
        }

        for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
            assert_eq!(
                node.lookup_child(u8::try_from(idx).unwrap()),
                Some(leaf_pointer)
            );
        }

        for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
            assert_eq!(
                node.remove_child(u8::try_from(idx).unwrap()),
                Some(leaf_pointer)
            );

            assert_eq!(node.lookup_child(u8::try_from(idx).unwrap()), None);
        }

        assert!(!node.is_full());
    }

    pub(crate) fn inner_node_shrink_test<const PREFIX_LEN: usize, N>(num_children: usize)
    where
        N: InnerNode<PREFIX_LEN, Key = Box<[u8]>, Value = ()>,
    {
        let mut leaves: Vec<LeafNode<Box<[u8]>, (), PREFIX_LEN>> = (0..num_children)
            .map(|_| LeafNode::with_no_siblings(vec![].into(), ()))
            .collect();

        let leaf_pointers: Vec<OpaqueNodePtr<Box<[u8]>, (), PREFIX_LEN>> = leaves
            .iter_mut()
            .map(|leaf| NodePtr::from(leaf).to_opaque())
            .collect();

        let mut node = N::builder(&[], 0).write_child(0, leaf_pointers[0]).build();

        for (idx, leaf_pointer) in leaf_pointers[1..].iter().copied().enumerate() {
            node.write_child(u8::try_from(idx + 1).unwrap(), leaf_pointer);
        }

        let shrunk_node = node.shrink();

        for (idx, leaf_pointer) in leaf_pointers.into_iter().enumerate() {
            assert_eq!(
                shrunk_node.lookup_child(u8::try_from(idx).unwrap()),
                Some(leaf_pointer)
            );
        }
    }

    pub(crate) fn inner_node_min_max_test<const PREFIX_LEN: usize, N>(num_children: usize)
    where
        N: InnerNode<PREFIX_LEN, Key = Box<[u8]>, Value = ()>,
    {
        assert!(
            num_children >= 2,
            "test harness must specify more than 1 child"
        );

        let mut leaves: Vec<LeafNode<Box<[u8]>, (), PREFIX_LEN>> = (0..num_children)
            .map(|_| LeafNode::with_no_siblings(vec![].into(), ()))
            .collect();

        let leaf_pointers: Vec<OpaqueNodePtr<Box<[u8]>, (), PREFIX_LEN>> = leaves
            .iter_mut()
            .map(|leaf| NodePtr::from(leaf).to_opaque())
            .collect();

        let mut node = N::builder(&[], 0).write_child(0, leaf_pointers[0]).build();

        for (idx, leaf_pointer) in leaf_pointers[1..].iter().copied().enumerate() {
            node.write_child(u8::try_from(idx + 1).unwrap(), leaf_pointer);
        }

        assert_eq!(node.header().num_children(), num_children);

        // generate list of interleaved `[(0, num_children - 1), (1, num_children -
        // 2), (2, num_children - 3), ..., (midpoint, num_children - midpoint + 1)]`
        let midpoint = num_children / 2;
        let interleaved = (0..midpoint).zip((midpoint..num_children).rev());

        for (min_idx, max_idx) in interleaved {
            let (min_key_fragment, min_leaf_node) = node.min();
            assert_eq!(min_leaf_node, node.remove_child(min_key_fragment).unwrap());
            let expected_min_leaf_node =
                NodePtr::from(leaves.get_mut(min_idx).unwrap()).to_opaque();
            assert_eq!(expected_min_leaf_node, min_leaf_node);

            let (max_key_fragment, max_leaf_node) = node.max();
            assert_eq!(max_leaf_node, node.remove_child(max_key_fragment).unwrap());
            let expected_max_leaf_node =
                NodePtr::from(leaves.get_mut(max_idx).unwrap()).to_opaque();
            assert_eq!(expected_max_leaf_node, max_leaf_node);
        }

        assert_eq!(node.header().num_children(), 0);
    }

    // --------------------------------------- ITERATORS
    // ---------------------------------------

    pub(crate) type FixtureReturn<Node, const N: usize> = (
        Node,
        [LeafNode<Box<[u8]>, (), 16>; N],
        [OpaqueNodePtr<Box<[u8]>, (), 16>; N],
    );
}
