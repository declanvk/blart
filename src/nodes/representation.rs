//! Trie node representation

use crate::{
    rust_nightly_apis::{
        assume, maybe_uninit_slice_assume_init_mut, maybe_uninit_slice_assume_init_ref,
        maybe_uninit_uninit_array,
    },
    tagged_pointer::TaggedPointer,
    AsBytes,
};
use std::{
    borrow::Borrow,
    cmp::Ordering,
    error::Error,
    fmt,
    hash::Hash,
    iter::{Copied, Enumerate, FusedIterator, Zip},
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
    ops::Range,
    ptr::{self, NonNull},
    slice::Iter,
};

#[cfg(feature = "nightly")]
use std::{
    iter::{FilterMap, Map},
    simd::{
        cmp::{SimdPartialEq, SimdPartialOrd},
        u8x16, u8x64, usizex64,
    },
};

use super::NodeHeader;

// mod iterators;

#[cfg(test)]
mod tests;

/// The representation of inner nodes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum NodeType {
    /// Node that references between 2 and 4 children
    Node4 = 0b000,
    /// Node that references between 5 and 16 children
    Node16 = 0b001, // 0b001
    /// Node that references between 17 and 49 children
    Node48 = 0b010, // 0b010
    /// Node that references between 49 and 256 children
    Node256 = 0b011, // 0b011
    /// Node that contains a single value
    Leaf = 0b100, // 0b100
}

impl NodeType {
    /// The upper bound on the number of child nodes that this
    /// NodeType can have.
    pub const fn upper_capacity(self) -> usize {
        match self {
            NodeType::Node4 => 4,
            NodeType::Node16 => 16,
            NodeType::Node48 => 48,
            NodeType::Node256 => 256,
            NodeType::Leaf => 0,
        }
    }

    /// Converts a u8 value to a [`NodeType`]
    ///
    /// # Safety
    ///  - `src` must be a valid variant from the enum
    pub const unsafe fn from_u8(src: u8) -> NodeType {
        // SAFETY: `NodeType` is repr(u8)
        unsafe { std::mem::transmute::<u8, NodeType>(src) }
    }

    /// Return true if an [`InnerNode`] with the given [`NodeType`] and
    /// specified number of children should be shrunk.
    ///
    /// # Panics
    ///  - Panics if `node_type` equals [`NodeType::Leaf`]
    pub fn should_shrink_inner_node(self, num_children: usize) -> bool {
        match self {
            NodeType::Node4 => false,
            NodeType::Node16 => num_children <= 4,
            NodeType::Node48 => num_children <= 16,
            NodeType::Node256 => num_children <= 48,
            NodeType::Leaf => panic!("cannot shrink leaf"),
        }
    }

    /// Return the range of number of children that each node type accepts.
    pub const fn capacity_range(self) -> Range<usize> {
        match self {
            NodeType::Node4 => Range { start: 1, end: 5 },
            NodeType::Node16 => Range { start: 5, end: 17 },
            NodeType::Node48 => Range { start: 17, end: 49 },
            NodeType::Node256 => Range {
                start: 49,
                end: 256,
            },
            NodeType::Leaf => Range { start: 0, end: 0 },
        }
    }
}

/// A placeholder type that has the required amount of alignment.
///
/// An alignment of 8 gives us 3 unused bits in any pointer to this type.
#[derive(Debug)]
#[repr(align(8))]
struct OpaqueValue;

/// An opaque pointer to a [`Node`].
///
/// Could be any one of the NodeTypes, need to perform check on the runtime type
/// and then cast to a [`NodePtr`].
#[repr(transparent)]
pub struct OpaqueNodePtr<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
>(TaggedPointer<OpaqueValue, 3>, PhantomData<(K, V, H)>);

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Copy
    for OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>
{
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Clone
    for OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> fmt::Debug
    for OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("OpaqueNodePtr").field(&self.0).finish()
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> fmt::Pointer
    for OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Eq
    for OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>
{
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> PartialEq
    for OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H1: NodeHeader<NUM_PREFIX_BYTES>> Hash
    for OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H1>
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>
{
    /// Construct a new opaque node pointer from an existing non-null node
    /// pointer.
    pub fn new<N>(pointer: NonNull<N>) -> Self
    where
        N: Node<NUM_PREFIX_BYTES, Value = V>,
    {
        let mut tagged_ptr = TaggedPointer::from(pointer).cast::<OpaqueValue>();
        tagged_ptr.set_data(N::TYPE as usize);

        OpaqueNodePtr(tagged_ptr, PhantomData)
    }

    /// Return `true` if this Node_ pointer points to the specified concrete
    /// [`NodeType`].
    pub fn is<N: Node<NUM_PREFIX_BYTES>>(&self) -> bool {
        self.0.to_data() == usize::from(N::TYPE as u8)
    }

    /// Create a non-opaque node pointer that will eliminate future type
    /// assertions, if the type of the pointed node matches the given
    /// node type.
    pub fn cast<N: Node<NUM_PREFIX_BYTES>>(self) -> Option<NodePtr<NUM_PREFIX_BYTES, N>> {
        if self.is::<N>() {
            Some(NodePtr(self.0.cast::<N>().into()))
        } else {
            None
        }
    }

    /// Cast this opaque pointer type an enum that contains a pointer to the
    /// concrete node type.
    pub fn to_node_ptr(self) -> ConcreteNodePtr<K, V, NUM_PREFIX_BYTES, H> {
        match self.node_type() {
            NodeType::Node4 => ConcreteNodePtr::Node4(NodePtr(
                self.0
                    .cast::<InnerNode4<K, V, NUM_PREFIX_BYTES, H>>()
                    .into(),
            )),
            NodeType::Node16 => ConcreteNodePtr::Node16(NodePtr(
                self.0
                    .cast::<InnerNode16<K, V, NUM_PREFIX_BYTES, H>>()
                    .into(),
            )),
            NodeType::Node48 => ConcreteNodePtr::Node48(NodePtr(
                self.0
                    .cast::<InnerNode48<K, V, NUM_PREFIX_BYTES, H>>()
                    .into(),
            )),
            NodeType::Node256 => ConcreteNodePtr::Node256(NodePtr(
                self.0
                    .cast::<InnerNode256<K, V, NUM_PREFIX_BYTES, H>>()
                    .into(),
            )),
            NodeType::Leaf => ConcreteNodePtr::LeafNode(NodePtr(
                self.0.cast::<LeafNode<K, V, NUM_PREFIX_BYTES, H>>().into(),
            )),
        }
    }

    /// Retrieve the runtime node type information.
    pub fn node_type(self) -> NodeType {
        // SAFETY: We know that we can convert the usize into a `NodeType` because
        // we have only stored `NodeType` values into this pointer
        unsafe { NodeType::from_u8(self.0.to_data() as u8) }
    }

    /// Get a mutable reference to the header if the underlying node has a
    /// header field, otherwise return `None`.
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'h is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get accessed
    ///    (read or written) through any other pointer.
    pub(crate) unsafe fn header_mut<'h>(self) -> Option<&'h mut H> {
        let header_ptr = match self.node_type() {
            NodeType::Node4 | NodeType::Node16 | NodeType::Node48 | NodeType::Node256 => unsafe {
                self.header_mut_uncheked()
            },
            NodeType::Leaf => {
                return None;
            },
        };

        // SAFETY: The pointer is properly aligned and points to a initialized instance
        // of Header that is dereferenceable. The lifetime safety requirements are
        // passed up to the caller of this function.
        Some(header_ptr)
    }

    /// Get a mutable reference to the header, this doesn't check if the pointer
    /// is to an inner node.
    ///
    /// # Safety
    ///  - The pointer must be to an inner node
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'h is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get accessed
    ///    (read or written) through any other pointer.
    pub(crate) unsafe fn header_mut_uncheked<'h>(self) -> &'h mut H {
        unsafe { &mut *self.0.cast::<H>().to_ptr() }
    }

    /// Do a deep clone recursively, by allocating new nodes
    pub fn deep_clone(&self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        // SAFETY: We hold a shared reference, so it's safe to make
        // a shared reference from it
        match self.to_node_ptr() {
            ConcreteNodePtr::Node4(inner) => unsafe { inner.as_ref().deep_clone().to_opaque() },
            ConcreteNodePtr::Node16(inner) => unsafe { inner.as_ref().deep_clone().to_opaque() },
            ConcreteNodePtr::Node48(inner) => unsafe { inner.as_ref().deep_clone().to_opaque() },
            ConcreteNodePtr::Node256(inner) => unsafe { inner.as_ref().deep_clone().to_opaque() },
            ConcreteNodePtr::LeafNode(inner) => unsafe {
                NodePtr::allocate_node_ptr(inner.as_ref().clone()).to_opaque()
            },
        }
    }
}

/// An enum that encapsulates pointers to every type of Node
pub enum ConcreteNodePtr<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
> {
    /// Node that references between 2 and 4 children
    Node4(NodePtr<NUM_PREFIX_BYTES, InnerNode4<K, V, NUM_PREFIX_BYTES, H>>),
    /// Node that references between 5 and 16 children
    Node16(NodePtr<NUM_PREFIX_BYTES, InnerNode16<K, V, NUM_PREFIX_BYTES, H>>),
    /// Node that references between 17 and 49 children
    Node48(NodePtr<NUM_PREFIX_BYTES, InnerNode48<K, V, NUM_PREFIX_BYTES, H>>),
    /// Node that references between 49 and 256 children
    Node256(NodePtr<NUM_PREFIX_BYTES, InnerNode256<K, V, NUM_PREFIX_BYTES, H>>),
    /// Node that contains a single value
    LeafNode(NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>),
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> fmt::Debug
    for ConcreteNodePtr<K, V, NUM_PREFIX_BYTES, H>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Node4(arg0) => f.debug_tuple("Node4").field(arg0).finish(),
            Self::Node16(arg0) => f.debug_tuple("Node16").field(arg0).finish(),
            Self::Node48(arg0) => f.debug_tuple("Node48").field(arg0).finish(),
            Self::Node256(arg0) => f.debug_tuple("Node256").field(arg0).finish(),
            Self::LeafNode(arg0) => f.debug_tuple("LeafNode").field(arg0).finish(),
        }
    }
}

/// A pointer to a [`Node`].
#[repr(transparent)]
pub struct NodePtr<const NUM_PREFIX_BYTES: usize, N: Node<NUM_PREFIX_BYTES>>(NonNull<N>);

impl<const NUM_PREFIX_BYTES: usize, N: Node<NUM_PREFIX_BYTES>> NodePtr<NUM_PREFIX_BYTES, N> {
    /// Create a safe pointer to a [`Node`].
    ///
    /// # Safety
    /// - Given pointer must be non-null, aligned, and valid for reads or writes
    ///   of a value of N type.
    pub unsafe fn new(ptr: *mut N) -> Self {
        // SAFETY: The safety requirements of this function match the
        // requirements of `NonNull::new_unchecked`.
        unsafe { NodePtr(NonNull::new_unchecked(ptr)) }
    }

    /// Allocate the given [`Node`] on the [`std::alloc::Global`] heap and
    /// return a [`NodePtr`] that wrap the raw pointer.
    pub fn allocate_node_ptr(node: N) -> Self {
        // SAFETY: The pointer from [`Box::into_raw`] is non-null, aligned, and valid
        // for reads and writes of the [`Node`] `N`.
        unsafe { NodePtr::new(Box::into_raw(Box::new(node))) }
    }

    /// Deallocate a [`Node`] object created with the
    /// [`NodePtr::allocate_node_ptr`] function.
    ///
    /// # Safety
    ///  - This function can only be called once for a given node object.
    #[must_use]
    pub unsafe fn deallocate_node_ptr(node: Self) -> N {
        // SAFETY: Covered by safety condition on functiom
        unsafe { *Box::from_raw(node.to_ptr()) }
    }

    /// Moves `new_value` into the referenced `dest`, returning the previous
    /// `dest` value.
    ///
    /// Neither value is dropped.
    ///
    /// # Safety
    ///  - The node the `dest` pointers points to must not get accessed (read or
    ///    written) through any other pointers concurrent to this modification.
    pub unsafe fn replace(dest: Self, new_value: N) -> N {
        // SAFETY: The lifetime of the `dest` reference is restricted to this function,
        // and the referenced node is not accessed by the safety doc on the containing
        // function.
        let dest = unsafe { dest.as_mut() };
        mem::replace(dest, new_value)
    }

    /// Cast node pointer back to an opaque version, losing type information
    pub fn to_opaque(self) -> OpaqueNodePtr<N::Key, N::Value, NUM_PREFIX_BYTES, N::Header> {
        OpaqueNodePtr::new(self.0)
    }

    /// Reads the Node from self without moving it. This leaves the memory in
    /// self unchanged.
    pub fn read(self) -> ManuallyDrop<N> {
        // SAFETY: The non-null requirements of ptr::read is already
        // guaranteed by the NonNull wrapper. The requirements of proper alignment,
        // initialization, validity for reads are required by the construction
        // of the NodePtr type.
        ManuallyDrop::new(unsafe { ptr::read(self.0.as_ptr()) })
    }

    /// Returns a shared reference to the value.
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get mutated
    ///    (except inside UnsafeCell).
    pub unsafe fn as_ref<'a>(self) -> &'a N {
        // SAFETY: The pointer is properly aligned and points to a initialized instance
        // of N that is dereferenceable. The lifetime safety requirements are passed up
        // to the invoked of this function.
        unsafe { self.0.as_ref() }
    }

    /// Returns a unique mutable reference to the node.
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the node. In particular, for the duration of this
    ///    lifetime, the node the pointer points to must not get accessed (read
    ///    or written) through any other pointer.
    pub unsafe fn as_mut<'a>(mut self) -> &'a mut N {
        // SAFETY: The pointer is properly aligned and points to a initialized instance
        // of N that is dereferenceable. The lifetime safety requirements are passed up
        // to the invoked of this function.
        unsafe { self.0.as_mut() }
    }

    /// Acquires the underlying *mut pointer.
    pub fn to_ptr(self) -> *mut N {
        self.0.as_ptr()
    }

    fn as_mut_safe(&mut self) -> &mut N {
        // SAFETY: The pointer is properly aligned and points to a initialized instance
        // of N that is dereferenceable. The lifetime safety requirements are passed up
        // to the invoked of this function.
        unsafe { self.0.as_mut() }
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>
{
    /// Returns a shared reference to the key and value of the pointed to
    /// [`LeafNode`].
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get mutated
    ///    (except inside UnsafeCell).
    pub unsafe fn as_key_value_ref<'a>(self) -> (&'a K, &'a V)
    where
        H: 'a,
    {
        // SAFETY: Safety requirements are covered by the containing function.
        let leaf = unsafe { self.as_ref() };

        (leaf.key_ref(), leaf.value_ref())
    }

    /// Returns a unique mutable reference to the key and value of the pointed
    /// to [`LeafNode`].
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the node. In particular, for the duration of this
    ///    lifetime, the node the pointer points to must not get accessed (read
    ///    or written) through any other pointer.
    pub unsafe fn as_key_ref_value_mut<'a>(self) -> (&'a K, &'a mut V)
    where
        H: 'a,
    {
        // SAFETY: Safety requirements are covered by the containing function.
        let leaf = unsafe { self.as_mut() };

        let (key, value) = leaf.entry_mut();
        (key, value)
    }

    /// Returns a unique mutable reference to the key and value of the pointed
    /// to [`LeafNode`].
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get mutated
    ///    (except inside UnsafeCell).
    pub unsafe fn as_key_ref<'a>(self) -> &'a K
    where
        V: 'a,
        H: 'a,
    {
        // SAFETY: Safety requirements are covered by the containing function.
        let leaf = unsafe { self.as_ref() };

        leaf.key_ref()
    }

    /// Returns a unique mutable reference to the key and value of the pointed
    /// to [`LeafNode`].
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get mutated
    ///    (except inside UnsafeCell).
    pub unsafe fn as_value_ref<'a>(self) -> &'a V
    where
        K: 'a,
        V: 'a,
        H: 'a,
    {
        // SAFETY: Safety requirements are covered by the containing function.
        let leaf = unsafe { self.as_ref() };

        leaf.value_ref()
    }

    /// Returns a unique mutable reference to the key and value of the pointed
    /// to [`LeafNode`].
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the node. In particular, for the duration of this
    ///    lifetime, the node the pointer points to must not get accessed (read
    ///    or written) through any other pointer.
    pub unsafe fn as_value_mut<'a>(self) -> &'a mut V
    where
        K: 'a,
        V: 'a,
        H: 'a,
    {
        // SAFETY: Safety requirements are covered by the containing function.
        let leaf = unsafe { self.as_mut() };

        leaf.value_mut()
    }
}

impl<const NUM_PREFIX_BYTES: usize, N: Node<NUM_PREFIX_BYTES>> Clone
    for NodePtr<NUM_PREFIX_BYTES, N>
{
    fn clone(&self) -> Self {
        *self
    }
}
impl<const NUM_PREFIX_BYTES: usize, N: Node<NUM_PREFIX_BYTES>> Copy
    for NodePtr<NUM_PREFIX_BYTES, N>
{
}

impl<const NUM_PREFIX_BYTES: usize, N: Node<NUM_PREFIX_BYTES>> From<&mut N>
    for NodePtr<NUM_PREFIX_BYTES, N>
{
    fn from(node_ref: &mut N) -> Self {
        // SAFETY: Pointer is non-null, aligned, and pointing to a valid instance of N
        // because it was constructed from a mutable reference.
        unsafe { NodePtr::new(node_ref as *mut _) }
    }
}

impl<const NUM_PREFIX_BYTES: usize, N: Node<NUM_PREFIX_BYTES>> PartialEq
    for NodePtr<NUM_PREFIX_BYTES, N>
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<const NUM_PREFIX_BYTES: usize, N: Node<NUM_PREFIX_BYTES>> Eq for NodePtr<NUM_PREFIX_BYTES, N> {}

impl<const NUM_PREFIX_BYTES: usize, N: Node<NUM_PREFIX_BYTES>> fmt::Debug
    for NodePtr<NUM_PREFIX_BYTES, N>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("NodePtr").field(&self.0).finish()
    }
}

impl<const NUM_PREFIX_BYTES: usize, N: Node<NUM_PREFIX_BYTES>> fmt::Pointer
    for NodePtr<NUM_PREFIX_BYTES, N>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

pub(crate) mod private {
    use crate::{nodes::NodeHeader, AsBytes};

    /// This trait is used to seal other traits, such that they cannot be
    /// implemented outside of the crate.
    pub trait Sealed {}

    impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Sealed
        for super::InnerNode4<K, V, NUM_PREFIX_BYTES, H>
    {
    }
    impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Sealed
        for super::InnerNode16<K, V, NUM_PREFIX_BYTES, H>
    {
    }
    impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Sealed
        for super::InnerNode48<K, V, NUM_PREFIX_BYTES, H>
    {
    }
    impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Sealed
        for super::InnerNode256<K, V, NUM_PREFIX_BYTES, H>
    {
    }
    impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Sealed
        for super::LeafNode<K, V, NUM_PREFIX_BYTES, H>
    {
    }
}

/// All nodes which contain a runtime tag that validates their type.
pub trait Node<const NUM_PREFIX_BYTES: usize>: private::Sealed {
    /// The runtime type of the node.
    const TYPE: NodeType;

    /// The key type carried by the leafe nodes
    type Key: AsBytes;

    /// The value type carried by the leaf nodes
    type Value;

    /// The header type
    type Header: NodeHeader<NUM_PREFIX_BYTES>;
}

/// Result of prefix match
#[derive(Debug)]
pub enum MatchPrefixResult<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
> {
    /// If prefixes don't match
    Mismatch {
        /// Mismatch object
        mismatch: Mismatch<K, V, NUM_PREFIX_BYTES, H>,
    },
    /// If the prefixes match entirely
    Match {
        /// How many bytes were matched
        matched_bytes: usize,
    },
}

/// Represents a prefix mismatch
#[derive(Debug)]
pub struct Mismatch<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> {
    /// How many bytes were matched
    pub matched_bytes: usize,
    /// Value of the byte that made it not match
    pub prefix_byte: u8,
    /// Pointer to the leaf if the prefix was reconstructed
    pub leaf_ptr: Option<NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>>,
}

/// Common methods implemented by all inner node.
pub trait InnerNode<const NUM_PREFIX_BYTES: usize>: Node<NUM_PREFIX_BYTES> + Sized {
    /// The type of the next larger node type.
    type GrownNode: InnerNode<
        NUM_PREFIX_BYTES,
        Key = Self::Key,
        Value = Self::Value,
        Header = Self::Header,
    >;

    /// The type of the next smaller node type.
    type ShrunkNode: InnerNode<
        NUM_PREFIX_BYTES,
        Key = Self::Key,
        Value = Self::Value,
        Header = Self::Header,
    >;

    /// The type of the iterator over all children of the inner node
    type Iter<'a>: Iterator<
            Item = (
                u8,
                OpaqueNodePtr<Self::Key, Self::Value, NUM_PREFIX_BYTES, Self::Header>,
            ),
        > + DoubleEndedIterator
        + FusedIterator
    where
        Self: 'a;

    /// Create an empty [`InnerNode`], with no children and no prefix
    fn empty() -> Self {
        Self::from_header(Self::Header::empty())
    }

    /// Create a new [`InnerNode`] using
    /// `prefix` as the node prefix and
    /// `prefix_len` as the node prefix length and
    ///
    /// This is done because when a prefix mismatch happens
    /// the length of the mismatch can be grater or equal to
    /// prefix size, since we search for the first child of the
    /// node to recreate the prefix, that's why we don't use
    /// `prefix.len()` as the node prefix length
    fn from_prefix(prefix: &[u8], prefix_len: usize) -> Self {
        Self::from_header(Self::Header::new(prefix, prefix_len))
    }

    /// Create a new [`InnerNode`] using a `Header`
    fn from_header(header: Self::Header) -> Self;

    /// Get the `Header` from the [`InnerNode`]
    fn header(&self) -> &Self::Header;

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    fn lookup_child(
        &self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, NUM_PREFIX_BYTES, Self::Header>>;

    /// Write a child pointer with key fragment to this inner node.
    ///
    /// If the key fragment already exists in the node, overwrite the existing
    /// child pointer.
    ///
    /// # Panics
    ///  - Panics when the node is full.
    fn write_child(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<Self::Key, Self::Value, NUM_PREFIX_BYTES, Self::Header>,
    );

    /// Attempt to remove a child pointer at the key fragment from this inner
    /// node.
    ///
    /// If the key fragment does not exist in this node, return `None`.
    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, NUM_PREFIX_BYTES, Self::Header>>;

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
        self.header().num_children() >= Self::TYPE.upper_capacity()
    }

    /// Create an iterator over all (key bytes, child pointers) in this inner
    /// node.
    ///
    /// # Safety
    ///  - The iterator type does not carry any lifetime, so the caller of this
    ///    function must enforce that the lifetime of the iterator does not
    ///    overlap with any mutating operations on the node.
    fn iter(&self) -> Self::Iter<'_>;

    /// Compares the compressed path of a node with the key and returns the
    /// number of equal bytes.
    ///
    /// # Safety
    ///  - `current_depth` > key len
    #[inline(always)]
    fn match_prefix(
        &self,
        key: &[u8],
        current_depth: usize,
    ) -> MatchPrefixResult<Self::Key, Self::Value, NUM_PREFIX_BYTES, Self::Header> {
        #[allow(unused_unsafe)]
        unsafe {
            // SAFETY: Since we are iterating the key and prefixes, we
            // expect that the depth never exceeds the key len.
            // Because if this happens we ran out of bytes in the key to match
            // and the whole process should be already finished
            assume!(current_depth <= key.len());
        }
        let (prefix, leaf_ptr) = self.read_full_prefix(current_depth);
        let key = &key[current_depth..];

        let matched_bytes = prefix
            .iter()
            .zip(key)
            .take_while(|(a, b)| **a == **b)
            .count();
        if matched_bytes < prefix.len() {
            MatchPrefixResult::Mismatch {
                mismatch: Mismatch {
                    matched_bytes,
                    prefix_byte: prefix[matched_bytes],
                    leaf_ptr,
                },
            }
        } else {
            MatchPrefixResult::Match { matched_bytes }
        }
    }

    /// Read the prefix as a whole, by reconstructing it if necessary from a
    /// leaf
    #[inline(always)]
    fn read_full_prefix(
        &self,
        current_depth: usize,
    ) -> (
        &[u8],
        Option<
            NodePtr<
                NUM_PREFIX_BYTES,
                LeafNode<Self::Key, Self::Value, NUM_PREFIX_BYTES, Self::Header>,
            >,
        >,
    ) {
        self.header().inner_read_full_prefix(self, current_depth)
    }

    /// Returns the minimum child pointer from this node and it's key
    ///
    /// # Safety
    ///  - Since this is a [`InnerNode`] we assume that the we hava at least one
    ///    child, (more strictly we have 2, because with one child the node
    ///    would have collapsed) so in this way we can avoid the [`Option`].
    ///    This is safe because if we had, no childs this current node should
    ///    have been deleted.
    fn min(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<Self::Key, Self::Value, NUM_PREFIX_BYTES, Self::Header>,
    );

    /// Returns the maximum child pointer from this node and it's key
    ///
    /// # Safety
    ///  - Since this is a [`InnerNode`] we assume that the we hava at least one
    ///    child, (more strictly we have 2, because with one child the node
    ///    would have collapsed) so in this way we can avoid the [`Option`].
    ///    This is safe because if we had, no childs this current node should
    ///    have been deleted.
    fn max(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<Self::Key, Self::Value, NUM_PREFIX_BYTES, Self::Header>,
    );

    /// Deep clones the inner node by allocating memory to a new one
    fn deep_clone(&self) -> NodePtr<NUM_PREFIX_BYTES, Self>
    where
        Self::Key: Clone,
        Self::Value: Clone;
}

/// Where a write should happen inside the node
enum WritePoint {
    /// In an already existing key fragment
    Existing(usize),
    /// As the last key fragment
    Last(usize),
    /// Shift the key fragments to the right
    Shift(usize),
}

/// Common methods for searching in an [`InnerNodeCompressed`]
trait SearchInnerNodeCompressed {
    /// Get the index of the child if it exists
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize>;

    /// Find the write point for `key_fragment`
    fn find_write_point(&self, key_fragment: u8) -> WritePoint;
}

/// Node type that has a compact representation for key bytes and children
/// pointers.
#[repr(C, align(8))]
pub struct InnerNodeCompressed<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
    const SIZE: usize,
> {
    /// The common node fields.
    pub header: H,
    /// An array that contains single key bytes in the same index as the
    /// `child_pointers` array contains the matching child tree.
    ///
    /// This array will only be initialized for the first `header.num_children`
    /// values.
    pub keys: [MaybeUninit<u8>; SIZE],
    /// An array that contains the child data.
    ///
    /// This array will only be initialized for the first `header.num_children`
    /// values.
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>; SIZE],
}

impl<
        K: AsBytes,
        V,
        const NUM_PREFIX_BYTES: usize,
        H: NodeHeader<NUM_PREFIX_BYTES>,
        const SIZE: usize,
    > Clone for InnerNodeCompressed<K, V, NUM_PREFIX_BYTES, H, SIZE>
{
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            keys: self.keys,
            child_pointers: self.child_pointers,
        }
    }
}

impl<
        K: AsBytes,
        V,
        const NUM_PREFIX_BYTES: usize,
        H: NodeHeader<NUM_PREFIX_BYTES>,
        const SIZE: usize,
    > fmt::Debug for InnerNodeCompressed<K, V, NUM_PREFIX_BYTES, H, SIZE>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (keys, child_pointers) = self.initialized_portion();
        f.debug_struct("InnerNodeBlock")
            .field("SIZE", &SIZE)
            .field("header", &self.header)
            .field("keys", &keys)
            .field("child_pointers", &child_pointers)
            .finish()
    }
}

/// Iterator type for an [`InnerNodeCompressed`]
pub type InnerNodeCompressedIter<'a, K, V, const NUM_PREFIX_BYTES: usize, H> =
    Zip<Copied<Iter<'a, u8>>, Copied<Iter<'a, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>>>;

impl<
        K: AsBytes,
        V,
        const NUM_PREFIX_BYTES: usize,
        H: NodeHeader<NUM_PREFIX_BYTES>,
        const SIZE: usize,
    > InnerNodeCompressed<K, V, NUM_PREFIX_BYTES, H, SIZE>
{
    /// Return the initialized portions of the keys and child pointer arrays.
    pub fn initialized_portion(&self) -> (&[u8], &[OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>]) {
        // SAFETY: The array prefix with length `header.num_children` is guaranteed to
        // be initialized
        unsafe {
            let num_children = self.header.num_children();
            assume!(num_children <= self.keys.len());
            (
                maybe_uninit_slice_assume_init_ref(self.keys.get_unchecked(0..num_children)),
                maybe_uninit_slice_assume_init_ref(
                    self.child_pointers.get_unchecked(0..num_children),
                ),
            )
        }
    }

    /// Generalized version of [`InnerNode::lookup_child`] for compressed nodes
    fn lookup_child_inner(
        &self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>
    where
        Self: SearchInnerNodeCompressed,
    {
        let idx = self.lookup_child_index(key_fragment)?;
        unsafe {
            // SAFETY: If `idx` is out of bounds the node should already have grown
            // so it's safe to assume that `idx` is in bounds
            assume!(idx < self.child_pointers.len());

            // SAFETY: The value at `child_index` is guaranteed to be initialized because
            // the `lookup_child_index` function will only search in the initialized portion
            // of the `child_pointers` array.
            Some(MaybeUninit::assume_init(self.child_pointers[idx]))
        }
    }

    /// Writes a child to the node by check the order of insertion
    ///
    /// # Panics
    ///  - This functions assumes that the write is gonna be inbound (i.e the
    ///    check for a full node is done previously to the call of this
    ///    function)
    fn write_child_inner(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    ) where
        Self: SearchInnerNodeCompressed,
    {
        let num_children = self.header.num_children();
        let idx = match self.find_write_point(key_fragment) {
            WritePoint::Existing(child_index) => child_index,
            WritePoint::Last(child_index) => {
                self.header.inc_num_children();
                child_index
            },
            WritePoint::Shift(child_index) => {
                #[allow(unused_unsafe)]
                unsafe {
                    // SAFETY: This is by construction, since the number of children
                    // is always <= maximum number o keys (childrens) that we can hold
                    assume!(num_children <= self.keys.len());

                    // SAFETY: When we are shifting children, because a new minimum one
                    // is being inserted this guarantees to us that the index of insertion
                    // is < current number of children (because if it was >= we wouldn't
                    // need to shift the data)
                    assume!(child_index < num_children);

                    // assume!(child_index + 1 + (num_children - child_index) <=
                    // self.keys.len());
                }
                self.keys
                    .copy_within(child_index..num_children, child_index + 1);
                self.child_pointers
                    .copy_within(child_index..num_children, child_index + 1);
                self.header.inc_num_children();
                child_index
            },
        };
        unsafe {
            // SAFETY: The check for a full node is done previsouly to the call
            // of this function, so it's safe to assume that the new child index is
            // in bounds
            self.write_child_at(idx, key_fragment, child_pointer);
        }
    }

    /// Writes a child to the node without bounds check or order
    ///
    /// # Safety
    /// - This functions assumes that the write is gonna be inbound (i.e the
    ///   check for a full node is done previously to the call of this function)
    pub unsafe fn write_child_unchecked(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    ) {
        let idx = self.header.num_children();
        unsafe { self.write_child_at(idx, key_fragment, child_pointer) };
        self.header.inc_num_children();
    }

    /// Writes a child to the node without bounds check or order
    ///
    /// # Safety
    ///  - This functions assumes that the write is gonna be inbound (i.e the
    ///    check for a full node is done previously to the call of this
    ///    function)
    unsafe fn write_child_at(
        &mut self,
        idx: usize,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    ) {
        unsafe {
            assume!(idx < self.keys.len());
            self.keys.get_unchecked_mut(idx).write(key_fragment);
            self.child_pointers
                .get_unchecked_mut(idx)
                .write(child_pointer);
        }
    }

    /// Removes child if it exists
    fn remove_child_inner(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>
    where
        Self: SearchInnerNodeCompressed,
    {
        let child_index = self.lookup_child_index(key_fragment)?;
        let child_ptr = mem::replace(&mut self.child_pointers[child_index], MaybeUninit::uninit());

        // Copy all the child_pointer and key values in higher indices down by one.
        self.child_pointers
            .copy_within((child_index + 1)..self.header.num_children(), child_index);
        self.keys
            .copy_within((child_index + 1)..self.header.num_children(), child_index);

        self.header.dec_num_children();
        // SAFETY: This child pointer value is initialized because we got it by
        // searching through the initialized keys and got the `Ok(index)` value.
        Some(unsafe { MaybeUninit::assume_init(child_ptr) })
    }

    /// Grows or shrinks the node
    fn change_block_size<const NEW_SIZE: usize>(
        &self,
    ) -> InnerNodeCompressed<K, V, NUM_PREFIX_BYTES, H, NEW_SIZE> {
        debug_assert!(
            self.header.num_children() <= NEW_SIZE,
            "Cannot change InnerNodeCompressed<{}> to size {} when it has more than {} children. \
             Currently has [{}] children.",
            SIZE,
            NEW_SIZE,
            NEW_SIZE,
            self.header.num_children()
        );

        let header = self.header.clone();
        let mut keys = [MaybeUninit::new(0); NEW_SIZE];
        let mut child_pointers = maybe_uninit_uninit_array();
        let num_children = header.num_children();

        #[allow(unused_unsafe)]
        unsafe {
            // SAFETY: By construction the number of children in the header
            // is kept in sync with the number of children written in the node
            // and if this number exceeds the maximum len the node should have
            // alredy grown. So we know for a fact that that num_children <= node len
            assume!(num_children <= self.keys.len());
            assume!(num_children <= self.child_pointers.len());

            // SAFETY: When calling this function the NEW_SIZE, should fit the nodes.
            // We only need to be careful when shrinking the node, since when growing
            // NEW_SIZE >= SIZE.
            // This function is only called in a shrink case when a node is removed from
            // a node and the new current size fits in the NEW_SIZE
            assume!(num_children <= keys.len());
            assume!(num_children <= child_pointers.len());
        }

        keys[..num_children].copy_from_slice(&self.keys[..num_children]);
        child_pointers[..num_children].copy_from_slice(&self.child_pointers[..num_children]);

        InnerNodeCompressed {
            header,
            keys,
            child_pointers,
        }
    }

    /// Transform node into a [`InnerNode48`]
    fn grow_node48(&self) -> InnerNode48<K, V, NUM_PREFIX_BYTES, H> {
        let header = self.header.clone();
        let mut child_indices = [RestrictedNodeIndex::<48>::EMPTY; 256];
        let mut child_pointers = maybe_uninit_uninit_array();

        let (keys, _) = self.initialized_portion();

        debug_assert_eq!(
            keys.len(),
            self.keys.len(),
            "Node must be full to grow to node 48"
        );

        for (index, key) in keys.iter().copied().enumerate() {
            // SAFETY: This `try_from` will not panic because index is guaranteed to
            // be 15 or less because of the length of the `InnerNode16.keys` array.
            child_indices[usize::from(key)] =
                unsafe { RestrictedNodeIndex::try_from(index).unwrap_unchecked() };
        }

        let num_children = header.num_children();

        #[allow(unused_unsafe)]
        unsafe {
            // SAFETY: By construction the number of children in the header
            // is kept in sync with the number of children written in the node
            // and if this number exceeds the maximum len the node should have
            // alredy grown. So we know for a fact that that num_children <= node len
            assume!(num_children <= self.child_pointers.len());

            // SAFETY: We know that the new size is >= old size, so this is safe
            assume!(num_children <= child_pointers.len());
        }

        child_pointers[..num_children].copy_from_slice(&self.child_pointers[..num_children]);

        InnerNode48 {
            header,
            child_indices,
            child_pointers,
        }
    }

    /// Get an iterator over the keys and values of the node
    fn inner_iter(&self) -> InnerNodeCompressedIter<'_, K, V, NUM_PREFIX_BYTES, H> {
        let (keys, nodes) = self.initialized_portion();
        keys.iter().copied().zip(nodes.iter().copied())
    }

    /// Deep clones the inner node by allocating memory to a new one
    fn inner_deep_clone(&self) -> NodePtr<NUM_PREFIX_BYTES, Self>
    where
        K: Clone,
        V: Clone,
        Self: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V, Header = H>,
    {
        let mut node = NodePtr::allocate_node_ptr(Self::from_header(self.header.clone()));
        let node_ref = node.as_mut_safe();
        for (idx, (key_fragment, child_pointer)) in self.iter().enumerate() {
            let child_pointer = child_pointer.deep_clone();
            unsafe { node_ref.write_child_at(idx, key_fragment, child_pointer) };
        }

        node
    }
}

/// Node that references between 2 and 4 children
pub type InnerNode4<K, V, const NUM_PREFIX_BYTES: usize, H> =
    InnerNodeCompressed<K, V, NUM_PREFIX_BYTES, H, 4>;

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    SearchInnerNodeCompressed for InnerNode4<K, V, NUM_PREFIX_BYTES, H>
{
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize> {
        let (keys, _) = self.initialized_portion();
        for (child_index, key) in keys.iter().enumerate() {
            if key_fragment == *key {
                return Some(child_index);
            }
        }

        None
    }

    fn find_write_point(&self, key_fragment: u8) -> WritePoint {
        let (keys, _) = self.initialized_portion();

        let mut child_index = 0;
        for key in keys {
            #[allow(clippy::comparison_chain)]
            if key_fragment < *key {
                return WritePoint::Shift(child_index);
            } else if key_fragment == *key {
                return WritePoint::Existing(child_index);
            }
            child_index += 1;
        }
        WritePoint::Last(child_index)
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Node<NUM_PREFIX_BYTES> for InnerNode4<K, V, NUM_PREFIX_BYTES, H>
{
    type Header = H;
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node4;
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    InnerNode<NUM_PREFIX_BYTES> for InnerNode4<K, V, NUM_PREFIX_BYTES, H>
{
    type GrownNode = InnerNode16<K, V, NUM_PREFIX_BYTES, H>;
    type Iter<'a> = InnerNodeCompressedIter<'a, K, V, NUM_PREFIX_BYTES, H> where Self: 'a;
    type ShrunkNode = InnerNode4<K, V, NUM_PREFIX_BYTES, H>;

    fn header(&self) -> &H {
        &self.header
    }

    fn from_header(header: H) -> Self {
        Self {
            header,
            child_pointers: maybe_uninit_uninit_array(),
            keys: maybe_uninit_uninit_array(),
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>> {
        self.lookup_child_inner(key_fragment)
    }

    fn write_child(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    ) {
        self.write_child_inner(key_fragment, child_pointer)
    }

    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>> {
        self.remove_child_inner(key_fragment)
    }

    fn grow(&self) -> Self::GrownNode {
        self.change_block_size()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        panic!("unable to shrink a Node4, something went wrong!")
    }

    fn iter(&self) -> Self::Iter<'_> {
        self.inner_iter()
    }

    fn min(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        let (keys, children) = self.initialized_portion();
        // SAFETY: Convered by the containing function
        unsafe {
            (
                keys.first().copied().unwrap_unchecked(),
                children.first().copied().unwrap_unchecked(),
            )
        }
    }

    fn max(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        let (keys, children) = self.initialized_portion();
        // SAFETY: Convered by the containing function
        unsafe {
            (
                keys.last().copied().unwrap_unchecked(),
                children.last().copied().unwrap_unchecked(),
            )
        }
    }

    #[inline(always)]
    fn deep_clone(&self) -> NodePtr<NUM_PREFIX_BYTES, Self>
    where
        K: Clone,
        V: Clone,
    {
        self.inner_deep_clone()
    }
}

/// Node that references between 5 and 16 children
pub type InnerNode16<K, V, const NUM_PREFIX_BYTES: usize, H> =
    InnerNodeCompressed<K, V, NUM_PREFIX_BYTES, H, 16>;

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    SearchInnerNodeCompressed for InnerNode16<K, V, NUM_PREFIX_BYTES, H>
{
    #[cfg(feature = "nightly")]
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize> {
        // SAFETY: Even though the type is marked is uninit data, when
        // crated this is filled with inited data, we just use it to
        // remind us that a portion might be unitialized
        let keys = unsafe { MaybeUninit::array_assume_init(self.keys) };
        let cmp = u8x16::splat(key_fragment)
            .simd_eq(u8x16::from_array(keys))
            .to_bitmask() as u32;
        let mask = (1u32 << self.header.num_children()) - 1;
        let bitfield = cmp & mask;
        if bitfield != 0 {
            Some(bitfield.trailing_zeros() as usize)
        } else {
            None
        }
    }

    #[cfg(not(feature = "nightly"))]
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize> {
        let (keys, _) = self.initialized_portion();
        for (child_index, key) in keys.iter().enumerate() {
            if key_fragment == *key {
                return Some(child_index);
            }
        }

        None
    }

    #[cfg(feature = "nightly")]
    fn find_write_point(&self, key_fragment: u8) -> WritePoint {
        match self.lookup_child_index(key_fragment) {
            Some(child_index) => WritePoint::Existing(child_index),
            None => {
                // SAFETY: Even though the type is marked is uninit data, when
                // crated this is filled with inited data, we just use it to
                // remind us that a portion might be unitialized
                let keys = unsafe { MaybeUninit::array_assume_init(self.keys) };
                let cmp = u8x16::splat(key_fragment)
                    .simd_lt(u8x16::from_array(keys))
                    .to_bitmask() as u32;
                let mask = (1u32 << self.header.num_children()) - 1;
                let bitfield = cmp & mask;
                if bitfield != 0 {
                    WritePoint::Shift(bitfield.trailing_zeros() as usize)
                } else {
                    WritePoint::Last(self.header.num_children())
                }
            },
        }
    }

    #[cfg(not(feature = "nightly"))]
    fn find_write_point(&self, key_fragment: u8) -> WritePoint {
        let (keys, _) = self.initialized_portion();

        let mut child_index = 0;
        for key in keys {
            #[allow(clippy::comparison_chain)]
            if key_fragment < *key {
                return WritePoint::Shift(child_index);
            } else if key_fragment == *key {
                return WritePoint::Existing(child_index);
            }
            child_index += 1;
        }
        WritePoint::Last(child_index)
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Node<NUM_PREFIX_BYTES> for InnerNode16<K, V, NUM_PREFIX_BYTES, H>
{
    type Header = H;
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node16;
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    InnerNode<NUM_PREFIX_BYTES> for InnerNode16<K, V, NUM_PREFIX_BYTES, H>
{
    type GrownNode = InnerNode48<K, V, NUM_PREFIX_BYTES, H>;
    type Iter<'a> = InnerNodeCompressedIter<'a, K, V, NUM_PREFIX_BYTES, H> where Self: 'a;
    type ShrunkNode = InnerNode4<K, V, NUM_PREFIX_BYTES, H>;

    fn header(&self) -> &H {
        &self.header
    }

    fn from_header(header: H) -> Self {
        Self {
            header,
            child_pointers: maybe_uninit_uninit_array(),
            keys: [MaybeUninit::new(0); 16],
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>> {
        self.lookup_child_inner(key_fragment)
    }

    fn write_child(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    ) {
        self.write_child_inner(key_fragment, child_pointer)
    }

    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>> {
        self.remove_child_inner(key_fragment)
    }

    fn grow(&self) -> Self::GrownNode {
        self.grow_node48()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        self.change_block_size()
    }

    fn iter(&self) -> Self::Iter<'_> {
        self.inner_iter()
    }

    fn min(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        let (keys, children) = self.initialized_portion();
        // SAFETY: Convered by the containing function
        unsafe {
            (
                keys.first().copied().unwrap_unchecked(),
                children.first().copied().unwrap_unchecked(),
            )
        }
    }

    fn max(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        let (keys, children) = self.initialized_portion();
        // SAFETY: Convered by the containing function
        unsafe {
            (
                keys.last().copied().unwrap_unchecked(),
                children.last().copied().unwrap_unchecked(),
            )
        }
    }

    #[inline(always)]
    fn deep_clone(&self) -> NodePtr<NUM_PREFIX_BYTES, Self>
    where
        K: Clone,
        V: Clone,
    {
        self.inner_deep_clone()
    }
}

/// A restricted index only valid from 0 to LIMIT - 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct RestrictedNodeIndex<const LIMIT: u8>(u8);

impl<const LIMIT: u8> RestrictedNodeIndex<LIMIT> {
    /// A placeholder index value that indicates that the index is not occupied
    pub const EMPTY: Self = RestrictedNodeIndex(LIMIT);

    /// Return true if the given index is the empty sentinel value
    pub fn is_empty(self) -> bool {
        self == Self::EMPTY
    }
}

impl<const LIMIT: u8> From<RestrictedNodeIndex<LIMIT>> for u8 {
    fn from(src: RestrictedNodeIndex<LIMIT>) -> Self {
        src.0
    }
}

impl<const LIMIT: u8> From<RestrictedNodeIndex<LIMIT>> for usize {
    fn from(src: RestrictedNodeIndex<LIMIT>) -> Self {
        usize::from(src.0)
    }
}

impl<const LIMIT: u8> TryFrom<usize> for RestrictedNodeIndex<LIMIT> {
    type Error = TryFromByteError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value < usize::from(LIMIT) {
            Ok(RestrictedNodeIndex(value as u8))
        } else {
            Err(TryFromByteError(LIMIT, value))
        }
    }
}

impl<const LIMIT: u8> TryFrom<u8> for RestrictedNodeIndex<LIMIT> {
    type Error = TryFromByteError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value < LIMIT {
            Ok(RestrictedNodeIndex(value))
        } else {
            Err(TryFromByteError(LIMIT, usize::from(value)))
        }
    }
}

impl<const LIMIT: u8> PartialOrd for RestrictedNodeIndex<LIMIT> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.0 == LIMIT || other.0 == LIMIT {
            None
        } else {
            Some(self.0.cmp(&other.0))
        }
    }
}

/// The error type returned when attempting to construct an index outside the
/// accepted range of a PartialNodeIndex.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TryFromByteError(u8, usize);

impl fmt::Display for TryFromByteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Input value [{}] is greater than the allowed maximum [{}] for PartialNodeIndex.",
            self.1, self.0
        )
    }
}

impl Error for TryFromByteError {}

/// Node that references between 17 and 49 children
#[repr(C, align(8))]
pub struct InnerNode48<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
> {
    /// The common node fields.
    pub header: H,
    /// An array that maps key bytes (as the index) to the index value in the
    /// `child_pointers` array.
    ///
    /// All the `child_indices` values are guaranteed to be
    /// `PartialNodeIndex<48>::EMPTY` when the node is constructed.
    pub child_indices: [RestrictedNodeIndex<48>; 256],
    /// For each element in this array, it is assumed to be initialized if there
    /// is a index in the `child_indices` array that points to it
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>; 48],
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> fmt::Debug
    for InnerNode48<K, V, NUM_PREFIX_BYTES, H>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode48")
            .field("header", &self.header)
            .field("child_indices", &self.child_indices)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Clone
    for InnerNode48<K, V, NUM_PREFIX_BYTES, H>
{
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_indices: self.child_indices,
            child_pointers: self.child_pointers,
        }
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    InnerNode48<K, V, NUM_PREFIX_BYTES, H>
{
    /// Return the initialized portions of the child pointer array.
    pub fn initialized_child_pointers(&self) -> &[OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>] {
        unsafe {
            // SAFETY: The array prefix with length `header.num_children` is guaranteed to
            // be initialized
            assume!(self.header.num_children() <= self.child_pointers.len());
            maybe_uninit_slice_assume_init_ref(&self.child_pointers[..self.header.num_children()])
        }
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Node<NUM_PREFIX_BYTES> for InnerNode48<K, V, NUM_PREFIX_BYTES, H>
{
    type Header = H;
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node48;
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    InnerNode<NUM_PREFIX_BYTES> for InnerNode48<K, V, NUM_PREFIX_BYTES, H>
{
    type GrownNode = InnerNode256<K, V, NUM_PREFIX_BYTES, H>;
    #[cfg(not(feature = "nightly"))]
    type Iter<'a> = stable_iters::Node48Iter<'a, K, V, NUM_PREFIX_BYTES, H> where Self: 'a;
    #[cfg(feature = "nightly")]
    type Iter<'a> = Map<FilterMap<Enumerate<Iter<'a, RestrictedNodeIndex<48>>>, impl FnMut((usize, &'a RestrictedNodeIndex<48>)) -> Option<(u8, usize)>>, impl FnMut((u8, usize)) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>)> where Self: 'a;
    type ShrunkNode = InnerNode16<K, V, NUM_PREFIX_BYTES, H>;

    fn header(&self) -> &H {
        &self.header
    }

    fn from_header(header: H) -> Self {
        InnerNode48 {
            header,
            child_indices: [RestrictedNodeIndex::<48>::EMPTY; 256],
            child_pointers: maybe_uninit_uninit_array(),
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>> {
        let index = &self.child_indices[usize::from(key_fragment)];
        let child_pointers = self.initialized_child_pointers();
        if !index.is_empty() {
            let idx = usize::from(*index);

            #[allow(unused_unsafe)]
            unsafe {
                // SAFETY: If `idx` is out of bounds we have more than
                // 48 childs in this node, so it should have already
                // grown. So it's safe to assume that it's in bounds
                assume!(idx < child_pointers.len());
            }
            Some(child_pointers[idx])
        } else {
            None
        }
    }

    fn write_child(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    ) {
        let key_fragment_idx = usize::from(key_fragment);
        let child_index = if self.child_indices[key_fragment_idx] == RestrictedNodeIndex::EMPTY {
            let child_index = self.header.num_children();
            debug_assert!(child_index < self.child_pointers.len(), "node is full");

            // SAFETY: By construction the number of children in the header
            // is kept in sync with the number of children written in the node
            // and if this number exceeds the maximum len the node should have
            // alredy grown. So we know for a fact that that num_children <= node len.
            //
            // With this we know that child_index is <= 47, because at the 48th time
            // calling this function for writing, the current len will bet 47, and
            // after this insert we increment it to 48, so this symbolizes that the
            // node is full and before calling this function again the node should
            // have alredy grown
            self.child_indices[key_fragment_idx] =
                unsafe { RestrictedNodeIndex::try_from(child_index).unwrap_unchecked() };
            self.header.inc_num_children();
            child_index
        } else {
            // overwrite existing
            usize::from(self.child_indices[key_fragment_idx])
        };

        // SAFETY: This index can be up to <= 47 as decribed above
        #[allow(unused_unsafe)]
        unsafe {
            assume!(child_index < self.child_pointers.len());
        }
        self.child_pointers[child_index].write(child_pointer);
    }

    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>> {
        let restricted_index = self.child_indices[usize::from(key_fragment)];
        if restricted_index.is_empty() {
            return None;
        }

        // Replace child pointer with unitialized value, even though it may possibly be
        // overwritten by the compaction step
        let child_ptr = mem::replace(
            &mut self.child_pointers[usize::from(restricted_index)],
            MaybeUninit::uninit(),
        );

        // Copy all the child_pointer values in higher indices down by one.
        self.child_pointers.copy_within(
            (usize::from(restricted_index) + 1)..self.header.num_children(),
            usize::from(restricted_index),
        );

        // Take all child indices that are greater than the index we're removing, and
        // subtract one so that they remain valid
        for other_restrict_index in &mut self.child_indices {
            if matches!(
                restricted_index.partial_cmp(other_restrict_index),
                Some(Ordering::Less)
            ) {
                // PANIC SAFETY: This will not underflow, because it is guaranteed to be
                // greater than at least 1 other index. This will not panic in the
                // `try_from` because the new value is derived from an existing restricted
                // index.
                *other_restrict_index =
                    RestrictedNodeIndex::try_from(other_restrict_index.0 - 1).unwrap();
            }
        }

        self.child_indices[usize::from(key_fragment)] = RestrictedNodeIndex::EMPTY;
        self.header.dec_num_children();
        // SAFETY: This child pointer value is initialized because we got it by using a
        // non-`RestrictedNodeIndex::<>::EMPTY` index from the child indices array.
        Some(unsafe { MaybeUninit::assume_init(child_ptr) })
    }

    fn grow(&self) -> Self::GrownNode {
        let header = self.header.clone();
        let mut child_pointers = [None; 256];
        let initialized_child_pointers = self.initialized_child_pointers();
        for (key_fragment, idx) in self.child_indices.iter().enumerate() {
            if idx.is_empty() {
                continue;
            }

            let idx = usize::from(*idx);

            #[allow(unused_unsafe)]
            unsafe {
                // SAFETY: When growing initialized_child_pointers should be full
                // i.e initialized_child_pointers len == 48. And idx <= 47, since
                // we can't insert in a full, node
                assume!(idx < initialized_child_pointers.len());
            }
            let child_pointer = initialized_child_pointers[idx];
            child_pointers[key_fragment] = Some(child_pointer);
        }

        InnerNode256 {
            header,
            child_pointers,
        }
    }

    fn shrink(&self) -> Self::ShrunkNode {
        debug_assert!(
            self.header.num_children() <= 16,
            "Cannot shrink a Node48 when it has more than 16 children. Currently has [{}] \
             children.",
            self.header.num_children()
        );

        let header = self.header.clone();

        let mut key_and_child_ptrs = maybe_uninit_uninit_array::<_, 16>();

        for (idx, value) in self.iter().enumerate() {
            key_and_child_ptrs[idx].write(value);
        }

        let init_key_and_child_ptrs = {
            // SAFETY: The first `num_children` are guaranteed to be initialized in this
            // array because the previous iterator loops through all children of the inner
            // node.
            let init_key_and_child_ptrs = unsafe {
                maybe_uninit_slice_assume_init_mut(&mut key_and_child_ptrs[..header.num_children()])
            };

            init_key_and_child_ptrs.sort_unstable_by_key(|(key_byte, _)| *key_byte);

            init_key_and_child_ptrs
        };

        let mut keys = maybe_uninit_uninit_array();
        let mut child_pointers = maybe_uninit_uninit_array();

        for (idx, (key_byte, child_ptr)) in init_key_and_child_ptrs.iter().copied().enumerate() {
            keys[idx].write(key_byte);
            child_pointers[idx].write(child_ptr);
        }

        InnerNodeCompressed {
            header,
            keys,
            child_pointers,
        }
    }

    fn iter(&self) -> Self::Iter<'_> {
        let child_pointers = self.initialized_child_pointers();

        #[cfg(not(feature = "nightly"))]
        {
            stable_iters::Node48Iter {
                it: self.child_indices.iter().enumerate(),
                child_pointers,
            }
        }

        #[cfg(feature = "nightly")]
        {
            self.child_indices
                .iter()
                .enumerate()
                .filter_map(|(key, idx)| {
                    (!idx.is_empty()).then_some((key as u8, usize::from(*idx)))
                })
                // SAFETY: By the construction of `Self` idx, must always
                // be inbounds
                .map(|(key, idx)| unsafe { (key, *child_pointers.get_unchecked(idx)) })
        }
    }

    #[cfg(feature = "nightly")]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        // SAFETY: Since `RestrictedNodeIndex` is
        // repr(u8) is safe to transmute it
        let child_indices: &[u8; 256] = unsafe { std::mem::transmute(&self.child_indices) };
        let empty = u8x64::splat(48);
        let r0 = u8x64::from_array(child_indices[0..64].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r1 = u8x64::from_array(child_indices[64..128].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r2 = u8x64::from_array(child_indices[128..192].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r3 = u8x64::from_array(child_indices[192..256].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();

        let key = if r0 != u64::MAX {
            r0.trailing_ones()
        } else if r1 != u64::MAX {
            r1.trailing_ones() + 64
        } else if r2 != u64::MAX {
            r2.trailing_ones() + 128
        } else {
            r3.trailing_ones() + 192
        } as usize;

        unsafe {
            // SAFETY: key can be at up to 256, but we are in a inner node
            // this means that this node has at least 1 child (it's even more
            // strict since, if we have 1 child the node would collapse), so we
            // know that exists at least one idx where != 48
            assume!(key < self.child_indices.len());
        }

        let idx = usize::from(self.child_indices[key]);
        let child_pointers = self.initialized_child_pointers();

        unsafe {
            // SAFETY: We know that idx is in bounds, because the value can't be
            // constructed if it >= 48 and also it has to be < num children, since
            // it's constructed from the num children before being incremented during
            // insertion process
            assume!(idx < child_pointers.len());
        }

        (key as u8, child_pointers[idx])
    }

    #[cfg(not(feature = "nightly"))]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        for (key, idx) in self.child_indices.iter().enumerate() {
            if idx.is_empty() {
                continue;
            }
            let child_pointers = self.initialized_child_pointers();
            return (key as u8, child_pointers[usize::from(*idx)]);
        }
        unreachable!();
    }

    #[cfg(feature = "nightly")]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        // SAFETY: Since `RestrictedNodeIndex` is
        // repr(u8) is safe to transmute it
        let child_indices: &[u8; 256] = unsafe { std::mem::transmute(&self.child_indices) };
        let empty = u8x64::splat(48);
        let r0 = u8x64::from_array(child_indices[0..64].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r1 = u8x64::from_array(child_indices[64..128].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r2 = u8x64::from_array(child_indices[128..192].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r3 = u8x64::from_array(child_indices[192..256].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();

        let key = if r3 != u64::MAX {
            255 - r3.leading_ones()
        } else if r2 != u64::MAX {
            191 - r2.leading_ones()
        } else if r1 != u64::MAX {
            127 - r1.leading_ones()
        } else {
            // SAFETY: This subtraction can't fail, because we know that
            // we have at least one child, so the number of leading ones
            // in this last case is <= 63
            63 - r0.leading_ones()
        } as usize;

        unsafe {
            // SAFETY: idx can be at up to 255 so it's in bounds
            assume!(key < self.child_indices.len());
        }

        let idx = usize::from(self.child_indices[key]);
        let child_pointers = self.initialized_child_pointers();

        unsafe {
            // SAFETY: We know that idx is in bounds, because the value can't be
            // constructed if it >= 48 and also it has to be < num children, since
            // it's constructed from the num children before being incremented during
            // insertion process
            assume!(idx < child_pointers.len());
        }

        (key as u8, child_pointers[idx])
    }

    #[cfg(not(feature = "nightly"))]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        for (key, idx) in self.child_indices.iter().enumerate().rev() {
            if idx.is_empty() {
                continue;
            }
            let child_pointers = self.initialized_child_pointers();
            return (key as u8, child_pointers[usize::from(*idx)]);
        }
        unreachable!();
    }

    #[inline(always)]
    fn deep_clone(&self) -> NodePtr<NUM_PREFIX_BYTES, Self>
    where
        K: Clone,
        V: Clone,
    {
        let mut node = NodePtr::allocate_node_ptr(Self::from_header(self.header.clone()));
        let node_ref = node.as_mut_safe();
        for (idx, (key_fragment, child_pointer)) in self.iter().enumerate() {
            let child_pointer = child_pointer.deep_clone();
            // SAFETY: This iterator is bound to have a maximum of
            // 256 iterations, so its safe to unwrap the result
            node_ref.child_indices[usize::from(key_fragment)] =
                unsafe { RestrictedNodeIndex::try_from(idx).unwrap_unchecked() };

            #[allow(unused_unsafe)]
            unsafe {
                // SAFETY: This idx is in bounds, since the number
                // of iterations is always <= 48 (i.e 0-47)
                assume!(idx < node_ref.child_pointers.len());
            }
            node_ref.child_pointers[idx].write(child_pointer);
        }

        node
    }
}

/// Node that references between 49 and 256 children
#[repr(C, align(8))]
pub struct InnerNode256<
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
> {
    /// The common node fields.
    pub header: H,
    /// An array that directly maps a key byte (as index) to a child node.
    pub child_pointers: [Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>; 256],
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> fmt::Debug
    for InnerNode256<K, V, NUM_PREFIX_BYTES, H>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode256")
            .field("header", &self.header)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Clone
    for InnerNode256<K, V, NUM_PREFIX_BYTES, H>
{
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_pointers: self.child_pointers,
        }
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Node<NUM_PREFIX_BYTES> for InnerNode256<K, V, NUM_PREFIX_BYTES, H>
{
    type Header = H;
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node256;
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    InnerNode<NUM_PREFIX_BYTES> for InnerNode256<K, V, NUM_PREFIX_BYTES, H>
{
    type GrownNode = Self;
    #[cfg(not(feature = "nightly"))]
    type Iter<'a> = stable_iters::Node256Iter<'a, K, V, NUM_PREFIX_BYTES, H> where Self: 'a;
    #[cfg(feature = "nightly")]
    type Iter<'a> = FilterMap<Enumerate<Iter<'a, Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>>>, impl FnMut((usize, &'a Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>)) -> Option<(u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>)>> where Self: 'a;
    type ShrunkNode = InnerNode48<K, V, NUM_PREFIX_BYTES, H>;

    fn header(&self) -> &H {
        &self.header
    }

    fn from_header(header: H) -> Self {
        InnerNode256 {
            header,
            child_pointers: [None; 256],
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>> {
        self.child_pointers[usize::from(key_fragment)]
    }

    fn write_child(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>,
    ) {
        let key_fragment_idx = usize::from(key_fragment);
        let existing_pointer = self.child_pointers[key_fragment_idx];
        self.child_pointers[key_fragment_idx] = Some(child_pointer);
        if existing_pointer.is_none() {
            self.header.inc_num_children();
        }
    }

    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>> {
        let removed_child = self.child_pointers[usize::from(key_fragment)].take();

        if removed_child.is_some() {
            self.header.dec_num_children();
        }

        removed_child
    }

    fn grow(&self) -> Self::GrownNode {
        panic!("unable to grow a Node256, something went wrong!")
    }

    fn shrink(&self) -> Self::ShrunkNode {
        debug_assert!(
            self.header.num_children() <= 48,
            "Cannot shrink a Node256 when it has more than 48 children. Currently has [{}] \
             children.",
            self.header.num_children()
        );

        let header = self.header.clone();
        let mut child_indices = [RestrictedNodeIndex::<48>::EMPTY; 256];
        let mut child_pointers = maybe_uninit_uninit_array();

        for (child_index, (key_byte, child_ptr)) in self.iter().enumerate() {
            // PANIC SAFETY: This `try_from` will not panic because the `next_index` value
            // is guaranteed to be 48 or less by the `assert!(num_children < 48)` at the
            // start of the function.
            let key_byte = usize::from(key_byte);
            child_indices[key_byte] = RestrictedNodeIndex::try_from(child_index).unwrap();
            child_pointers[child_index].write(child_ptr);
        }

        InnerNode48 {
            header,
            child_indices,
            child_pointers,
        }
    }

    fn iter(&self) -> Self::Iter<'_> {
        #[cfg(not(feature = "nightly"))]
        {
            stable_iters::Node256Iter {
                it: self.child_pointers.iter().enumerate(),
            }
        }

        #[cfg(feature = "nightly")]
        {
            self.child_pointers
                .iter()
                .enumerate()
                .filter_map(|(key, node)| node.map(|node| (key as u8, node)))
        }
    }

    #[cfg(feature = "nightly")]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        // SAFETY: Due to niche optimization Option<NonNull> has the same
        // size as NonNull and NonNull has the same size as usize
        // so it's safe to transmute
        let child_pointers: &[usize; 256] = unsafe { std::mem::transmute(&self.child_pointers) };
        let empty = usizex64::splat(0);
        let r0 = usizex64::from_array(child_pointers[0..64].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r1 = usizex64::from_array(child_pointers[64..128].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r2 = usizex64::from_array(child_pointers[128..192].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r3 = usizex64::from_array(child_pointers[192..256].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();

        let key = if r0 != u64::MAX {
            r0.trailing_ones()
        } else if r1 != u64::MAX {
            r1.trailing_ones() + 64
        } else if r2 != u64::MAX {
            r2.trailing_ones() + 128
        } else {
            r3.trailing_ones() + 192
        } as usize;

        unsafe {
            // SAFETY: key can be at up to 256, but we know that we have
            // at least one inner child, it's guarentee to be in bounds
            assume!(key < self.child_pointers.len());
        }

        // SAFETY: Convered by the containing function
        (key as u8, unsafe {
            self.child_pointers[key].unwrap_unchecked()
        })
    }

    #[cfg(not(feature = "nightly"))]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        for (key, child_pointer) in self.child_pointers.iter().enumerate() {
            match child_pointer {
                Some(child_pointer) => return (key as u8, *child_pointer),
                None => continue,
            }
        }
        unreachable!()
    }

    #[cfg(feature = "nightly")]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        // SAFETY: Due to niche optimization Option<NonNull> has the same
        // size as NonNull and NonNull has the same size as usize
        // so it's safe to transmute
        let child_pointers: &[usize; 256] = unsafe { std::mem::transmute(&self.child_pointers) };
        let empty = usizex64::splat(0);
        let r0 = usizex64::from_array(child_pointers[0..64].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r1 = usizex64::from_array(child_pointers[64..128].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r2 = usizex64::from_array(child_pointers[128..192].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();
        let r3 = usizex64::from_array(child_pointers[192..256].try_into().unwrap())
            .simd_eq(empty)
            .to_bitmask();

        let key = if r3 != u64::MAX {
            255 - r3.leading_ones()
        } else if r2 != u64::MAX {
            191 - r2.leading_ones()
        } else if r1 != u64::MAX {
            127 - r1.leading_ones()
        } else {
            // SAFETY: This subtraction can't fail, because we know that
            // we have at least one child, so the number of leading ones
            // in this last case is <= 63
            63 - r0.leading_ones()
        } as usize;

        unsafe {
            // SAFETY: idx can be at up to 255, so it's in bounds
            assume!(key < self.child_pointers.len());
        }

        // SAFETY: Convered by the containing function
        (key as u8, unsafe {
            self.child_pointers[key].unwrap_unchecked()
        })
    }

    #[cfg(not(feature = "nightly"))]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>) {
        for (key, child_pointer) in self.child_pointers.iter().enumerate().rev() {
            match child_pointer {
                Some(child_pointer) => return (key as u8, *child_pointer),
                None => continue,
            }
        }
        unreachable!()
    }

    #[inline(always)]
    fn deep_clone(&self) -> NodePtr<NUM_PREFIX_BYTES, Self>
    where
        K: Clone,
        V: Clone,
    {
        let mut node = NodePtr::allocate_node_ptr(Self::from_header(self.header.clone()));
        let node_ref = node.as_mut_safe();
        for (key_fragment, child_pointer) in self.iter() {
            node_ref.child_pointers[usize::from(key_fragment)] = Some(child_pointer.deep_clone());
        }

        node
    }
}

#[allow(dead_code)]
mod stable_iters {
    use super::*;

    pub struct Node48Iter<
        'a,
        K: AsBytes,
        V,
        const NUM_PREFIX_BYTES: usize,
        H: NodeHeader<NUM_PREFIX_BYTES>,
    > {
        pub(crate) it: Enumerate<Iter<'a, RestrictedNodeIndex<48>>>,
        pub(crate) child_pointers: &'a [OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>],
    }

    impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Iterator
        for Node48Iter<'a, K, V, NUM_PREFIX_BYTES, H>
    {
        type Item = (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>);

        fn next(&mut self) -> Option<Self::Item> {
            for (key, idx) in self.it.by_ref() {
                if idx.is_empty() {
                    continue;
                }
                let key = key as u8;
                // SAFETY: This idx is in bounds, since the number
                // of iterations is always <= 48 (i.e 0-47)
                let child_pointer =
                    unsafe { *self.child_pointers.get_unchecked(usize::from(*idx)) };
                return Some((key, child_pointer));
            }
            None
        }
    }

    impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
        DoubleEndedIterator for Node48Iter<'a, K, V, NUM_PREFIX_BYTES, H>
    {
        fn next_back(&mut self) -> Option<Self::Item> {
            while let Some((key, idx)) = self.it.next_back() {
                if idx.is_empty() {
                    continue;
                }
                let key = key as u8;
                // SAFETY: This idx is in bounds, since the number
                // of iterations is always <= 48 (i.e 0-47)
                let child_pointer =
                    unsafe { *self.child_pointers.get_unchecked(usize::from(*idx)) };
                return Some((key, child_pointer));
            }
            None
        }
    }

    impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
        FusedIterator for Node48Iter<'a, K, V, NUM_PREFIX_BYTES, H>
    {
    }

    pub struct Node256Iter<
        'a,
        K: AsBytes,
        V,
        const NUM_PREFIX_BYTES: usize,
        H: NodeHeader<NUM_PREFIX_BYTES>,
    > {
        pub(crate) it: Enumerate<Iter<'a, Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>>>,
    }

    impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Iterator
        for Node256Iter<'a, K, V, NUM_PREFIX_BYTES, H>
    {
        type Item = (u8, OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>);

        fn next(&mut self) -> Option<Self::Item> {
            for (key, node) in self.it.by_ref() {
                match node {
                    Some(node) => return Some((key as u8, *node)),
                    None => continue,
                }
            }
            None
        }
    }

    impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
        DoubleEndedIterator for Node256Iter<'a, K, V, NUM_PREFIX_BYTES, H>
    {
        fn next_back(&mut self) -> Option<Self::Item> {
            while let Some((key, node)) = self.it.next_back() {
                match node {
                    Some(node) => return Some((key as u8, *node)),
                    None => continue,
                }
            }
            None
        }
    }

    impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
        FusedIterator for Node256Iter<'a, K, V, NUM_PREFIX_BYTES, H>
    {
    }
}

/// Node that contains a single leaf value.
#[derive(Debug, Clone)]
#[repr(align(8))]
pub struct LeafNode<K, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> {
    /// The leaf value.
    value: V,
    /// The full key that the `value` was stored with.
    key: K,

    _marker: PhantomData<H>,
}

impl<K, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    LeafNode<K, V, NUM_PREFIX_BYTES, H>
{
    /// Create a new leaf node with the given value.
    pub fn new(key: K, value: V) -> Self {
        LeafNode {
            value,
            key,
            _marker: PhantomData,
        }
    }

    /// Returns a shared reference to the key contained by this leaf node
    pub fn key_ref(&self) -> &K {
        &self.key
    }

    /// Returns a shared reference to the value contained by this leaf node
    pub fn value_ref(&self) -> &V {
        &self.value
    }

    /// Returns a mutable reference to the value contained by this leaf node
    pub fn value_mut(&mut self) -> &mut V {
        &mut self.value
    }

    /// Return shared references to the key and value contained by this leaf
    /// node
    pub fn entry_ref(&self) -> (&K, &V) {
        (&self.key, &self.value)
    }

    /// Return mutable references to the key and value contained by this leaf
    /// node
    pub fn entry_mut(&mut self) -> (&mut K, &mut V) {
        (&mut self.key, &mut self.value)
    }

    /// Consume the leaf node and return a tuple of the key and value
    pub fn into_entry(self) -> (K, V) {
        (self.key, self.value)
    }

    /// Check that the provided full key is the same one as the stored key.
    pub fn matches_full_key<Q>(&self, possible_key: &Q) -> bool
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        self.key.borrow().as_bytes().eq(possible_key.as_bytes())
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Node<NUM_PREFIX_BYTES> for LeafNode<K, V, NUM_PREFIX_BYTES, H>
{
    type Header = H;
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Leaf;
}
