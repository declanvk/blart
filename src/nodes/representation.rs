//! Trie node representation

// pub use self::iterators::*;
use crate::{minimum_unchecked, tagged_pointer::TaggedPointer, AsBytes};
use std::{
    arch::x86_64::{__m128i, _mm_movemask_epi8},
    array::from_fn,
    borrow::Borrow,
    cmp::Ordering,
    error::Error,
    fmt,
    hash::Hash,
    hint::unreachable_unchecked,
    intrinsics::{assume, likely},
    iter::{Copied, Enumerate, FilterMap, FusedIterator, Map, Zip},
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
    ops::Range,
    ptr::{self, NonNull},
    simd::{
        cmp::{SimdPartialEq, SimdPartialOrd},
        u8x16, u8x64, usizex64, Simd,
    },
    slice::Iter,
};

// mod iterators;

#[cfg(test)]
mod tests;

/// The number of bytes stored for path compression in the node header.
pub const NUM_PREFIX_BYTES: usize = 16;

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

    /// Attempt to convert a u8 value to a [`NodeType`], returning None if there
    /// is no match.
    pub const fn from_u8(src: u8) -> NodeType {
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

/// The common header for all inner nodes
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[repr(align(8))]
pub struct Header {
    /// Number of children of this inner node. This field has no meaning for
    /// a leaf node.
    ///
    /// This needs to be a [`u16`], since a node 256 can hold up to 256 children
    /// if this was a [`u8`] (0-255) it would overflow when adding the last
    /// element
    pub num_children: u16,
    /// Number of bytes used by the prefix
    pub prefix_len: u32,
    /// The key prefix for this node.
    pub prefix: [u8; NUM_PREFIX_BYTES],
}

impl Header {
    pub fn new(prefix: &[u8], prefix_len: usize) -> Self {
        let mut header = Header {
            num_children: 0,
            prefix_len: prefix_len as u32,
            prefix: [0; NUM_PREFIX_BYTES],
        };
        let len = prefix.len().min(NUM_PREFIX_BYTES);
        header.prefix[..len].copy_from_slice(&prefix[..len]);

        header
    }

    /// Create a new `Header` for an empty node.
    pub fn empty() -> Self {
        Header {
            num_children: 0,
            prefix_len: 0,
            prefix: [0; NUM_PREFIX_BYTES],
        }
    }

    /// Read the initialized portion of the prefix present in the header.
    pub fn read_prefix(&self) -> &[u8] {
        &self.prefix[0..self.capped_prefix_len()]
    }

    /// Return the number of bytes in the prefix.
    pub fn prefix_len(&self) -> usize {
        self.prefix_len as usize
    }

    pub fn capped_prefix_len(&self) -> usize {
        (self.prefix_len as usize).min(NUM_PREFIX_BYTES)
    }

    /// Return the number of children of this node.
    pub fn num_children(&self) -> usize {
        usize::from(self.num_children)
    }

    /// Left trim by [`len`], copies the remaining data to the beging of the
    /// prefix
    ///
    /// # Panics
    ///
    /// If `len` > length of the prefix
    pub fn ltrim_by(&mut self, len: usize) {
        self.prefix_len -= len as u32;

        let begin = len;
        let end = begin + self.capped_prefix_len();
        unsafe {
            // SAFETY: This function is called when mismatch happened and
            // we used the node to match the number of bytes,
            // by this we know that len < prefix len, but since we + 1,
            // to skip the key byte we have that len <= prefix len
            assume(end <= self.prefix.len());

            // SAFETY: This is by construction end = begin + len
            assume(begin <= end);
        }
        self.prefix.copy_within(begin..end, 0);
    }

    /// Left trim by [`len`], copies the remaining data to the beging of the
    /// prefix, in this case we use a leaf to achieve this, we also need the
    /// [`depth`] (a.k.a how many bytes of the leaf have already been used)
    pub fn ltrim_by_with_leaf<K: AsBytes, V>(
        &mut self,
        len: usize,
        depth: usize,
        leaf_ptr: NodePtr<LeafNode<K, V>>,
    ) {
        self.prefix_len -= len as u32;

        let leaf_key = unsafe { leaf_ptr.as_key_ref().as_bytes() };

        let begin = depth + len;
        let end = begin + self.capped_prefix_len();
        let len = end - begin;
        unsafe {
            // SAFETY: This function is called a mismatch happened and
            // we used the leaf to match the number of matching bytes,
            // by this we know that len < prefix len, but since we + 1,
            // to skip the key byte we have that len <= prefix len
            assume(end <= leaf_key.len());

            // SAFETY: This is by construction end = begin + len
            assume(begin <= end);
        }

        let leaf_key = &leaf_key[begin..end];
        let leaf_key = &leaf_key[..leaf_key.len().min(NUM_PREFIX_BYTES)];
        self.prefix[..len.min(NUM_PREFIX_BYTES)].copy_from_slice(leaf_key)
    }

    pub fn push_prefix(&mut self, new: &[u8], new_len: usize) {
        let begin = self.capped_prefix_len();
        let end = (begin + new.len()).min(NUM_PREFIX_BYTES);
        let len = end - begin;
        self.prefix[begin..end].copy_from_slice(&new[..len]);
        self.prefix_len += new_len as u32;
    }

    pub fn clear_prefix(&mut self) -> ([u8; NUM_PREFIX_BYTES], usize, usize) {
        let len = self.prefix_len();
        let capped_len = self.capped_prefix_len();
        self.prefix_len = 0;

        (self.prefix, len, capped_len)
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
pub struct OpaqueNodePtr<K: AsBytes, V>(TaggedPointer<OpaqueValue, 3>, PhantomData<(K, V)>);

impl<K: AsBytes, V> Copy for OpaqueNodePtr<K, V> {}

impl<K: AsBytes, V> Clone for OpaqueNodePtr<K, V> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<K: AsBytes, V> fmt::Debug for OpaqueNodePtr<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("OpaqueNodePtr").field(&self.0).finish()
    }
}

impl<K: AsBytes, V> fmt::Pointer for OpaqueNodePtr<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

impl<K: AsBytes, V> Eq for OpaqueNodePtr<K, V> {}

impl<K: AsBytes, V> PartialEq for OpaqueNodePtr<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K: AsBytes, V> Hash for OpaqueNodePtr<K, V> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<K: AsBytes, V> OpaqueNodePtr<K, V> {
    /// Construct a new opaque node pointer from an existing non-null node
    /// pointer.
    pub fn new<N>(pointer: NonNull<N>) -> Self
    where
        N: Node<Value = V>,
    {
        let mut tagged_ptr = TaggedPointer::from(pointer).cast::<OpaqueValue>();
        tagged_ptr.set_data(N::TYPE as usize);

        OpaqueNodePtr(tagged_ptr, PhantomData)
    }

    /// Return `true` if this Node_ pointer points to the specified concrete
    /// [`NodeType`].
    pub fn is<N: Node>(&self) -> bool {
        self.0.to_data() == usize::from(N::TYPE as u8)
    }

    /// Create a non-opaque node pointer that will eliminate future type
    /// assertions, if the type of the pointed node matches the given
    /// node type.
    pub fn cast<N: Node>(self) -> Option<NodePtr<N>> {
        if self.is::<N>() {
            Some(NodePtr(self.0.cast::<N>().into()))
        } else {
            None
        }
    }

    /// Cast this opaque pointer type an enum that contains a pointer to the
    /// concrete node type.
    pub fn to_node_ptr(self) -> ConcreteNodePtr<K, V> {
        match self.node_type() {
            NodeType::Node4 => {
                ConcreteNodePtr::Node4(NodePtr(self.0.cast::<InnerNode4<K, V>>().into()))
            },
            NodeType::Node16 => {
                ConcreteNodePtr::Node16(NodePtr(self.0.cast::<InnerNode16<K, V>>().into()))
            },
            NodeType::Node48 => {
                ConcreteNodePtr::Node48(NodePtr(self.0.cast::<InnerNode48<K, V>>().into()))
            },
            NodeType::Node256 => {
                ConcreteNodePtr::Node256(NodePtr(self.0.cast::<InnerNode256<K, V>>().into()))
            },
            NodeType::Leaf => {
                ConcreteNodePtr::LeafNode(NodePtr(self.0.cast::<LeafNode<K, V>>().into()))
            },
        }
    }

    /// Retrieve the runtime node type information.
    pub fn node_type(self) -> NodeType {
        // PANIC SAFETY: We know that we can convert the usize into a `NodeType` because
        // we have only stored `NodeType` values into this pointer
        NodeType::from_u8(self.0.to_data() as u8)
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
    pub(crate) unsafe fn header_mut<'h>(self) -> Option<&'h mut Header> {
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

    pub(crate) unsafe fn header_mut_uncheked<'h>(self) -> &'h mut Header {
        unsafe { &mut *self.0.cast::<Header>().to_ptr() }
    }

    pub fn deep_clone(&self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        match self.to_node_ptr() {
            ConcreteNodePtr::Node4(inner) => unsafe {
                NodePtr::allocate_node_ptr(inner.as_ref().deep_clone()).to_opaque()
            },
            ConcreteNodePtr::Node16(inner) => unsafe {
                NodePtr::allocate_node_ptr(inner.as_ref().deep_clone()).to_opaque()
            },
            ConcreteNodePtr::Node48(inner) => unsafe {
                NodePtr::allocate_node_ptr(inner.as_ref().deep_clone()).to_opaque()
            },
            ConcreteNodePtr::Node256(inner) => unsafe {
                NodePtr::allocate_node_ptr(inner.as_ref().deep_clone()).to_opaque()
            },
            ConcreteNodePtr::LeafNode(inner) => unsafe {
                NodePtr::allocate_node_ptr(inner.as_ref().clone()).to_opaque()
            },
        }
    }
}

/// An enum that encapsulates pointers to every type of Node
pub enum ConcreteNodePtr<K: AsBytes, V> {
    /// Node that references between 2 and 4 children
    Node4(NodePtr<InnerNode4<K, V>>),
    /// Node that references between 5 and 16 children
    Node16(NodePtr<InnerNode16<K, V>>),
    /// Node that references between 17 and 49 children
    Node48(NodePtr<InnerNode48<K, V>>),
    /// Node that references between 49 and 256 children
    Node256(NodePtr<InnerNode256<K, V>>),
    /// Node that contains a single value
    LeafNode(NodePtr<LeafNode<K, V>>),
}

impl<K: AsBytes, V> fmt::Debug for ConcreteNodePtr<K, V> {
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
pub struct NodePtr<N: Node>(NonNull<N>);

impl<N: Node> NodePtr<N> {
    /// Create a safe pointer to a [`Node`].
    ///
    /// # Safety
    ///
    /// Given pointer must be non-null, aligned, and valid for reads or writes
    /// of a value of N type.
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
    ///
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
    pub fn to_opaque(self) -> OpaqueNodePtr<N::Key, N::Value> {
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
}

impl<K: AsBytes, V> NodePtr<LeafNode<K, V>> {
    /// Returns a shared reference to the key and value of the pointed to
    /// [`LeafNode`].
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get mutated
    ///    (except inside UnsafeCell).
    pub unsafe fn as_key_value_ref<'a>(self) -> (&'a K, &'a V) {
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
    pub unsafe fn as_key_ref_value_mut<'a>(self) -> (&'a K, &'a mut V) {
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
    {
        // SAFETY: Safety requirements are covered by the containing function.
        let leaf = unsafe { self.as_mut() };

        leaf.value_mut()
    }
}

impl<N: Node> Clone for NodePtr<N> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<N: Node> Copy for NodePtr<N> {}

impl<N: Node> From<&mut N> for NodePtr<N> {
    fn from(node_ref: &mut N) -> Self {
        // SAFETY: Pointer is non-null, aligned, and pointing to a valid instance of N
        // because it was constructed from a mutable reference.
        unsafe { NodePtr::new(node_ref as *mut _) }
    }
}

impl<N: Node> PartialEq for NodePtr<N> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<N: Node> Eq for NodePtr<N> {}

impl<N: Node> fmt::Debug for NodePtr<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("NodePtr").field(&self.0).finish()
    }
}

impl<N: Node> fmt::Pointer for NodePtr<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

pub(crate) mod private {
    use crate::AsBytes;

    /// This trait is used to seal other traits, such that they cannot be
    /// implemented outside of the crate.
    pub trait Sealed {}

    impl<K: AsBytes, V> Sealed for super::InnerNode4<K, V> {}
    impl<K: AsBytes, V> Sealed for super::InnerNode16<K, V> {}
    impl<K: AsBytes, V> Sealed for super::InnerNode48<K, V> {}
    impl<K: AsBytes, V> Sealed for super::InnerNode256<K, V> {}
    impl<K: AsBytes, V> Sealed for super::LeafNode<K, V> {}
}

/// All nodes which contain a runtime tag that validates their type.
pub trait Node: private::Sealed {
    /// The runtime type of the node.
    const TYPE: NodeType;

    /// The key type carried by the leafe nodes
    type Key: AsBytes;

    /// The value type carried by the leaf nodes
    type Value;
}

#[derive(Debug)]
pub enum MatchPrefix<K: AsBytes, V> {
    Mismatch { mismatch: Mismatch<K, V> },
    Match { matched_bytes: usize },
}

#[derive(Debug)]
pub struct Mismatch<K: AsBytes, V> {
    pub matched_bytes: usize,
    pub prefix_byte: u8,
    pub leaf_ptr: Option<NodePtr<LeafNode<K, V>>>,
}

/// Common methods implemented by all inner node.
pub trait InnerNode: Node + Sized {
    /// The type of the next larger node type.
    type GrownNode: InnerNode<Key = <Self as Node>::Key, Value = <Self as Node>::Value>;

    /// The type of the next smaller node type.
    type ShrunkNode: InnerNode<Key = <Self as Node>::Key, Value = <Self as Node>::Value>;

    /// The type of the iterator over all children of the inner node
    type Iter<'a>: Iterator<
            Item = (
                u8,
                OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
            ),
        > + DoubleEndedIterator
        + FusedIterator
    where
        Self: 'a;

    fn empty() -> Self {
        Self::from_header(Header::empty())
    }

    fn from_prefix(prefix: &[u8], prefix_len: usize) -> Self {
        Self::from_header(Header::new(prefix, prefix_len))
    }

    fn from_header(header: Header) -> Self;

    fn header(&self) -> &Header;

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    fn lookup_child(
        &self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>>;

    /// Write a child pointer with key fragment to this inner node.
    ///
    /// If the key fragment already exists in the node, overwrite the existing
    /// child pointer.
    ///
    /// # Panics
    ///
    /// Panics when the node is full.
    fn write_child(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    );

    /// Attempt to remove a child pointer at the key fragment from this inner
    /// node.
    ///
    /// If the key fragment does not exist in this node, return `None`.
    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>>;

    /// Grow this node into the next larger class, copying over children and
    /// prefix information.
    fn grow(&self) -> Self::GrownNode;

    /// Shrink this node into the next smaller class, copying over children and
    /// prefix information.
    ///
    /// # Panics
    ///
    /// Panics if the new, smaller node size does not have enough capacity to
    /// hold all the children.
    fn shrink(&self) -> Self::ShrunkNode;

    /// Returns true if this node has no more space to store children.
    fn is_full(&self) -> bool {
        self.header().num_children() >= Self::TYPE.upper_capacity()
    }

    /// Create an iterator over all (key bytes, child pointers) in this inner
    /// node.
    ///
    /// # Safety
    ///
    /// The iterator type does not carry any lifetime, so the caller of this
    /// function must enforce that the lifetime of the iterator does not overlap
    /// with any mutating operations on the node.
    fn iter<'a>(&'a self) -> Self::Iter<'a>;

    /// Compares the compressed path of a node with the key and returns the
    /// number of equal bytes.
    ///
    /// # Panics
    ///
    /// `current_depth` > key len
    #[inline(always)]
    fn match_prefix(
        &self,
        key: &[u8],
        current_depth: usize,
    ) -> MatchPrefix<<Self as Node>::Key, <Self as Node>::Value> {
        unsafe {
            // SAFETY: Since we are iterating the key and prefixes, we
            // expect that the depth never exceeds the key len.
            // Because if this happens we ran out of bytes in the key to match
            // and the whole process should be already finished
            assume(current_depth <= key.len());
        }
        let (prefix, leaf_ptr) = self.read_full_prefix(current_depth);
        let key = &key[current_depth..];

        let matched_bytes = prefix
            .iter()
            .zip(key)
            .take_while(|(a, b)| **a == **b)
            .count();
        if matched_bytes < prefix.len() {
            MatchPrefix::Mismatch {
                mismatch: Mismatch {
                    matched_bytes,
                    prefix_byte: prefix[matched_bytes],
                    leaf_ptr,
                },
            }
        } else {
            MatchPrefix::Match { matched_bytes }
        }
    }

    #[inline(always)]
    fn read_full_prefix(
        &self,
        current_depth: usize,
    ) -> (
        &[u8],
        Option<NodePtr<LeafNode<<Self as Node>::Key, <Self as Node>::Value>>>,
    ) {
        let header = self.header();
        let len = header.prefix_len();
        if likely(len <= NUM_PREFIX_BYTES) {
            (header.read_prefix(), None)
        } else {
            // SAFETY: By construction a InnerNode, must have >= 1 childs, this
            // is even more strict since in the case of 1 child the node can be
            // collapsed, so a InnserNode must have >= 2 childs, so it's safe
            // to search for the minium. And the same applies to the `minimum_unchecked`
            // function
            let (_, min_child) = self.min();
            let leaf_ptr = unsafe { minimum_unchecked(min_child) };
            let leaf = unsafe { leaf_ptr.as_ref() };
            let leaf = leaf.key_ref().as_bytes();
            unsafe {
                // SAFETY: Since we are iterating the key and prefixes, we
                // expect that the depth never exceeds the key len.
                // Because if this happens we ran out of bytes in the key to match
                // and the whole process should be already finished
                assume(current_depth <= leaf.len());

                // SAFETY: By the construction of the prefix we know that this is inbounds
                // since the prefix len guarantees it to us
                assume(current_depth + len <= leaf.len());

                // SAFETY: This can't overflow since len comes from a u32
                assume(current_depth <= current_depth + len);
            }
            let leaf = &leaf[current_depth..(current_depth + len)];
            (leaf, Some(leaf_ptr))
        }
    }

    /// Returns the minimum child pointer from this node and it's key
    ///
    /// # Safety
    ///
    /// Since this is a [`InnerNode`] we assume that the we hava at least one
    /// child, (more strictly we have 2, because with one child the node
    /// would have collapsed) so in this way we can avoid the [`Option`].
    /// This is safe because if we had, no childs this current node should
    /// have been deleted.
    fn min(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    );

    /// Returns the maximum child pointer from this node and it's key
    ///
    /// # Safety
    ///
    /// Since this is a [`InnerNode`] we assume that the we hava at least one
    /// child, (more strictly we have 2, because with one child the node
    /// would have collapsed) so in this way we can avoid the [`Option`].
    /// This is safe because if we had, no childs this current node should
    /// have been deleted.
    fn max(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    );

    fn deep_clone(&self) -> Self
    where
        <Self as Node>::Key: Clone,
        <Self as Node>::Value: Clone;
}

enum WritePoint {
    Existing(usize),
    Last(usize),
    Shift(usize),
}

trait SearchInnerNodeCompressed {
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize>;
    fn find_write_point(&self, key_fragment: u8) -> WritePoint;
}

/// Node type that has a compact representation for key bytes and children
/// pointers.
#[repr(C, align(8))]
pub struct InnerNodeCompressed<K: AsBytes, V, const SIZE: usize> {
    /// The common node fields.
    pub header: Header,
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
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<K, V>>; SIZE],
}

impl<K: AsBytes, V, const SIZE: usize> Clone for InnerNodeCompressed<K, V, SIZE> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            keys: self.keys,
            child_pointers: self.child_pointers,
        }
    }
}

impl<K: AsBytes, V, const SIZE: usize> fmt::Debug for InnerNodeCompressed<K, V, SIZE> {
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

pub type InnerNodeCompressedIter<'a, K, V> =
    Zip<Copied<Iter<'a, u8>>, Copied<Iter<'a, OpaqueNodePtr<K, V>>>>;
impl<K: AsBytes, V, const SIZE: usize> InnerNodeCompressed<K, V, SIZE> {
    /// Return the initialized portions of the keys and child pointer arrays.
    pub fn initialized_portion(&self) -> (&[u8], &[OpaqueNodePtr<K, V>]) {
        // SAFETY: The array prefix with length `header.num_children` is guaranteed to
        // be initialized
        unsafe {
            let num_children = self.header.num_children();
            assume(num_children <= self.keys.len());
            (
                MaybeUninit::slice_assume_init_ref(self.keys.get_unchecked(0..num_children)),
                MaybeUninit::slice_assume_init_ref(
                    self.child_pointers.get_unchecked(0..num_children),
                ),
            )
        }
    }

    fn lookup_child_inner(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V>>
    where
        Self: SearchInnerNodeCompressed,
    {
        let idx = self.lookup_child_index(key_fragment)?;
        unsafe {
            // SAFETY: If `idx` is out of bounds the node should already have grown
            // so it's safe to assume that `idx` is in bounds
            assume(idx < self.child_pointers.len());

            // SAFETY: The value at `child_index` is guaranteed to be initialized because
            // the `lookup_child_index` function will only search in the initialized portion
            // of the `child_pointers` array.
            Some(MaybeUninit::assume_init(self.child_pointers[idx]))
        }
    }

    /// Writes a child to the node by check the order of insertion
    ///
    /// # Panics
    ///
    /// This functions assumes that the write is gonna be inbound
    /// (i.e the check for a full node is done previously to the call of this
    /// function)
    fn write_child_inner(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V>)
    where
        Self: SearchInnerNodeCompressed,
    {
        let num_children = self.header.num_children();
        let idx = match self.find_write_point(key_fragment) {
            WritePoint::Existing(child_index) => child_index,
            WritePoint::Last(child_index) => {
                self.header.num_children += 1;
                child_index
            },
            WritePoint::Shift(child_index) => {
                unsafe {
                    // SAFETY: This is by construction, since the number of children
                    // is always <= maximum number o keys (childrens) that we can hold
                    assume(num_children <= self.keys.len());

                    // SAFETY: When we are shifting children, because a new minimum one
                    // is being inserted this guarantees to us that the index of insertion
                    // is < current number of children (because if it was >= we wouldn't
                    // need to shift the data)
                    assume(child_index < num_children);

                    // assume(child_index + 1 + (num_children - child_index) <=
                    // self.keys.len());
                }
                self.keys
                    .copy_within(child_index..num_children, child_index + 1);
                self.child_pointers
                    .copy_within(child_index..num_children, child_index + 1);
                self.header.num_children += 1;
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
    /// # Panics
    ///
    /// This functions assumes that the write is gonna be inbound
    /// (i.e the check for a full node is done previously to the call of this
    /// function)
    pub unsafe fn write_child_unchecked(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V>,
    ) {
        let idx = self.header.num_children as usize;
        unsafe { self.write_child_at(idx, key_fragment, child_pointer) };
        self.header.num_children += 1;
    }

    unsafe fn write_child_at(
        &mut self,
        idx: usize,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<K, V>,
    ) {
        unsafe {
            assume(idx < self.keys.len());
            self.keys.get_unchecked_mut(idx).write(key_fragment);
            self.child_pointers
                .get_unchecked_mut(idx)
                .write(child_pointer);
        }
    }

    fn remove_child_inner(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V>>
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

        self.header.num_children -= 1;
        // SAFETY: This child pointer value is initialized because we got it by
        // searching through the initialized keys and got the `Ok(index)` value.
        Some(unsafe { MaybeUninit::assume_init(child_ptr) })
    }

    fn change_block_size<const NEW_SIZE: usize>(&self) -> InnerNodeCompressed<K, V, NEW_SIZE> {
        debug_assert!(
            self.header.num_children() <= NEW_SIZE,
            "Cannot change InnerNodeCompressed<{}> to size {} when it has more than {} children. \
             Currently has [{}] children.",
            SIZE,
            NEW_SIZE,
            NEW_SIZE,
            self.header.num_children
        );

        let header = self.header.clone();
        let mut keys = [MaybeUninit::new(0); NEW_SIZE];
        let mut child_pointers = MaybeUninit::uninit_array();
        let num_children = header.num_children();

        unsafe {
            // SAFETY: By construction the number of children in the header
            // is kept in sync with the number of children written in the node
            // and if this number exceeds the maximum len the node should have
            // alredy grown. So we know for a fact that that num_children <= node len
            assume(num_children <= self.keys.len());
            assume(num_children <= self.child_pointers.len());

            // SAFETY: When calling this function the NEW_SIZE, should fit the nodes.
            // We only need to be careful when shrinking the node, since when growing
            // NEW_SIZE >= SIZE.
            // This function is only called in a shrink case when a node is removed from
            // a node and the new current size fits in the NEW_SIZE
            assume(num_children <= keys.len());
            assume(num_children <= child_pointers.len());
        }

        keys[..num_children].copy_from_slice(&self.keys[..num_children]);
        child_pointers[..num_children].copy_from_slice(&self.child_pointers[..num_children]);

        InnerNodeCompressed {
            header,
            keys,
            child_pointers,
        }
    }

    fn grow_node48(&self) -> InnerNode48<K, V> {
        let header = self.header.clone();
        let mut child_indices = [RestrictedNodeIndex::<48>::EMPTY; 256];
        let mut child_pointers = MaybeUninit::uninit_array();

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

        unsafe {
            // SAFETY: By construction the number of children in the header
            // is kept in sync with the number of children written in the node
            // and if this number exceeds the maximum len the node should have
            // alredy grown. So we know for a fact that that num_children <= node len
            assume(num_children <= self.child_pointers.len());

            // SAFETY: We know that the new size is >= old size, so this is safe
            assume(num_children <= child_pointers.len());
        }

        child_pointers[..num_children].copy_from_slice(&self.child_pointers[..num_children]);

        InnerNode48 {
            header,
            child_indices,
            child_pointers,
        }
    }

    fn inner_iter<'a>(&'a self) -> InnerNodeCompressedIter<'a, K, V> {
        let (keys, nodes) = self.initialized_portion();
        keys.iter().copied().zip(nodes.iter().copied())
    }

    fn inner_deep_clone(&self) -> Self
    where
        K: Clone,
        V: Clone,
        Self: InnerNode<Key = K, Value = V>,
    {
        let mut node = Self::from_header(self.header.clone());
        for (idx, (key_fragment, child_pointer)) in self.iter().enumerate() {
            let child_pointer = child_pointer.deep_clone();
            unsafe { node.write_child_at(idx, key_fragment, child_pointer) };
        }

        node
    }
}

/// Node that references between 2 and 4 children
pub type InnerNode4<K, V> = InnerNodeCompressed<K, V, 4>;

impl<K: AsBytes, V> SearchInnerNodeCompressed for InnerNode4<K, V> {
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

impl<K: AsBytes, V> Node for InnerNode4<K, V> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node4;
}

impl<K: AsBytes, V> InnerNode for InnerNode4<K, V> {
    type GrownNode = InnerNode16<<Self as Node>::Key, <Self as Node>::Value>;
    type Iter<'a> = InnerNodeCompressedIter<'a, K, V> where Self: 'a;
    type ShrunkNode = InnerNode4<<Self as Node>::Key, <Self as Node>::Value>;

    fn header(&self) -> &Header {
        &self.header
    }

    fn from_header(header: Header) -> Self {
        Self {
            header,
            child_pointers: MaybeUninit::uninit_array(),
            keys: MaybeUninit::uninit_array(),
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V>> {
        self.lookup_child_inner(key_fragment)
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V>) {
        self.write_child_inner(key_fragment, child_pointer)
    }

    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>> {
        self.remove_child_inner(key_fragment)
    }

    fn grow(&self) -> Self::GrownNode {
        self.change_block_size()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        panic!("unable to shrink a Node4, something went wrong!")
    }

    fn iter<'a>(&'a self) -> Self::Iter<'a> {
        self.inner_iter()
    }

    fn min(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    ) {
        let (keys, children) = self.initialized_portion();
        unsafe {
            (
                keys.first().copied().unwrap_unchecked(),
                children.first().copied().unwrap_unchecked(),
            )
        }
    }

    fn max(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    ) {
        let (keys, children) = self.initialized_portion();
        unsafe {
            (
                keys.last().copied().unwrap_unchecked(),
                children.last().copied().unwrap_unchecked(),
            )
        }
    }

    fn deep_clone(&self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        self.inner_deep_clone()
    }
}

/// Node that references between 5 and 16 children
pub type InnerNode16<K, V> = InnerNodeCompressed<K, V, 16>;

impl<K: AsBytes, V> SearchInnerNodeCompressed for InnerNode16<K, V> {
    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize> {
        let keys = unsafe { MaybeUninit::array_assume_init(self.keys) };
        let cmp = u8x16::splat(key_fragment)
            .simd_eq(u8x16::from_array(keys))
            .to_bitmask() as u32;
        let mask = (1u32 << self.header.num_children) - 1;
        let bitfield = cmp & mask;
        if bitfield != 0 {
            Some(bitfield.trailing_zeros() as usize)
        } else {
            None
        }
    }

    fn find_write_point(&self, key_fragment: u8) -> WritePoint {
        match self.lookup_child_index(key_fragment) {
            Some(child_index) => WritePoint::Existing(child_index),
            None => {
                let keys = unsafe { MaybeUninit::array_assume_init(self.keys) };
                let cmp = u8x16::splat(key_fragment)
                    .simd_lt(u8x16::from_array(keys))
                    .to_bitmask() as u32;
                let mask = (1u32 << self.header.num_children) - 1;
                let bitfield = cmp & mask;
                if bitfield != 0 {
                    WritePoint::Shift(bitfield.trailing_zeros() as usize)
                } else {
                    WritePoint::Last(self.header.num_children())
                }
            },
        }
    }
}

impl<K: AsBytes, V> Node for InnerNode16<K, V> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node16;
}

impl<K: AsBytes, V> InnerNode for InnerNode16<K, V> {
    type GrownNode = InnerNode48<<Self as Node>::Key, <Self as Node>::Value>;
    type Iter<'a> = InnerNodeCompressedIter<'a, K, V> where Self: 'a;
    type ShrunkNode = InnerNode4<<Self as Node>::Key, <Self as Node>::Value>;

    fn header(&self) -> &Header {
        &self.header
    }

    fn from_header(header: Header) -> Self {
        Self {
            header,
            child_pointers: MaybeUninit::uninit_array(),
            keys: [MaybeUninit::new(0); 16],
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V>> {
        self.lookup_child_inner(key_fragment)
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V>) {
        self.write_child_inner(key_fragment, child_pointer)
    }

    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>> {
        self.remove_child_inner(key_fragment)
    }

    fn grow(&self) -> Self::GrownNode {
        self.grow_node48()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        self.change_block_size()
    }

    fn iter<'a>(&'a self) -> Self::Iter<'a> {
        self.inner_iter()
    }

    fn min(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    ) {
        let (keys, children) = self.initialized_portion();
        unsafe {
            (
                keys.first().copied().unwrap_unchecked(),
                children.first().copied().unwrap_unchecked(),
            )
        }
    }

    fn max(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    ) {
        let (keys, children) = self.initialized_portion();
        unsafe {
            (
                keys.last().copied().unwrap_unchecked(),
                children.last().copied().unwrap_unchecked(),
            )
        }
    }

    fn deep_clone(&self) -> Self
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
pub struct InnerNode48<K: AsBytes, V> {
    /// The common node fields.
    pub header: Header,
    /// An array that maps key bytes (as the index) to the index value in the
    /// `child_pointers` array.
    ///
    /// All the `child_indices` values are guaranteed to be
    /// `PartialNodeIndex<48>::EMPTY` when the node is constructed.
    pub child_indices: [RestrictedNodeIndex<48>; 256],
    /// For each element in this array, it is assumed to be initialized if there
    /// is a index in the `child_indices` array that points to it
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<K, V>>; 48],
}

impl<K: AsBytes, V> fmt::Debug for InnerNode48<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode48")
            .field("header", &self.header)
            .field("child_indices", &self.child_indices)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<K: AsBytes, V> Clone for InnerNode48<K, V> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_indices: self.child_indices,
            child_pointers: self.child_pointers,
        }
    }
}

impl<K: AsBytes, V> InnerNode48<K, V> {
    /// Return the initialized portions of the child pointer array.
    pub fn initialized_child_pointers(&self) -> &[OpaqueNodePtr<K, V>] {
        unsafe {
            // SAFETY: The array prefix with length `header.num_children` is guaranteed to
            // be initialized
            assume(self.header.num_children() <= self.child_pointers.len());
            MaybeUninit::slice_assume_init_ref(&self.child_pointers[..self.header.num_children()])
        }
    }
}

impl<K: AsBytes, V> Node for InnerNode48<K, V> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node48;
}

impl<K: AsBytes, V> InnerNode for InnerNode48<K, V> {
    type GrownNode = InnerNode256<<Self as Node>::Key, <Self as Node>::Value>;
    type Iter<'a> = Map<FilterMap<Enumerate<Iter<'a, RestrictedNodeIndex<48>>>, impl FnMut((usize, &'a RestrictedNodeIndex<48>)) -> Option<(u8, usize)>>, impl FnMut((u8, usize)) -> (u8, OpaqueNodePtr<K, V>)> where Self: 'a;
    type ShrunkNode = InnerNode16<<Self as Node>::Key, <Self as Node>::Value>;

    fn header(&self) -> &Header {
        &self.header
    }

    fn from_header(header: Header) -> Self {
        InnerNode48 {
            header,
            child_indices: [RestrictedNodeIndex::<48>::EMPTY; 256],
            child_pointers: MaybeUninit::uninit_array(),
        }
    }

    fn lookup_child(
        &self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>> {
        let index = &self.child_indices[usize::from(key_fragment)];
        let child_pointers = self.initialized_child_pointers();
        if !index.is_empty() {
            let idx = usize::from(*index);
            unsafe {
                // SAFETY: If `idx` is out of bounds we have more than
                // 48 childs in this node, so it should have already
                // grown. So it's safe to assume that it's in bounds
                assume(idx < child_pointers.len());
            }
            Some(child_pointers[idx])
        } else {
            None
        }
    }

    fn write_child(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
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
            self.header.num_children += 1;
            child_index
        } else {
            // overwrite existing
            usize::from(self.child_indices[key_fragment_idx])
        };

        // SAFETY: This index can be up to <= 47 as decribed above
        unsafe {
            assume(child_index < self.child_pointers.len());
        }
        self.child_pointers[child_index].write(child_pointer);
    }

    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>> {
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
        self.header.num_children -= 1;
        // SAFETY: This child pointer value is initialized because we got it by using a
        // non-`RestrictedNodeIndex::<>::EMPTY` index from the child indices array.
        Some(unsafe { MaybeUninit::assume_init(child_ptr) })
    }

    fn grow(&self) -> Self::GrownNode {
        let header = self.header.clone();
        let mut child_pointers = [None; 256];
        // SAFETY: This iterator lives only for the lifetime of this function, which
        // does not mutate the `InnerNode48` (guaranteed by reference).
        // let iter = unsafe { InnerNode48Iter::new(self) };

        let initialized_child_pointers = self.initialized_child_pointers();
        for (key_fragment, idx) in self.child_indices.iter().enumerate() {
            if idx.is_empty() {
                continue;
            }

            let idx = usize::from(*idx);
            unsafe {
                // SAFETY: When growing initialized_child_pointers should be full
                // i.e initialized_child_pointers len == 48. And idx <= 47, since
                // we can't insert in a full, node
                assume(idx < initialized_child_pointers.len());
            }
            let child_pointer = initialized_child_pointers[idx];
            child_pointers[usize::from(key_fragment)] = Some(child_pointer);
        }

        InnerNode256 {
            header,
            child_pointers,
        }
    }

    fn shrink(&self) -> Self::ShrunkNode {
        debug_assert!(
            self.header.num_children <= 16,
            "Cannot shrink a Node48 when it has more than 16 children. Currently has [{}] \
             children.",
            self.header.num_children
        );

        let header = self.header.clone();

        let mut key_and_child_ptrs = MaybeUninit::uninit_array::<16>();

        for (idx, value) in self.iter().enumerate() {
            key_and_child_ptrs[idx].write(value);
        }

        let init_key_and_child_ptrs = {
            // SAFETY: The first `num_children` are guaranteed to be initialized in this
            // array because the previous iterator loops through all children of the inner
            // node.
            let init_key_and_child_ptrs = unsafe {
                MaybeUninit::slice_assume_init_mut(&mut key_and_child_ptrs[..header.num_children()])
            };

            init_key_and_child_ptrs.sort_unstable_by_key(|(key_byte, _)| *key_byte);

            init_key_and_child_ptrs
        };

        let mut keys = MaybeUninit::uninit_array();
        let mut child_pointers = MaybeUninit::uninit_array();

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

    fn iter<'a>(&'a self) -> Self::Iter<'a> {
        let child_pointers = self.initialized_child_pointers();
        self.child_indices
            .iter()
            .enumerate()
            .filter_map(|(key, idx)| (!idx.is_empty()).then_some((key as u8, usize::from(*idx))))
            .map(|(key, idx)| unsafe { (key, *child_pointers.get_unchecked(idx)) })
    }

    fn min(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    ) {
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
            assume(key < self.child_indices.len());
        }

        let idx = usize::from(self.child_indices[key]);
        let child_pointers = self.initialized_child_pointers();

        unsafe {
            // SAFETY: We know that idx is in bounds, because the value can't be
            // constructed if it >= 48 and also it has to be < num children, since
            // it's constructed from the num children before being incremented during
            // insertion process
            assume(idx < child_pointers.len());
        }

        (key as u8, child_pointers[idx])
    }

    fn max(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    ) {
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
            assume(key < self.child_indices.len());
        }

        let idx = usize::from(self.child_indices[key]);
        let child_pointers = self.initialized_child_pointers();

        unsafe {
            // SAFETY: We know that idx is in bounds, because the value can't be
            // constructed if it >= 48 and also it has to be < num children, since
            // it's constructed from the num children before being incremented during
            // insertion process
            assume(idx < child_pointers.len());
        }

        (key as u8, child_pointers[idx])
    }

    fn deep_clone(&self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        let mut node = Self::from_header(self.header.clone());
        for (idx, (key_fragment, child_pointer)) in self.iter().enumerate() {
            let child_pointer = child_pointer.deep_clone();
            node.child_indices[usize::from(key_fragment)] =
                unsafe { RestrictedNodeIndex::try_from(idx).unwrap_unchecked() };
            unsafe {
                assume(idx < node.child_pointers.len());
            }
            node.child_pointers[idx].write(child_pointer);
        }

        node
    }
}

/// Node that references between 49 and 256 children
#[repr(C, align(8))]
pub struct InnerNode256<K: AsBytes, V> {
    /// The common node fields.
    pub header: Header,
    /// An array that directly maps a key byte (as index) to a child node.
    pub child_pointers: [Option<OpaqueNodePtr<K, V>>; 256],
}

impl<K: AsBytes, V> fmt::Debug for InnerNode256<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode256")
            .field("header", &self.header)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<K: AsBytes, V> Clone for InnerNode256<K, V> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_pointers: self.child_pointers,
        }
    }
}

impl<K: AsBytes, V> Node for InnerNode256<K, V> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node256;
}

impl<K: AsBytes, V> InnerNode for InnerNode256<K, V> {
    type GrownNode = Self;
    type Iter<'a> = FilterMap<Enumerate<Iter<'a, Option<OpaqueNodePtr<K, V>>>>, impl FnMut((usize, &'a Option<OpaqueNodePtr<K, V>>)) -> Option<(u8, OpaqueNodePtr<K, V>)>> where Self: 'a;
    type ShrunkNode = InnerNode48<K, V>;

    fn header(&self) -> &Header {
        &self.header
    }

    fn from_header(header: Header) -> Self {
        InnerNode256 {
            header,
            child_pointers: [None; 256],
        }
    }

    fn lookup_child(
        &self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>> {
        self.child_pointers[usize::from(key_fragment)]
    }

    fn write_child(
        &mut self,
        key_fragment: u8,
        child_pointer: OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    ) {
        let key_fragment_idx = usize::from(key_fragment);
        let existing_pointer = self.child_pointers[key_fragment_idx];
        self.child_pointers[key_fragment_idx] = Some(child_pointer);
        if existing_pointer.is_none() {
            self.header.num_children += 1;
        }
    }

    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>> {
        let removed_child = self.child_pointers[usize::from(key_fragment)].take();

        if removed_child.is_some() {
            self.header.num_children -= 1;
        }

        removed_child
    }

    fn grow(&self) -> Self::GrownNode {
        panic!("unable to grow a Node256, something went wrong!")
    }

    fn shrink(&self) -> Self::ShrunkNode {
        debug_assert!(
            self.header.num_children <= 48,
            "Cannot shrink a Node256 when it has more than 48 children. Currently has [{}] \
             children.",
            self.header.num_children
        );

        let header = self.header.clone();
        let mut child_indices = [RestrictedNodeIndex::<48>::EMPTY; 256];
        let mut child_pointers = MaybeUninit::uninit_array();

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

    fn iter<'a>(&'a self) -> Self::Iter<'a> {
        self.child_pointers
            .iter()
            .enumerate()
            .filter_map(|(key, node)| node.map(|node| (key as u8, node)))
    }

    fn min(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    ) {
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
            assume(key < self.child_pointers.len());
        }

        (key as u8, unsafe {
            self.child_pointers[key].unwrap_unchecked()
        })
    }

    fn max(
        &self,
    ) -> (
        u8,
        OpaqueNodePtr<<Self as Node>::Key, <Self as Node>::Value>,
    ) {
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
            assume(key < self.child_pointers.len());
        }

        (key as u8, unsafe {
            self.child_pointers[key].unwrap_unchecked()
        })
    }

    fn deep_clone(&self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        let mut node = Self::from_header(self.header.clone());
        for (key_fragment, child_pointer) in self.iter() {
            node.child_pointers[usize::from(key_fragment)] = Some(child_pointer.deep_clone());
        }

        node
    }
}

/// Node that contains a single leaf value.
#[derive(Debug, Clone)]
#[repr(align(8))]
pub struct LeafNode<K, V> {
    /// The leaf value.
    value: V,
    /// The full key that the `value` was stored with.
    key: K,
}

impl<K, V> LeafNode<K, V> {
    /// Create a new leaf node with the given value.
    pub fn new(key: K, value: V) -> Self {
        LeafNode { value, key }
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

impl<K: AsBytes, V> Node for LeafNode<K, V> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Leaf;
}
