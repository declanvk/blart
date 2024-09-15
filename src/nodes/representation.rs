//! Trie node representation

use crate::{rust_nightly_apis::assume, tagged_pointer::TaggedPointer, AsBytes};
use std::{
    fmt,
    hash::Hash,
    iter::FusedIterator,
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ops::{Range, RangeBounds},
    ptr::{self, NonNull},
};

mod header;
pub(crate) use header::*;

mod inner_node_256;
pub use inner_node_256::*;

mod inner_node_48;
pub use inner_node_48::*;

mod inner_node_compressed;
pub use inner_node_compressed::*;

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
pub struct OpaqueNodePtr<K, V, const PREFIX_LEN: usize>(
    TaggedPointer<OpaqueValue, 3>,
    PhantomData<(K, V)>,
);

impl<K, V, const PREFIX_LEN: usize> Copy for OpaqueNodePtr<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> Clone for OpaqueNodePtr<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for OpaqueNodePtr<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("OpaqueNodePtr").field(&self.0).finish()
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Pointer for OpaqueNodePtr<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

impl<K, V, const PREFIX_LEN: usize> Eq for OpaqueNodePtr<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> PartialEq for OpaqueNodePtr<K, V, PREFIX_LEN> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K, V, const PREFIX_LEN: usize> Hash for OpaqueNodePtr<K, V, PREFIX_LEN> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<K, V, const PREFIX_LEN: usize> OpaqueNodePtr<K, V, PREFIX_LEN> {
    /// Construct a new opaque node pointer from an existing non-null node
    /// pointer.
    pub fn new<N>(pointer: NonNull<N>) -> Self
    where
        N: Node<PREFIX_LEN, Value = V>,
    {
        let mut tagged_ptr = TaggedPointer::from(pointer).cast::<OpaqueValue>();
        tagged_ptr.set_data(N::TYPE as usize);

        OpaqueNodePtr(tagged_ptr, PhantomData)
    }

    /// Return `true` if this Node_ pointer points to the specified concrete
    /// [`NodeType`].
    pub fn is<N: Node<PREFIX_LEN>>(&self) -> bool {
        self.0.to_data() == usize::from(N::TYPE as u8)
    }

    /// Create a non-opaque node pointer that will eliminate future type
    /// assertions, if the type of the pointed node matches the given
    /// node type.
    pub fn cast<N: Node<PREFIX_LEN>>(self) -> Option<NodePtr<PREFIX_LEN, N>> {
        if self.is::<N>() {
            Some(NodePtr(self.0.cast::<N>().into()))
        } else {
            None
        }
    }

    /// Cast this opaque pointer type an enum that contains a pointer to the
    /// concrete node type.
    pub fn to_node_ptr(self) -> ConcreteNodePtr<K, V, PREFIX_LEN> {
        match self.node_type() {
            NodeType::Node4 => ConcreteNodePtr::Node4(NodePtr(
                self.0.cast::<InnerNode4<K, V, PREFIX_LEN>>().into(),
            )),
            NodeType::Node16 => ConcreteNodePtr::Node16(NodePtr(
                self.0.cast::<InnerNode16<K, V, PREFIX_LEN>>().into(),
            )),
            NodeType::Node48 => ConcreteNodePtr::Node48(NodePtr(
                self.0.cast::<InnerNode48<K, V, PREFIX_LEN>>().into(),
            )),
            NodeType::Node256 => ConcreteNodePtr::Node256(NodePtr(
                self.0.cast::<InnerNode256<K, V, PREFIX_LEN>>().into(),
            )),
            NodeType::Leaf => ConcreteNodePtr::LeafNode(NodePtr(
                self.0.cast::<LeafNode<K, V, PREFIX_LEN>>().into(),
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
    pub(crate) unsafe fn header_mut<'h>(self) -> Option<&'h mut Header<PREFIX_LEN>> {
        let header_ptr = match self.node_type() {
            NodeType::Node4 | NodeType::Node16 | NodeType::Node48 | NodeType::Node256 => unsafe {
                self.header_mut_unchecked()
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
    pub(crate) unsafe fn header_mut_unchecked<'h>(self) -> &'h mut Header<PREFIX_LEN> {
        unsafe { &mut *self.0.cast::<Header<PREFIX_LEN>>().to_ptr() }
    }

    /// Get a shared reference to the header, this doesn't check if the pointer
    /// is to an inner node.
    ///
    /// # Safety
    ///  - The pointer must be to an inner node
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'h is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not be mutated
    ///    through any other pointer.
    pub(crate) unsafe fn header_ref_unchecked<'h>(self) -> &'h Header<PREFIX_LEN> {
        unsafe { &*self.0.cast::<Header<PREFIX_LEN>>().to_ptr() }
    }
}

/// An enum that encapsulates pointers to every type of [`Node`]
pub enum ConcreteNodePtr<K, V, const PREFIX_LEN: usize> {
    /// Node that references between 2 and 4 children
    Node4(NodePtr<PREFIX_LEN, InnerNode4<K, V, PREFIX_LEN>>),
    /// Node that references between 5 and 16 children
    Node16(NodePtr<PREFIX_LEN, InnerNode16<K, V, PREFIX_LEN>>),
    /// Node that references between 17 and 49 children
    Node48(NodePtr<PREFIX_LEN, InnerNode48<K, V, PREFIX_LEN>>),
    /// Node that references between 49 and 256 children
    Node256(NodePtr<PREFIX_LEN, InnerNode256<K, V, PREFIX_LEN>>),
    /// Node that contains a single value
    LeafNode(NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>),
}

impl<K, V, const PREFIX_LEN: usize> Copy for ConcreteNodePtr<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> Clone for ConcreteNodePtr<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PREFIX_LEN: usize> ConcreteNodePtr<K, V, PREFIX_LEN> {
    /// Convert this node pointer with node type information into an
    /// [`OpaqueNodePtr`] with the type information stored in the pointer.
    pub fn to_opaque(self) -> OpaqueNodePtr<K, V, PREFIX_LEN> {
        match self {
            ConcreteNodePtr::Node4(node_ptr) => node_ptr.to_opaque(),
            ConcreteNodePtr::Node16(node_ptr) => node_ptr.to_opaque(),
            ConcreteNodePtr::Node48(node_ptr) => node_ptr.to_opaque(),
            ConcreteNodePtr::Node256(node_ptr) => node_ptr.to_opaque(),
            ConcreteNodePtr::LeafNode(node_ptr) => node_ptr.to_opaque(),
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for ConcreteNodePtr<K, V, PREFIX_LEN> {
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

macro_rules! concrete_node_ptr_from {
    ($input:ty, $variant:ident) => {
        impl<K, V, const PREFIX_LEN: usize> From<$input> for ConcreteNodePtr<K, V, PREFIX_LEN> {
            fn from(value: $input) -> Self {
                ConcreteNodePtr::$variant(value)
            }
        }
    };
}

concrete_node_ptr_from!(NodePtr<PREFIX_LEN, InnerNode4<K, V, PREFIX_LEN>>, Node4);
concrete_node_ptr_from!(NodePtr<PREFIX_LEN, InnerNode16<K, V, PREFIX_LEN>>, Node16);
concrete_node_ptr_from!(NodePtr<PREFIX_LEN, InnerNode48<K, V, PREFIX_LEN>>, Node48);
concrete_node_ptr_from!(NodePtr<PREFIX_LEN, InnerNode256<K, V, PREFIX_LEN>>, Node256);
concrete_node_ptr_from!(NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>, LeafNode);

/// An enum that encapsulates pointers to every type of [`InnerNode`]
pub enum ConcreteInnerNodePtr<K, V, const PREFIX_LEN: usize> {
    /// Node that references between 2 and 4 children
    Node4(NodePtr<PREFIX_LEN, InnerNode4<K, V, PREFIX_LEN>>),
    /// Node that references between 5 and 16 children
    Node16(NodePtr<PREFIX_LEN, InnerNode16<K, V, PREFIX_LEN>>),
    /// Node that references between 17 and 49 children
    Node48(NodePtr<PREFIX_LEN, InnerNode48<K, V, PREFIX_LEN>>),
    /// Node that references between 49 and 256 children
    Node256(NodePtr<PREFIX_LEN, InnerNode256<K, V, PREFIX_LEN>>),
}

impl<K, V, const PREFIX_LEN: usize> Copy for ConcreteInnerNodePtr<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> Clone for ConcreteInnerNodePtr<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for ConcreteInnerNodePtr<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Node4(arg0) => f.debug_tuple("Node4").field(arg0).finish(),
            Self::Node16(arg0) => f.debug_tuple("Node16").field(arg0).finish(),
            Self::Node48(arg0) => f.debug_tuple("Node48").field(arg0).finish(),
            Self::Node256(arg0) => f.debug_tuple("Node256").field(arg0).finish(),
        }
    }
}

macro_rules! concrete_inner_node_ptr_from {
    ($input:ty, $variant:ident) => {
        impl<K, V, const PREFIX_LEN: usize> From<$input>
            for ConcreteInnerNodePtr<K, V, PREFIX_LEN>
        {
            fn from(value: $input) -> Self {
                Self::$variant(value)
            }
        }
    };
}

concrete_inner_node_ptr_from!(NodePtr<PREFIX_LEN, InnerNode4<K, V, PREFIX_LEN>>, Node4);
concrete_inner_node_ptr_from!(NodePtr<PREFIX_LEN, InnerNode16<K, V, PREFIX_LEN>>, Node16);
concrete_inner_node_ptr_from!(NodePtr<PREFIX_LEN, InnerNode48<K, V, PREFIX_LEN>>, Node48);
concrete_inner_node_ptr_from!(NodePtr<PREFIX_LEN, InnerNode256<K, V, PREFIX_LEN>>, Node256);

impl<K, V, const PREFIX_LEN: usize> From<ConcreteInnerNodePtr<K, V, PREFIX_LEN>>
    for ConcreteNodePtr<K, V, PREFIX_LEN>
{
    fn from(value: ConcreteInnerNodePtr<K, V, PREFIX_LEN>) -> Self {
        match value {
            ConcreteInnerNodePtr::Node4(inner_ptr) => ConcreteNodePtr::Node4(inner_ptr),
            ConcreteInnerNodePtr::Node16(inner_ptr) => ConcreteNodePtr::Node16(inner_ptr),
            ConcreteInnerNodePtr::Node48(inner_ptr) => ConcreteNodePtr::Node48(inner_ptr),
            ConcreteInnerNodePtr::Node256(inner_ptr) => ConcreteNodePtr::Node256(inner_ptr),
        }
    }
}

/// A pointer to a [`Node`].
#[repr(transparent)]
pub struct NodePtr<const PREFIX_LEN: usize, N>(NonNull<N>);

impl<const PREFIX_LEN: usize, N: Node<PREFIX_LEN>> NodePtr<PREFIX_LEN, N> {
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
        // SAFETY: Covered by safety condition on function
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
    pub fn to_opaque(self) -> OpaqueNodePtr<N::Key, N::Value, PREFIX_LEN> {
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

impl<K, V, const PREFIX_LEN: usize> NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>> {
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

impl<const PREFIX_LEN: usize, N> Clone for NodePtr<PREFIX_LEN, N> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<const PREFIX_LEN: usize, N> Copy for NodePtr<PREFIX_LEN, N> {}

impl<const PREFIX_LEN: usize, N: Node<PREFIX_LEN>> From<&mut N> for NodePtr<PREFIX_LEN, N> {
    fn from(node_ref: &mut N) -> Self {
        // SAFETY: Pointer is non-null, aligned, and pointing to a valid instance of N
        // because it was constructed from a mutable reference.
        unsafe { NodePtr::new(node_ref as *mut _) }
    }
}

impl<const PREFIX_LEN: usize, N> PartialEq for NodePtr<PREFIX_LEN, N> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<const PREFIX_LEN: usize, N> Eq for NodePtr<PREFIX_LEN, N> {}

impl<const PREFIX_LEN: usize, N> fmt::Debug for NodePtr<PREFIX_LEN, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("NodePtr").field(&self.0).finish()
    }
}

impl<const PREFIX_LEN: usize, N> fmt::Pointer for NodePtr<PREFIX_LEN, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

pub(crate) mod private {
    /// This trait is used to seal other traits, such that they cannot be
    /// implemented outside of the crate.
    pub trait Sealed {}

    impl<K, V, const PREFIX_LEN: usize> Sealed for super::InnerNode4<K, V, PREFIX_LEN> {}
    impl<K, V, const PREFIX_LEN: usize> Sealed for super::InnerNode16<K, V, PREFIX_LEN> {}
    impl<K, V, const PREFIX_LEN: usize> Sealed for super::InnerNode48<K, V, PREFIX_LEN> {}
    impl<K, V, const PREFIX_LEN: usize> Sealed for super::InnerNode256<K, V, PREFIX_LEN> {}
    impl<K, V, const PREFIX_LEN: usize> Sealed for super::LeafNode<K, V, PREFIX_LEN> {}
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

/// Result of prefix match
pub enum MatchPrefixResult<K, V, const PREFIX_LEN: usize> {
    /// If prefixes don't match
    Mismatch {
        /// Mismatch object
        mismatch: Mismatch<K, V, PREFIX_LEN>,
    },
    /// If the prefixes match entirely
    Match {
        /// How many bytes were matched
        matched_bytes: usize,
    },
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for MatchPrefixResult<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Mismatch { mismatch } => f
                .debug_struct("Mismatch")
                .field("mismatch", mismatch)
                .finish(),
            Self::Match { matched_bytes } => f
                .debug_struct("Match")
                .field("matched_bytes", matched_bytes)
                .finish(),
        }
    }
}

/// Represents a prefix mismatch
pub struct Mismatch<K, V, const PREFIX_LEN: usize> {
    /// How many bytes were matched
    pub matched_bytes: usize,
    /// Value of the byte that made it not match
    pub prefix_byte: u8,
    /// Pointer to the leaf if the prefix was reconstructed
    pub leaf_ptr: OptionalLeafPtr<K, V, PREFIX_LEN>,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for Mismatch<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Mismatch")
            .field("matched_bytes", &self.matched_bytes)
            .field("prefix_byte", &self.prefix_byte)
            .field("leaf_ptr", &self.leaf_ptr)
            .finish()
    }
}

/// Common methods implemented by all inner node.
pub trait InnerNode<const PREFIX_LEN: usize>: Node<PREFIX_LEN> + Sized + fmt::Debug {
    /// The type of the next larger node type.
    type GrownNode: InnerNode<PREFIX_LEN, Key = Self::Key, Value = Self::Value>;

    /// The type of the next smaller node type.
    type ShrunkNode: InnerNode<PREFIX_LEN, Key = Self::Key, Value = Self::Value>;

    /// The type of the iterator over all children of the inner node
    type Iter<'a>: Iterator<Item = (u8, OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>)>
        + DoubleEndedIterator
        + FusedIterator
    where
        Self: 'a;

    /// Create an empty [`InnerNode`], with no children and no prefix
    fn empty() -> Self {
        Self::from_header(Header::empty())
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
        Self::from_header(Header::new(prefix, prefix_len))
    }

    /// Create a new [`InnerNode`] using a `Header`
    fn from_header(header: Header<PREFIX_LEN>) -> Self;

    /// Get the `Header` from the [`InnerNode`]
    fn header(&self) -> &Header<PREFIX_LEN>;

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    fn lookup_child(
        &self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>>;

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
        child_pointer: OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>,
    );

    /// Attempt to remove a child pointer at the key fragment from this inner
    /// node.
    ///
    /// If the key fragment does not exist in this node, return `None`.
    fn remove_child(
        &mut self,
        key_fragment: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>>;

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

    /// Create an iterator over all `(key bytes, child pointers)` in this inner
    /// node.
    fn iter(&self) -> Self::Iter<'_>;

    /// Create an iterator over a subset of `(key bytes, child pointers)`, using
    /// the given `bound` as a restriction on the set of key bytes.
    fn range(
        &self,
        bound: impl RangeBounds<u8>,
    ) -> impl DoubleEndedIterator<Item = (u8, OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>)>
           + FusedIterator;

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
    ) -> MatchPrefixResult<Self::Key, Self::Value, PREFIX_LEN>
    where
        Self::Key: AsBytes,
    {
        // TODO: We could optimize the usage of this function by splitting it into two
        // cases:
        //  1. Where we read the full prefix, in cases of an insert when we need to
        //     determine where to split the prefix
        //  2. Where we read only the inline part of the prefix, in cases of a lookup
        //     where we can still check the final leaf key for equality at the end of
        //     the search
        // This would speed up the `lookup` case, since we wouldn't need to load the
        // full prefix for some of those cases.
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
        Option<NodePtr<PREFIX_LEN, LeafNode<Self::Key, Self::Value, PREFIX_LEN>>>,
    )
    where
        Self::Key: AsBytes,
    {
        self.header().inner_read_full_prefix(self, current_depth)
    }

    /// Returns the minimum child pointer from this node and it's key
    ///
    /// # Safety
    ///  - Since this is a [`InnerNode`] we assume that the we have at least one
    ///    child, (more strictly we have 2, because with one child the node
    ///    would have collapsed) so in this way we can avoid the [`Option`].
    ///    This is safe because if we had no children this current node should
    ///    have been deleted.
    fn min(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>);

    /// Returns the maximum child pointer from this node and it's key
    ///
    /// # Safety
    ///  - Since this is a [`InnerNode`] we assume that the we have at least one
    ///    child, (more strictly we have 2, because with one child the node
    ///    would have collapsed) so in this way we can avoid the [`Option`].
    ///    This is safe because if we had, no children this current node should
    ///    have been deleted.
    fn max(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PREFIX_LEN>);
}

/// This type alias represents an optional pointer to a leaf node.
pub(crate) type OptionalLeafPtr<K, V, const PREFIX_LEN: usize> =
    Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>>;

/// Node that contains a single leaf value.
#[derive(Debug)]
#[repr(align(8))]
pub struct LeafNode<K, V, const PREFIX_LEN: usize> {
    /// The leaf value.
    value: V,
    /// The full key that the `value` was stored with.
    key: K,

    /// Pointer to the previous leaf node in the trie. If the value is `None`,
    /// then this is the first leaf.
    pub(crate) previous: OptionalLeafPtr<K, V, PREFIX_LEN>,

    /// Pointer to the next leaf node in the trie. If the value is `None`,
    /// then this is the last leaf.
    pub(crate) next: OptionalLeafPtr<K, V, PREFIX_LEN>,
}

impl<K, V, const PREFIX_LEN: usize> LeafNode<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    /// Insert the leaf node pointed to by `this_ptr` into the linked list that
    /// `previous_sibling_ptr` belongs to, placing the "this" leaf node after
    /// the "previous sibling" in the list.
    ///
    /// # Safety
    ///
    /// This function requires that no other operation is concurrently modifying
    /// or reading the `this_ptr` leaf node, the `previous_sibling_ptr` leaf
    /// node, and the sibling leaf node of `previous_sibling_ptr`.
    pub unsafe fn insert_after(
        this_ptr: NodePtr<PREFIX_LEN, Self>,
        previous_sibling_ptr: NodePtr<PREFIX_LEN, Self>,
    ) {
        // SAFETY: Covered by safety doc of this function
        let (this, previous_sibling) =
            unsafe { (this_ptr.as_mut(), previous_sibling_ptr.as_mut()) };

        if cfg!(debug_assertions) {
            debug_assert!(
                this.previous.is_none(),
                "previous ptr should be None on insert into linked list"
            );
            debug_assert!(
                this.next.is_none(),
                "next ptr should be None on insert into linked list"
            );
            debug_assert!(
                previous_sibling.key.as_bytes() < this.key.as_bytes(),
                "sibling must be ordered before this leaf in the trie"
            );
        }

        this.previous = Some(previous_sibling_ptr);
        this.next = previous_sibling.next;

        if let Some(next_sibling_ptr) = previous_sibling.next {
            // SAFETY: Covered by safety doc of this function
            let next_sibling = unsafe { next_sibling_ptr.as_mut() };
            next_sibling.previous = Some(this_ptr);
        }
        previous_sibling.next = Some(this_ptr);
    }

    /// Insert the leaf node pointed to by `this_ptr` into the linked list that
    /// `next_sibling_ptr` belongs to, placing the "this" leaf node before
    /// the "next sibling" in the list.
    ///
    /// # Safety
    ///
    /// This function requires that no other operation is concurrently modifying
    /// or reading the `this_ptr` leaf node, the `next_sibling_ptr` leaf
    /// node, and the sibling leaf node of `next_sibling_ptr`.
    pub unsafe fn insert_before(
        this_ptr: NodePtr<PREFIX_LEN, Self>,
        next_sibling_ptr: NodePtr<PREFIX_LEN, Self>,
    ) {
        // SAFETY: Covered by safety doc of this function
        let (this, next_sibling) = unsafe { (this_ptr.as_mut(), next_sibling_ptr.as_mut()) };

        if cfg!(debug_assertions) {
            debug_assert!(
                this.previous.is_none(),
                "previous ptr should be None on insert into linked list"
            );
            debug_assert!(
                this.next.is_none(),
                "next ptr should be None on insert into linked list"
            );
            debug_assert!(
                this.key.as_bytes() < next_sibling.key.as_bytes(),
                "this leaf must be ordered before sibling in the trie"
            );
        }

        this.previous = next_sibling.previous;
        this.next = Some(next_sibling_ptr);

        if let Some(previous_sibling_ptr) = next_sibling.previous {
            // SAFETY: Covered by safety doc of this function
            let previous_sibling = unsafe { previous_sibling_ptr.as_mut() };
            previous_sibling.next = Some(this_ptr);
        }
        next_sibling.previous = Some(this_ptr);
    }

    /// Insert the leaf node pointed to by `this_ptr` into the linked list
    /// position that `old_leaf` currently occupies, and then remove `old_leaf`
    /// from the linked list.
    ///
    /// # Safety
    ///
    /// This function requires that no other operation is concurrently modifying
    /// or reading the `this_ptr` leaf node and the sibling leaf nodes of the
    /// `old_leaf`.
    pub unsafe fn replace(this_ptr: NodePtr<PREFIX_LEN, Self>, old_leaf: &mut Self) {
        // SAFETY: Covered by safety doc of this function
        let this = unsafe { this_ptr.as_mut() };

        if cfg!(debug_assertions) {
            debug_assert!(
                this.previous.is_none(),
                "previous ptr should be None on insert into linked list"
            );
            debug_assert!(
                this.next.is_none(),
                "next ptr should be None on insert into linked list"
            );
            debug_assert_eq!(
                this.key.as_bytes(),
                old_leaf.key.as_bytes(),
                "To replace a node, the key must be exactly the same"
            );
        }

        this.next = old_leaf.next;
        this.previous = old_leaf.previous;

        if let Some(prev_leaf_ptr) = this.previous {
            // SAFETY: Covered by safety doc of this function
            let prev_leaf = unsafe { prev_leaf_ptr.as_mut() };
            prev_leaf.next = Some(this_ptr);
        }

        if let Some(next_leaf_ptr) = this.next {
            // SAFETY: Covered by safety doc of this function
            let next_leaf = unsafe { next_leaf_ptr.as_mut() };
            next_leaf.previous = Some(this_ptr);
        }

        old_leaf.next = None;
        old_leaf.previous = None;
    }
}

impl<const PREFIX_LEN: usize, K, V> LeafNode<K, V, PREFIX_LEN> {
    /// Create a new leaf node with the given value and no siblings.
    pub fn with_no_siblings(key: K, value: V) -> Self {
        LeafNode {
            value,
            key,
            previous: None,
            next: None,
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
    pub fn matches_full_key(&self, possible_key: &[u8]) -> bool
    where
        K: AsBytes,
    {
        self.key.as_bytes().eq(possible_key)
    }

    /// This function removes this leaf node from its linked list.
    ///
    /// # Safety
    ///
    /// This function requires that no other operation is concurrently modifying
    /// or reading the `this_ptr` leaf node and its sibling leaf nodes.
    pub unsafe fn remove_self(this_ptr: NodePtr<PREFIX_LEN, Self>) {
        // SAFETY: Covered by safety doc of this function
        let this = unsafe { this_ptr.as_mut() };

        if let Some(sibling_ptr) = this.previous {
            // SAFETY: Covered by safety doc of this function
            let sibling = unsafe { sibling_ptr.as_mut() };
            sibling.next = this.next;
        }

        if let Some(sibling_ptr) = this.next {
            // SAFETY: Covered by safety doc of this function
            let sibling = unsafe { sibling_ptr.as_mut() };
            sibling.previous = this.previous;
        }

        // Normally this is where I would reset the `previous`/`next` pointers
        // to `None`, but it is useful in the delete case to keep this
        // information around.
    }

    /// Create a copy of this leaf node with the sibling references removed.
    pub fn clone_without_siblings(&self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        Self {
            value: self.value.clone(),
            key: self.key.clone(),
            // We override the default clone behavior to wipe these values out, since its unlikely
            // that the cloned leaf should point to the old linked list of leaves
            previous: None,
            next: None,
        }
    }
}

impl<const PREFIX_LEN: usize, K, V> Node<PREFIX_LEN> for LeafNode<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Leaf;
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem;

    #[cfg(not(feature = "nightly"))]
    use sptr::Strict;

    // This test is important because it verifies that we can transform a tagged
    // pointer to a type with large and small alignment and back without issues.
    #[test]
    fn leaf_node_alignment() {
        let mut p0 = TaggedPointer::<LeafNode<[u8; 0], _, 16>, 3>::new(Box::into_raw(Box::new(
            LeafNode::with_no_siblings([], 3u8),
        )))
        .unwrap()
        .cast::<OpaqueValue>();
        p0.set_data(0b001);

        #[repr(align(64))]
        struct LargeAlignment;

        let mut p1 = TaggedPointer::<LeafNode<LargeAlignment, _, 16>, 3>::new(Box::into_raw(
            Box::new(LeafNode::with_no_siblings(LargeAlignment, 2u16)),
        ))
        .unwrap()
        .cast::<OpaqueValue>();
        p1.set_data(0b011);

        let mut p2 = TaggedPointer::<LeafNode<_, LargeAlignment, 16>, 3>::new(Box::into_raw(
            Box::new(LeafNode::with_no_siblings(1u64, LargeAlignment)),
        ))
        .unwrap()
        .cast::<OpaqueValue>();
        p2.set_data(0b111);

        unsafe {
            // These tests apparently leak memory in Miri's POV unless we explicitly cast
            // them back to the original type when we deallocate. The `.cast` calls
            // are required, even though the tests pass under normal execution otherwise (I
            // guess normal test execution doesn't care about leaked memory?)
            drop(Box::from_raw(
                p0.cast::<LeafNode<[u8; 0], u8, 16>>().to_ptr(),
            ));
            drop(Box::from_raw(
                p1.cast::<LeafNode<LargeAlignment, u16, 16>>().to_ptr(),
            ));
            drop(Box::from_raw(
                p2.cast::<LeafNode<u64, LargeAlignment, 16>>().to_ptr(),
            ));
        }
    }

    #[test]
    fn opaque_node_ptr_is_correct() {
        let mut n4 = InnerNode4::<Box<[u8]>, usize, 16>::empty();
        let mut n16 = InnerNode16::<Box<[u8]>, usize, 16>::empty();
        let mut n48 = InnerNode48::<Box<[u8]>, usize, 16>::empty();
        let mut n256 = InnerNode256::<Box<[u8]>, usize, 16>::empty();

        let n4_ptr = NodePtr::from(&mut n4).to_opaque();
        let n16_ptr = NodePtr::from(&mut n16).to_opaque();
        let n48_ptr = NodePtr::from(&mut n48).to_opaque();
        let n256_ptr = NodePtr::from(&mut n256).to_opaque();

        assert!(n4_ptr.is::<InnerNode4<Box<[u8]>, usize, 16>>());
        assert!(n16_ptr.is::<InnerNode16<Box<[u8]>, usize, 16>>());
        assert!(n48_ptr.is::<InnerNode48<Box<[u8]>, usize, 16>>());
        assert!(n256_ptr.is::<InnerNode256<Box<[u8]>, usize, 16>>());
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn node_sizes() {
        const DEFAULT_PREFIX_LEN: usize = 4;
        const EXPECTED_HEADER_SIZE: usize = DEFAULT_PREFIX_LEN.next_multiple_of(8) + 8;

        assert_eq!(
            mem::size_of::<Header<DEFAULT_PREFIX_LEN>>(),
            EXPECTED_HEADER_SIZE
        );
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
            mem::size_of::<InnerNode256<Box<[u8]>, usize, DEFAULT_PREFIX_LEN>>(),
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
        assert_eq!(mem::align_of::<InnerNode256<Box<[u8]>, u8, 16>>(), 8);
        assert_eq!(mem::align_of::<LeafNode<Box<[u8]>, u8, 16>>(), 8);
        assert_eq!(mem::align_of::<Header<16>>(), 8);

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
            mem::align_of::<InnerNode256<Box<[u8]>, u8, 16>>(),
            mem::align_of::<OpaqueValue>()
        );
        assert_eq!(
            mem::align_of::<LeafNode<Box<[u8]>, u8, 16>>(),
            mem::align_of::<OpaqueValue>()
        );

        let n4 = InnerNode4::<Box<[u8]>, (), 16>::empty();
        let n16 = InnerNode4::<Box<[u8]>, (), 16>::empty();
        let n48 = InnerNode4::<Box<[u8]>, (), 16>::empty();
        let n256 = InnerNode4::<Box<[u8]>, (), 16>::empty();

        let n4_ptr = (&n4 as *const InnerNode4<Box<[u8]>, (), 16>).addr();
        let n16_ptr = (&n16 as *const InnerNode4<Box<[u8]>, (), 16>).addr();
        let n48_ptr = (&n48 as *const InnerNode4<Box<[u8]>, (), 16>).addr();
        let n256_ptr = (&n256 as *const InnerNode4<Box<[u8]>, (), 16>).addr();

        // Ensure that there are 3 bits of unused space in the node pointer because of
        // the alignment.
        assert!(n4_ptr.trailing_zeros() >= 3);
        assert!(n16_ptr.trailing_zeros() >= 3);
        assert!(n48_ptr.trailing_zeros() >= 3);
        assert!(n256_ptr.trailing_zeros() >= 3);
    }

    pub(crate) fn inner_node_write_child_test<const PREFIX_LEN: usize>(
        mut node: impl InnerNode<PREFIX_LEN, Key = Box<[u8]>, Value = ()>,
        num_children: usize,
    ) {
        let mut leaves = Vec::with_capacity(num_children);
        for _ in 0..num_children {
            leaves.push(LeafNode::with_no_siblings(vec![].into(), ()));
        }

        assert!(!node.is_full());
        {
            let leaf_pointers = leaves
                .iter_mut()
                .map(|leaf| NodePtr::from(leaf).to_opaque())
                .collect::<Vec<_>>();

            for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
                node.write_child(u8::try_from(idx).unwrap(), leaf_pointer);
            }

            for (idx, leaf_pointer) in leaf_pointers.into_iter().enumerate() {
                assert_eq!(
                    node.lookup_child(u8::try_from(idx).unwrap()),
                    Some(leaf_pointer)
                );
            }
        }

        assert!(node.is_full());
    }

    pub fn inner_node_remove_child_test<const PREFIX_LEN: usize>(
        mut node: impl InnerNode<PREFIX_LEN, Key = Box<[u8]>, Value = ()>,
        num_children: usize,
    ) {
        let mut leaves = Vec::with_capacity(num_children);
        for _ in 0..num_children {
            leaves.push(LeafNode::with_no_siblings(vec![].into(), ()));
        }

        assert!(!node.is_full());
        {
            let leaf_pointers = leaves
                .iter_mut()
                .map(|leaf| NodePtr::from(leaf).to_opaque())
                .collect::<Vec<_>>();

            for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
                node.write_child(u8::try_from(idx).unwrap(), leaf_pointer);
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
        }
        assert!(!node.is_full());
    }

    pub(crate) fn inner_node_shrink_test<const PREFIX_LEN: usize>(
        mut node: impl InnerNode<PREFIX_LEN, Key = Box<[u8]>, Value = ()>,
        num_children: usize,
    ) {
        let mut leaves = Vec::with_capacity(num_children);
        for _ in 0..num_children {
            leaves.push(LeafNode::with_no_siblings(vec![].into(), ()));
        }

        let leaf_pointers = leaves
            .iter_mut()
            .map(|leaf| NodePtr::from(leaf).to_opaque())
            .collect::<Vec<_>>();

        for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
            node.write_child(u8::try_from(idx).unwrap(), leaf_pointer);
        }

        let shrunk_node = node.shrink();

        for (idx, leaf_pointer) in leaf_pointers.into_iter().enumerate() {
            assert_eq!(
                shrunk_node.lookup_child(u8::try_from(idx).unwrap()),
                Some(leaf_pointer)
            );
        }
    }

    // --------------------------------------- ITERATORS
    // ---------------------------------------

    pub(crate) type FixtureReturn<Node, const N: usize> = (
        Node,
        [LeafNode<Box<[u8]>, (), 16>; N],
        [OpaqueNodePtr<Box<[u8]>, (), 16>; N],
    );
}
