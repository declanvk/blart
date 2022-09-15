//! Trie node representation

pub use self::iterators::*;
use crate::tagged_pointer::TaggedPointer;
use std::{
    cmp::Ordering,
    error::Error,
    fmt,
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
    ptr::{self, NonNull},
};
use tinyvec::TinyVec;

mod iterators;

#[cfg(test)]
mod tests;

/// The number of bytes stored for path compression in the node header.
pub const NUM_PREFIX_BYTES: usize = 8;

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
    pub const fn from_u8(src: u8) -> Option<NodeType> {
        let node_type = match src {
            x if x == NodeType::Node4 as u8 => NodeType::Node4,
            x if x == NodeType::Node16 as u8 => NodeType::Node16,
            x if x == NodeType::Node48 as u8 => NodeType::Node48,
            x if x == NodeType::Node256 as u8 => NodeType::Node256,
            x if x == NodeType::Leaf as u8 => NodeType::Leaf,
            _ => {
                return None;
            },
        };

        Some(node_type)
    }
}

/// The common header for all inner nodes
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Header {
    /// Number of children of this inner node. This field has no meaning for
    /// a leaf node.
    pub num_children: u16,
    /// The key prefix for this node.
    pub prefix: TinyVec<[u8; NUM_PREFIX_BYTES]>,
}

impl Header {
    /// Create a new `Header` for an empty node.
    pub fn empty() -> Self {
        Header {
            num_children: 0,
            prefix: TinyVec::new(),
        }
    }

    /// Write prefix bytes to this header, appending to existing bytes if
    /// present.
    pub fn write_prefix(&mut self, new_bytes: &[u8]) {
        self.prefix.extend(new_bytes.iter().copied());
    }

    /// Remove the specified number of bytes from the start of the prefix.
    ///
    /// # Panics
    ///
    ///  - Panics if the number of bytes to remove is greater than the prefix
    ///    size.
    pub fn ltrim_prefix(&mut self, num_bytes: usize) {
        // this is an explicit match instead of a direct `self.prefix.drain` because it
        // is more efficient. See `TinyVec::drain` documentation.
        match self.prefix {
            TinyVec::Inline(ref mut vec) => {
                vec.drain(..num_bytes).for_each(|_| ());
            },
            TinyVec::Heap(ref mut vec) => {
                vec.drain(..num_bytes).for_each(|_| ());
            },
        }
    }

    /// Remove the specified number of bytes from the end of the prefix.
    ///
    /// # Panics
    ///
    ///  - Panics if the number of bytes to remove is greater than the prefix
    ///    size.
    pub fn rtrim_prefix(&mut self, num_bytes: usize) {
        self.prefix.truncate(self.prefix_size() - num_bytes);
    }

    /// Read the initialized portion of the prefix present in the header.
    pub fn read_prefix(&self) -> &[u8] {
        self.prefix.as_ref()
    }

    /// Return the number of bytes in the prefix.
    pub fn prefix_size(&self) -> usize {
        self.prefix.len()
    }

    /// Compares the compressed path of a node with the key and returns the
    /// number of equal bytes.
    pub fn match_prefix(&self, possible_key: &[u8]) -> usize {
        self.read_prefix()
            .iter()
            .zip(possible_key)
            .take_while(|(a, b)| **a == **b)
            .count()
    }

    /// Return the number of children of this node.
    pub fn num_children(&self) -> usize {
        usize::from(self.num_children)
    }
}

#[derive(Debug)]
#[repr(align(8))]
struct OpaqueValue;

/// An opaque pointer to a Node{4,16,48,256}.
///
/// Could be any one of the NodeTypes, need to perform check on the runtime type
/// and then cast to a `NodeRef`.
#[repr(transparent)]
pub struct OpaqueNodePtr<V>(TaggedPointer<OpaqueValue>, PhantomData<V>);

impl<V> Copy for OpaqueNodePtr<V> {}

impl<V> Clone for OpaqueNodePtr<V> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<V> fmt::Debug for OpaqueNodePtr<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("OpaqueNodePtr").field(&self.0).finish()
    }
}

impl<V> fmt::Pointer for OpaqueNodePtr<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

impl<V> Eq for OpaqueNodePtr<V> {}

impl<V> PartialEq for OpaqueNodePtr<V> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<V> OpaqueNodePtr<V> {
    /// Construct a new opaque node pointer from an existing non-null node
    /// pointer.
    pub fn new<N>(pointer: NonNull<N>) -> Self
    where
        N: Node<Value = V>,
    {
        let mut tagged_ptr = TaggedPointer::from(pointer).cast::<OpaqueValue>().unwrap();
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
            Some(NodePtr(self.0.cast::<N>().unwrap().into()))
        } else {
            None
        }
    }

    /// Cast this opaque pointer type an enum that contains a pointer to the
    /// concrete node type.
    pub fn to_node_ptr(self) -> ConcreteNodePtr<V> {
        match self.node_type() {
            NodeType::Node4 => {
                ConcreteNodePtr::Node4(NodePtr(self.0.cast::<InnerNode4<V>>().unwrap().into()))
            },
            NodeType::Node16 => {
                ConcreteNodePtr::Node16(NodePtr(self.0.cast::<InnerNode16<V>>().unwrap().into()))
            },
            NodeType::Node48 => {
                ConcreteNodePtr::Node48(NodePtr(self.0.cast::<InnerNode48<V>>().unwrap().into()))
            },
            NodeType::Node256 => {
                ConcreteNodePtr::Node256(NodePtr(self.0.cast::<InnerNode256<V>>().unwrap().into()))
            },
            NodeType::Leaf => {
                ConcreteNodePtr::LeafNode(NodePtr(self.0.cast::<LeafNode<V>>().unwrap().into()))
            },
        }
    }

    /// Retrieve the runtime node type information.
    pub fn node_type(self) -> NodeType {
        NodeType::from_u8(self.0.to_data().try_into().unwrap()).unwrap()
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
            NodeType::Node4 => {
                let node_ptr = self.0.cast::<InnerNode4<V>>().unwrap().to_ptr();

                ptr::addr_of_mut!((*node_ptr).header)
            },
            NodeType::Node16 => {
                let node_ptr = self.0.cast::<InnerNode16<V>>().unwrap().to_ptr();

                ptr::addr_of_mut!((*node_ptr).header)
            },
            NodeType::Node48 => {
                let node_ptr = self.0.cast::<InnerNode48<V>>().unwrap().to_ptr();

                ptr::addr_of_mut!((*node_ptr).header)
            },
            NodeType::Node256 => {
                let node_ptr = self.0.cast::<InnerNode256<V>>().unwrap().to_ptr();

                ptr::addr_of_mut!((*node_ptr).header)
            },
            NodeType::Leaf => {
                return None;
            },
        };

        // SAFETY: The pointer is properly aligned and points to a initialized instance
        // of Header that is dereferenceable. The lifetime safety requirements are
        // passed up to the caller of this function.
        unsafe { header_ptr.as_mut() }
    }
}

/// An enum that encapsulates pointers to every type of Node
pub enum ConcreteNodePtr<V> {
    /// Node that references between 2 and 4 children
    Node4(NodePtr<InnerNode4<V>>),
    /// Node that references between 5 and 16 children
    Node16(NodePtr<InnerNode16<V>>),
    /// Node that references between 17 and 49 children
    Node48(NodePtr<InnerNode48<V>>),
    /// Node that references between 49 and 256 children
    Node256(NodePtr<InnerNode256<V>>),
    /// Node that contains a single value
    LeafNode(NodePtr<LeafNode<V>>),
}

impl<V> fmt::Debug for ConcreteNodePtr<V> {
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

/// A pointer to a Node{4,16,48,256}.
#[repr(transparent)]
pub struct NodePtr<N: Node>(NonNull<N>);

impl<N: Node> NodePtr<N> {
    /// Create a safe pointer to a Node_.
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
    pub fn allocate_node(node: N) -> Self {
        // SAFETY: The pointer from [`Box::into_raw`] is non-null, aligned, and valid
        // for reads and writes of the [`Node`] `N`.
        unsafe { NodePtr::new(Box::into_raw(Box::new(node))) }
    }

    /// Deallocate a [`Node`] object created with the
    /// [`NodePtr::allocate_node`] function.
    ///
    /// # Safety
    ///
    ///  - This function can only be called once for a given node object.
    pub unsafe fn deallocate_node(node: Self) {
        // SAFETY: Covered by safety condition on functiom
        unsafe {
            drop(Box::from_raw(node.to_ptr()));
        }
    }

    /// Cast node pointer back to an opaque version, losing type information
    pub fn to_opaque(self) -> OpaqueNodePtr<N::Value> {
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
    /// This trait is used to seal other traits, such that they cannot be
    /// implemented outside of the crate.
    pub trait Sealed {}

    impl<V> Sealed for super::InnerNode4<V> {}
    impl<V> Sealed for super::InnerNode16<V> {}
    impl<V> Sealed for super::InnerNode48<V> {}
    impl<V> Sealed for super::InnerNode256<V> {}
    impl<V> Sealed for super::LeafNode<V> {}
}

/// All nodes which contain a runtime tag that validates their type.
pub trait Node: private::Sealed {
    /// The runtime type of the node.
    const TYPE: NodeType;

    /// The value type carried by the leaf nodes
    type Value;
}

/// Common methods implemented by all inner node.
pub trait InnerNode: Node {
    /// The type of the next larger node type.
    type GrownNode: InnerNode<Value = <Self as Node>::Value>;

    /// The type of the next smaller node type.
    type ShrunkNode: InnerNode<Value = <Self as Node>::Value>;

    /// The type of the iterator over all children of the inner node
    type Iter: Iterator<Item = (u8, OpaqueNodePtr<<Self as Node>::Value>)>
        + Into<InnerNodeIter<<Self as Node>::Value>>;

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<Self::Value>>;

    /// Write a child pointer with key fragment to this inner node.
    ///
    /// If the key fragment already exists in the node, overwrite the existing
    /// child pointer.
    ///
    /// # Panics
    ///
    /// Panics when the node is full.
    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<Self::Value>);

    /// Attempt to remove a child pointer at the key fragment from this inner
    /// node.
    ///
    /// If the key fragment does not exist in this node, return `None`.
    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<Self::Value>>;

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

    /// Access the header information for this node.
    fn header(&self) -> &Header;

    /// Access the header information for this node.
    fn header_mut(&mut self) -> &mut Header;

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
    unsafe fn iter(&self) -> Self::Iter;
}

/// Node type that has a compact representation for key bytes and children
/// pointers.
pub struct InnerNodeCompressed<V, const SIZE: usize> {
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
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<V>>; SIZE],
}

impl<V, const SIZE: usize> Clone for InnerNodeCompressed<V, SIZE> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            keys: self.keys,
            child_pointers: self.child_pointers,
        }
    }
}

impl<V, const SIZE: usize> fmt::Debug for InnerNodeCompressed<V, SIZE> {
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

impl<V, const SIZE: usize> InnerNodeCompressed<V, SIZE> {
    /// Create an empty [`InnerNodeCompressed`] with the given [`NodeType`].
    pub fn empty() -> Self {
        InnerNodeCompressed {
            header: Header::default(),
            child_pointers: MaybeUninit::uninit_array(),
            keys: MaybeUninit::uninit_array(),
        }
    }

    fn lookup_child_index(&self, key_fragment: u8) -> Option<usize> {
        let (keys, _) = self.initialized_portion();

        for (child_index, key) in keys.iter().enumerate() {
            if *key == key_fragment {
                return Some(child_index);
            }
        }

        None
    }

    /// Return the initialized portions of the keys and child pointer arrays.
    pub fn initialized_portion(&self) -> (&[u8], &[OpaqueNodePtr<V>]) {
        // SAFETY: The array prefix with length `header.num_children` is guaranteed to
        // be initialized
        unsafe {
            (
                MaybeUninit::slice_assume_init_ref(&self.keys[0..self.header.num_children()]),
                MaybeUninit::slice_assume_init_ref(
                    &self.child_pointers[0..self.header.num_children()],
                ),
            )
        }
    }

    fn lookup_child_inner(&self, key_fragment: u8) -> Option<OpaqueNodePtr<V>> {
        let child_index = self.lookup_child_index(key_fragment)?;
        // SAFETY: The value at `child_index` is guaranteed to be initialized because
        // the `lookup_child_index` function will only search in the initialized portion
        // of the `child_pointers` array.
        Some(unsafe { MaybeUninit::assume_init(self.child_pointers[child_index]) })
    }

    fn write_child_inner(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<V>) {
        let (keys, _) = self.initialized_portion();
        let num_children = self.header.num_children();
        match keys.binary_search(&key_fragment) {
            Ok(child_index) => {
                // overwrite existing key
                self.child_pointers[child_index].write(child_pointer);
            },
            Err(child_index) => {
                // add new key
                // make sure new index is not beyond bounds, checks node is not full
                assert!(child_index < self.keys.len(), "node is full");

                if child_index != self.keys.len() - 1 {
                    self.keys
                        .copy_within(child_index..num_children, child_index + 1);
                    self.child_pointers
                        .copy_within(child_index..num_children, child_index + 1);
                }

                self.keys[child_index].write(key_fragment);
                self.child_pointers[child_index].write(child_pointer);

                self.header.num_children += 1;
            },
        }
    }

    fn remove_child_inner(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<V>> {
        let search_result = {
            let (keys, _) = self.initialized_portion();
            keys.binary_search(&key_fragment)
        };

        match search_result {
            Ok(child_index) => {
                let child_ptr =
                    mem::replace(&mut self.child_pointers[child_index], MaybeUninit::uninit());

                // Copy all the child_pointer and key values in higher indices down by one.
                self.child_pointers
                    .copy_within((child_index + 1)..self.header.num_children(), child_index);
                self.keys
                    .copy_within((child_index + 1)..self.header.num_children(), child_index);

                self.header.num_children -= 1;
                // SAFETY: This child pointer value is initialized because we got it by
                // searching through the initialized keys and got the `Ok(index)` value.
                Some(unsafe { MaybeUninit::assume_init(child_ptr) })
            },
            Err(_) => None,
        }
    }

    fn change_block_size<const NEW_SIZE: usize>(&self) -> InnerNodeCompressed<V, NEW_SIZE> {
        assert!(
            self.header.num_children() <= NEW_SIZE,
            "Cannot change InnerNodeCompressed<{}> to size {} when it has more than {} children. \
             Currently has [{}] children.",
            SIZE,
            NEW_SIZE,
            NEW_SIZE,
            self.header.num_children
        );

        let header = self.header.clone();
        let mut keys = MaybeUninit::<u8>::uninit_array::<NEW_SIZE>();
        let mut child_pointers = MaybeUninit::<OpaqueNodePtr<V>>::uninit_array::<NEW_SIZE>();

        keys[..header.num_children()].copy_from_slice(&self.keys[..header.num_children()]);
        child_pointers[..header.num_children()]
            .copy_from_slice(&self.child_pointers[..header.num_children()]);

        InnerNodeCompressed {
            header,
            keys,
            child_pointers,
        }
    }

    fn grow_node48(&self) -> InnerNode48<V> {
        let header = self.header.clone();
        let mut child_indices = [RestrictedNodeIndex::<48>::EMPTY; 256];
        let mut child_pointers = MaybeUninit::<OpaqueNodePtr<V>>::uninit_array::<48>();

        let (n16_keys, _) = self.initialized_portion();

        for (index, key) in n16_keys.iter().copied().enumerate() {
            // PANIC SAFETY: This `try_from` will not panic because index is guaranteed to
            // be 15 or less because of the length of the `InnerNode16.keys` array.
            child_indices[usize::from(key)] = RestrictedNodeIndex::<48>::try_from(index).unwrap();
        }

        child_pointers[..header.num_children()]
            .copy_from_slice(&self.child_pointers[..header.num_children()]);

        InnerNode48 {
            header,
            child_indices,
            child_pointers,
        }
    }
}

/// Node that references between 2 and 4 children
pub type InnerNode4<V> = InnerNodeCompressed<V, 4>;

impl<V> Node for InnerNode4<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Node4;
}

impl<V> InnerNode for InnerNode4<V> {
    type GrownNode = InnerNode16<Self::Value>;
    type Iter = InnerNodeCompressedIter<Self::Value>;
    type ShrunkNode = InnerNode4<Self::Value>;

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<V>> {
        Self::lookup_child_inner(self, key_fragment)
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<V>) {
        Self::write_child_inner(self, key_fragment, child_pointer)
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<Self::Value>> {
        Self::remove_child_inner(self, key_fragment)
    }

    fn grow(&self) -> Self::GrownNode {
        self.change_block_size()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        panic!("unable to shrink a Node4, something went wrong!")
    }

    fn header(&self) -> &Header {
        &self.header
    }

    fn header_mut(&mut self) -> &mut Header {
        &mut self.header
    }

    unsafe fn iter(&self) -> Self::Iter {
        // SAFETY: The safety requirements on the `iter` function match the `new`
        // function
        unsafe { InnerNodeCompressedIter::new(self) }
    }
}

/// Node that references between 5 and 16 children
pub type InnerNode16<V> = InnerNodeCompressed<V, 16>;

impl<V> Node for InnerNode16<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Node16;
}

impl<V> InnerNode for InnerNode16<V> {
    type GrownNode = InnerNode48<Self::Value>;
    type Iter = InnerNodeCompressedIter<Self::Value>;
    type ShrunkNode = InnerNode4<Self::Value>;

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<V>> {
        Self::lookup_child_inner(self, key_fragment)
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<V>) {
        Self::write_child_inner(self, key_fragment, child_pointer)
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<Self::Value>> {
        Self::remove_child_inner(self, key_fragment)
    }

    fn grow(&self) -> Self::GrownNode {
        self.grow_node48()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        self.change_block_size()
    }

    fn header(&self) -> &Header {
        &self.header
    }

    fn header_mut(&mut self) -> &mut Header {
        &mut self.header
    }

    unsafe fn iter(&self) -> Self::Iter {
        // SAFETY: The safety requirements on the `iter` function match the `new`
        // function
        unsafe { InnerNodeCompressedIter::new(self) }
    }
}

/// A restricted index only valid from 0 to LIMIT - 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct RestrictedNodeIndex<const LIMIT: u8>(u8);

impl<const LIMIT: u8> RestrictedNodeIndex<LIMIT> {
    /// A placeholder index value that indicates that the index is not occupied
    pub const EMPTY: Self = RestrictedNodeIndex(LIMIT);
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
            Ok(RestrictedNodeIndex(value as u8))
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
pub struct InnerNode48<V> {
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
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<V>>; 48],
}

impl<V> fmt::Debug for InnerNode48<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode48")
            .field("header", &self.header)
            .field("child_indices", &self.child_indices)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<V> Clone for InnerNode48<V> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_indices: self.child_indices,
            child_pointers: self.child_pointers,
        }
    }
}

impl<V> InnerNode48<V> {
    /// Create an empty `Node48`.
    pub fn empty() -> Self {
        InnerNode48 {
            header: Header::default(),
            child_indices: [RestrictedNodeIndex::<48>::EMPTY; 256],
            child_pointers: MaybeUninit::uninit_array(),
        }
    }

    /// Return the initialized portions of the child pointer array.
    pub fn initialized_child_pointers(&self) -> &[OpaqueNodePtr<V>] {
        // SAFETY: The array prefix with length `header.num_children` is guaranteed to
        // be initialized
        unsafe {
            MaybeUninit::slice_assume_init_ref(&self.child_pointers[0..self.header.num_children()])
        }
    }
}

impl<V> Node for InnerNode48<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Node48;
}

impl<V> InnerNode for InnerNode48<V> {
    type GrownNode = InnerNode256<Self::Value>;
    type Iter = InnerNode48Iter<Self::Value>;
    type ShrunkNode = InnerNode16<Self::Value>;

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<Self::Value>> {
        let index = &self.child_indices[usize::from(key_fragment)];
        let child_pointers = self.initialized_child_pointers();
        if *index != RestrictedNodeIndex::EMPTY {
            Some(child_pointers[usize::from(*index)])
        } else {
            None
        }
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<Self::Value>) {
        let key_fragment_idx = usize::from(key_fragment);
        let child_index = if self.child_indices[key_fragment_idx] == RestrictedNodeIndex::EMPTY {
            let child_index = self.header.num_children();
            assert!(child_index < self.child_pointers.len(), "node is full");

            self.child_indices[key_fragment_idx] =
                RestrictedNodeIndex::<48>::try_from(child_index).unwrap();
            self.header.num_children += 1;
            child_index
        } else {
            // overwrite existing
            usize::from(self.child_indices[key_fragment_idx])
        };
        self.child_pointers[child_index].write(child_pointer);
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<Self::Value>> {
        let restricted_index = self.child_indices[usize::from(key_fragment)];
        if restricted_index != RestrictedNodeIndex::EMPTY {
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
                if let Some(Ordering::Less) = restricted_index.partial_cmp(other_restrict_index) {
                    // PANIC SAFETY: This will not underflow, because it is guaranteed to be
                    // greater than at least 1 other index. This will not panic in the
                    // `try_from` because the new value is derived from an existing restricted
                    // index.
                    *other_restrict_index =
                        RestrictedNodeIndex::try_from(other_restrict_index.0 - 1).unwrap()
                }
            }

            self.child_indices[usize::from(key_fragment)] = RestrictedNodeIndex::EMPTY;
            self.header.num_children -= 1;
            // SAFETY: This child pointer value is initialized because we got it by using a
            // non-`RestrictedNodeIndex::<>::EMPTY` index from the child indices array.
            Some(unsafe { MaybeUninit::assume_init(child_ptr) })
        } else {
            None
        }
    }

    fn grow(&self) -> Self::GrownNode {
        let header = self.header.clone();
        let mut child_pointers = [None; 256];
        // SAFETY: This iterator lives only for the lifetime of this function, which
        // does not mutate the `InnerNode48` (guaranteed by reference).
        let iter = unsafe { InnerNode48Iter::new(self) };

        for (key_fragment, child_pointer) in iter {
            child_pointers[usize::from(key_fragment)] = Some(child_pointer);
        }

        InnerNode256 {
            header,
            child_pointers,
        }
    }

    fn shrink(&self) -> Self::ShrunkNode {
        assert!(
            self.header.num_children <= 16,
            "Cannot shrink a Node48 when it has more than 16 children. Currently has [{}] \
             children.",
            self.header.num_children
        );

        let header = self.header.clone();

        let mut key_and_child_ptrs = MaybeUninit::<(u8, OpaqueNodePtr<V>)>::uninit_array::<16>();
        // SAFETY: The lifetime of this iterator is bounded to this function, and will
        // not overlap with any mutating operations on the node because it of the shared
        // reference that this function uses.
        let iter = unsafe { InnerNode48Iter::new(self) };

        for (idx, value) in iter.enumerate() {
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

        let mut keys = MaybeUninit::<u8>::uninit_array::<16>();
        let mut child_pointers = MaybeUninit::<OpaqueNodePtr<V>>::uninit_array::<16>();

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

    fn header(&self) -> &Header {
        &self.header
    }

    fn header_mut(&mut self) -> &mut Header {
        &mut self.header
    }

    unsafe fn iter(&self) -> Self::Iter {
        // SAFETY: The safety requirements on the `iter` function match the `new`
        // function
        unsafe { InnerNode48Iter::new(self) }
    }
}

/// Node that references between 49 and 256 children
pub struct InnerNode256<V> {
    /// The common node fields.
    pub header: Header,
    /// An array that directly maps a key byte (as index) to a child node.
    pub child_pointers: [Option<OpaqueNodePtr<V>>; 256],
}

impl<V> fmt::Debug for InnerNode256<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode256")
            .field("header", &self.header)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<V> Clone for InnerNode256<V> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_pointers: self.child_pointers,
        }
    }
}

impl<V> InnerNode256<V> {
    /// Create an empty `InnerNode256`.
    pub fn empty() -> Self {
        InnerNode256 {
            header: Header::default(),
            child_pointers: [None; 256],
        }
    }
}

impl<V> Node for InnerNode256<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Node256;
}

impl<V> InnerNode for InnerNode256<V> {
    type GrownNode = Self;
    type Iter = InnerNode256Iter<V>;
    type ShrunkNode = InnerNode48<V>;

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<Self::Value>> {
        self.child_pointers[usize::from(key_fragment)]
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<Self::Value>) {
        let key_fragment_idx = usize::from(key_fragment);
        let existing_pointer = self.child_pointers[key_fragment_idx];
        self.child_pointers[key_fragment_idx] = Some(child_pointer);
        if existing_pointer.is_none() {
            self.header.num_children += 1;
        }
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<Self::Value>> {
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
        assert!(
            self.header.num_children <= 48,
            "Cannot shrink a Node256 when it has more than 48 children. Currently has [{}] \
             children.",
            self.header.num_children
        );

        let header = self.header.clone();
        let mut child_indices = [RestrictedNodeIndex::<48>::EMPTY; 256];
        let mut child_pointers = MaybeUninit::<OpaqueNodePtr<V>>::uninit_array::<48>();

        // SAFETY: This iterator lives only for the lifetime of this function, which
        // does not mutate the `InnerNode256` (guaranteed by reference).
        let iter = unsafe { InnerNode256Iter::new(self) };

        for (child_index, (key_byte, child_ptr)) in iter.enumerate() {
            // PANIC SAFETY: This `try_from` will not panic because the `next_index` value
            // is guaranteed to be 48 or less by the `assert!(num_children < 48)` at the
            // start of the function.
            child_indices[usize::from(key_byte)] =
                RestrictedNodeIndex::<48>::try_from(child_index).unwrap();
            child_pointers[child_index].write(child_ptr);
        }

        InnerNode48 {
            header,
            child_indices,
            child_pointers,
        }
    }

    fn header(&self) -> &Header {
        &self.header
    }

    fn header_mut(&mut self) -> &mut Header {
        &mut self.header
    }

    unsafe fn iter(&self) -> Self::Iter {
        // SAFETY: The safety requirements on the `iter` function match the `new`
        // function
        unsafe { InnerNode256Iter::new(self) }
    }
}

/// Node that contains a single leaf value.
#[derive(Debug, Clone)]
pub struct LeafNode<V> {
    /// The leaf value.
    pub value: V,
    /// The full key that the `value` was stored with.
    pub key: Box<[u8]>,
}

impl<V> LeafNode<V> {
    /// Create a new leaf node with the given value.
    pub fn new(key: Box<[u8]>, value: V) -> Self {
        LeafNode { value, key }
    }

    /// Check that the provided full key is the same one as the stored key.
    pub fn matches_full_key(&self, possible_key: &[u8]) -> bool {
        self.key.as_ref().eq(possible_key)
    }
}

impl<V> Node for LeafNode<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Leaf;
}
