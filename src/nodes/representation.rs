//! Trie node representation

use smallvec::SmallVec;
use std::{
    cmp,
    error::Error,
    fmt,
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    ptr::{self, NonNull},
};

/// The number of bytes stored for path compression in the node header.
pub const NUM_PREFIX_BYTES: usize = 8;

/// The representation of inner nodes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum NodeType {
    /// Node that references between 2 and 4 children
    Node4 = 0b000,
    /// Node that references between 5 and 16 children
    Node16, // 0b001
    /// Node that references between 17 and 49 children
    Node48, // 0b010
    /// Node that references between 49 and 256 children
    Node256, // 0b011
    /// Node that contains a single value
    Leaf, // 0b100
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
}

/// The common header for all inner nodes
#[derive(Clone)]
#[repr(C)]
pub struct Header {
    /// Number of children of this inner node. This field has no meaning for
    /// a leaf node.
    pub num_children: u16,
    /// The type of representation for this current node
    pub node_type: NodeType,
    /// The key prefix for this node.
    ///
    /// Only the first `prefix_size` bytes are guaranteed to be initialized.
    // size NUM_PREFIX_BYTES, alignment 1
    pub prefix: SmallVec<[u8; NUM_PREFIX_BYTES]>,
}

impl fmt::Debug for Header {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = self.read_prefix();
        f.debug_struct("Header")
            .field("num_children", &self.num_children)
            .field("node_type", &self.node_type)
            .field("prefix", &prefix)
            .finish()
    }
}

impl Header {
    /// Create a new `Header` for an empty node.
    pub fn empty() -> Self {
        Header {
            num_children: 0,
            node_type: NodeType::Node4,
            prefix: SmallVec::new(),
        }
    }

    /// Write prefix bytes to this header, appending to existing bytes if
    /// present.
    ///
    /// If the total numbers of bytes (existing + new) is greater than
    /// [`NUM_PREFIX_BYTES`], the prefix is truncated to [`NUM_PREFIX_BYTES`]
    /// length and remainder are represented implicitly by the length. This
    /// doesn't present an issue to the radix tree operation (lookup, insert,
    /// etc) because the full key is always stored in the leaf nodes.
    pub fn write_prefix(&mut self, new_bytes: &[u8]) {
        self.prefix.extend(new_bytes.iter().copied());
    }

    /// Remove the specified number of bytes from the start of the prefix.
    ///
    /// # Panics
    ///
    ///  - Panics if the number of bytes to remove is greater than or equal to
    ///    the prefix size
    pub fn ltrim_prefix(&mut self, num_bytes: usize) {
        self.prefix.drain(..num_bytes).for_each(|_| ());
    }

    /// Read the initialized portion of the prefix present in the header.
    ///
    /// The `prefix_size` can be larger than the `read_prefix().len()` because
    /// only [`NUM_PREFIX_BYTES`] are stored.
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
        let inited_prefix = self.read_prefix();

        let mut num_matching_bytes: usize = 0;
        for index in 0..cmp::min(inited_prefix.len(), possible_key.len()) {
            if inited_prefix[index] != possible_key[index] {
                break;
            }

            num_matching_bytes += 1;
        }

        num_matching_bytes
    }

    /// Return true if the number of children of this node is greater than or
    /// equal to the maximum capacity of this node type.
    pub fn is_full(&self) -> bool {
        self.num_children() >= self.node_type.upper_capacity()
    }

    /// Return the number of children of this node.
    pub fn num_children(&self) -> usize {
        usize::from(self.num_children)
    }
}

impl Default for Header {
    fn default() -> Self {
        Self::empty()
    }
}

/// An opaque pointer to a Node{4,16,48,256}.
///
/// Could be any one of the NodeTypes, need to perform check on the runtime type
/// and then cast to a `NodeRef`.
#[repr(transparent)]
pub struct OpaqueNodePtr<V>(NonNull<Header>, PhantomData<V>);

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

impl<V> Eq for OpaqueNodePtr<V> {}

impl<V> PartialEq for OpaqueNodePtr<V> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<V> OpaqueNodePtr<V> {
    /// Return `true` if this Node_ pointer points to the specified concrete
    /// [`NodeType`].
    pub fn is<N: TaggedNode>(&self) -> bool {
        // SAFETY: inner pointer is guaranteed not to be null by `NonNull` wrapper.
        unsafe { (*self.0.as_ptr()).node_type == N::TYPE }
    }

    /// Create a non-opaque node pointer that will eliminate future type
    /// assertions, if the type of the pointed node matches the given
    /// node type.
    pub fn cast<N: TaggedNode>(self) -> Option<NodePtr<N>> {
        if self.is::<N>() {
            // SAFETY: This cast is safe because all Node_ types have `repr(C)`
            // and have the `Header` field first.
            Some(NodePtr(self.0.cast::<N>()))
        } else {
            None
        }
    }

    /// Cast this opaque pointer type an enum that contains a pointer to the
    /// concrete node type.
    pub fn to_node_ptr(self) -> InnerNodePtr<V> {
        let header = self.read();
        match header.node_type {
            NodeType::Node4 => InnerNodePtr::Node4(self.cast::<InnerNode4<V>>().unwrap()),
            NodeType::Node16 => InnerNodePtr::Node16(self.cast::<InnerNode16<V>>().unwrap()),
            NodeType::Node48 => InnerNodePtr::Node48(self.cast::<InnerNode48<V>>().unwrap()),
            NodeType::Node256 => InnerNodePtr::Node256(self.cast::<InnerNode256<V>>().unwrap()),
            NodeType::Leaf => InnerNodePtr::LeafNode(self.cast::<LeafNode<V>>().unwrap()),
        }
    }

    /// Reads the Node from self without moving it. This leaves the memory in
    /// self unchanged.
    pub fn read(self) -> ManuallyDrop<Header> {
        // SAFETY: The non-null requirements of ptr::read is already
        // guaranteed by the NonNull wrapper. The requirements of proper alignment,
        // initialization, validity for reads are required by the construction
        // of the NodePtr type. An OpaqueNodePtr can only be constructed from an earlier
        // instance of a NodePtr.
        ManuallyDrop::new(unsafe { ptr::read(self.0.as_ptr()) })
    }

    /// Write a new value for the header without moving the old value.
    ///
    /// The old value is overwritten without dropping because the [Header]
    /// struct is Copy.
    pub fn write(self, updated_value: Header) {
        // SAFETY: The requirements of proper alignment and validity for
        // writes are required by the construction of the NodePtr type. An
        // OpaqueNodePtr can only be constructed from an earlier instance of a
        // NodePtr.
        unsafe { ptr::write(self.0.as_ptr(), updated_value) }
    }

    /// Acquires the underlying *mut pointer.
    pub fn to_ptr(self) -> *mut Header {
        self.0.as_ptr()
    }
}

/// An that encapsulates all the types of Nodes
pub enum InnerNodePtr<V> {
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

impl<V> fmt::Debug for InnerNodePtr<V> {
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
pub struct NodePtr<N: TaggedNode>(NonNull<N>);

impl<N: TaggedNode> NodePtr<N> {
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

    /// Allocate the given [`TaggedNode`] on the [`std::alloc::Global`] heap and
    /// return a [`NodePtr`] that wrap the raw pointer.
    pub fn allocate_node(node: N) -> Self {
        // SAFETY: The pointer from [`Box::into_raw`] is non-null, aligned, and valid
        // for reads and writes of the [`TaggedNode`] `N`.
        unsafe { NodePtr::new(Box::into_raw(Box::new(node))) }
    }

    /// Deallocate a [`TaggedNode`] object created with the
    /// [`NodePtr::allocate_node`] function.
    ///
    /// # Safety
    ///
    ///  - This function can only be called when there is only a single
    ///    remaining [`NodePtr`] to the object, otherwise other pointers would
    ///    be referenced deallocated memory.
    ///  - This function can only be called once for a given node object.
    pub unsafe fn deallocate_node(node: Self) {
        // SAFETY: Covered by safety condition on functiom
        unsafe {
            Box::from_raw(node.to_ptr());
        }
    }

    /// Cast node pointer back to an opaque version, losing type information
    pub fn to_opaque(self) -> OpaqueNodePtr<N::Value> {
        // SAFETY: This cast is safe because all Node_ types have `repr(C)`
        // and have the `Header` field first.
        OpaqueNodePtr(self.0.cast::<Header>(), PhantomData)
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

    /// With the given closure, perform an update to the underlying node through
    /// a mutable reference.
    ///
    /// # Safety
    ///
    ///  - This function must not be called concurrent with any other read or
    ///    mutation of the underlying node.
    pub unsafe fn update<O>(mut self, f: impl FnOnce(&mut N) -> O) -> O {
        // SAFETY: The pointer is properly aligned and points to a initialized instance
        // of N that is dereferenceable. The lifetime of this reference is bounded to
        // this function and will not escape the code. However, calls to this function
        // must enforce the uniqueness constraint that is associated with mutable
        // references.
        let inner_value = unsafe { self.0.as_mut() };

        (f)(inner_value)
    }

    /// Acquires the underlying *mut pointer.
    pub fn to_ptr(self) -> *mut N {
        self.0.as_ptr()
    }
}

impl<N: TaggedNode> Clone for NodePtr<N> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<N: TaggedNode> Copy for NodePtr<N> {}

impl<N: TaggedNode> From<&mut N> for NodePtr<N> {
    fn from(node_ref: &mut N) -> Self {
        // SAFETY: Pointer is non-null, aligned, and pointing to a valid instance of N
        // because it was constructed from a mutable reference.
        unsafe { NodePtr::new(node_ref as *mut _) }
    }
}

impl<N: TaggedNode> PartialEq for NodePtr<N> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<N: TaggedNode> Eq for NodePtr<N> {}

impl<N: TaggedNode> fmt::Debug for NodePtr<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("NodePtr").field(&self.0).finish()
    }
}

/// All nodes which contain a runtime tag that validates their type.
pub trait TaggedNode {
    /// The runtime type of the node.
    const TYPE: NodeType;

    /// The value type carried by the leaf nodes
    type Value;
}

/// Node that references between 2 and 4 children
#[repr(C)]
pub struct InnerNode4<V> {
    /// The common node fields.
    pub header: Header,
    /// An array that contains the child data.
    ///
    /// This array will only be initialized for the first`header.num_children`
    /// values.
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<V>>; 4],
    /// An array that contains single key bytes in the same index as the
    /// `child_pointers` array contains the matching child tree.
    ///
    /// This array will only be initialized for the first `header.num_children`
    /// values.
    pub keys: [MaybeUninit<u8>; 4],
}

impl<V> Clone for InnerNode4<V> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            keys: self.keys,
            child_pointers: self.child_pointers,
        }
    }
}

impl<V> fmt::Debug for InnerNode4<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (keys, child_pointers) = self.initialized_portion();
        f.debug_struct("InnerNode4")
            .field("header", &self.header)
            .field("keys", &keys)
            .field("child_pointers", &child_pointers)
            .finish()
    }
}

impl<V> InnerNode4<V> {
    /// Create an empty `Node4`.
    pub fn empty() -> Self {
        InnerNode4 {
            header: Header::empty(),
            child_pointers: MaybeUninit::uninit_array(),
            keys: MaybeUninit::uninit_array(),
        }
    }

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    pub fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<V>> {
        let child_index = self.lookup_child_index(key_fragment)?;
        // SAFETY: The value at `child_index` is guaranteed to be initialized because
        // the `lookup_child_index` function will only search in the initialized portion
        // of the `child_pointers` array.
        Some(unsafe { MaybeUninit::assume_init(self.child_pointers[child_index]) })
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

    /// Write a child pointer with key fragment to this inner node.
    ///
    /// If the key fragment already exists in the node, overwrite the existing
    /// child pointer.
    ///
    /// # Panics
    ///
    /// Panics when the node is full.
    pub fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<V>) {
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

    /// Return an iterator over all the children of this node with their
    /// associated key fragment
    pub fn iter(&self) -> impl Iterator<Item = (u8, OpaqueNodePtr<V>)> + '_ {
        let (keys, child_pointers) = self.initialized_portion();
        keys.iter().copied().zip(child_pointers.iter().copied())
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

    /// Grow this node into the next larger class, copying over children and
    /// prefix information.
    pub fn grow(&self) -> InnerNode16<V> {
        let mut header = self.header.clone();
        header.node_type = InnerNode16::<V>::TYPE;
        let mut keys = MaybeUninit::<u8>::uninit_array::<16>();
        let mut child_pointers = MaybeUninit::<OpaqueNodePtr<V>>::uninit_array::<16>();

        keys[..header.num_children()].copy_from_slice(&self.keys[..header.num_children()]);
        child_pointers[..header.num_children()]
            .copy_from_slice(&self.child_pointers[..header.num_children()]);

        InnerNode16 {
            header,
            keys,
            child_pointers,
        }
    }
}

impl<V> TaggedNode for InnerNode4<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Node4;
}

/// Node that references between 5 and 16 children
#[repr(C)]
pub struct InnerNode16<V> {
    /// The common node fields.
    pub header: Header,
    /// An array that contains single key bytes in the same index as the
    /// `child_pointers` array contains the matching child tree.
    ///
    /// This array will only be initialized for `header.num_children` values,
    /// starting from the 0 index.
    pub keys: [MaybeUninit<u8>; 16],
    /// An array that contains the child data.
    ///
    /// This array will only be initialized for `header.num_children` values,
    /// starting from the 0 index.
    pub child_pointers: [MaybeUninit<OpaqueNodePtr<V>>; 16],
}

impl<V> Clone for InnerNode16<V> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            keys: self.keys,
            child_pointers: self.child_pointers,
        }
    }
}

impl<V> fmt::Debug for InnerNode16<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (keys, child_pointers) = self.initialized_portion();
        f.debug_struct("InnerNode16")
            .field("header", &self.header)
            .field("keys", &keys)
            .field("child_pointers", &child_pointers)
            .finish()
    }
}

impl<V> InnerNode16<V> {
    /// Create an empty `Node16`.
    pub fn empty() -> Self {
        InnerNode16 {
            header: Header {
                node_type: NodeType::Node16,
                ..Header::default()
            },
            child_pointers: MaybeUninit::uninit_array(),
            keys: MaybeUninit::uninit_array(),
        }
    }

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    pub fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<V>> {
        let child_index = self.lookup_child_index(key_fragment)?;
        // SAFETY: The value at `child_index` is guaranteed to be initialized because
        // the `lookup_child_index` function will only search in the initialized portion
        // of the `child_pointers` array.
        Some(unsafe { MaybeUninit::assume_init(self.child_pointers[child_index]) })
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

    /// Write a child pointer with key fragment to this inner node.
    ///
    /// If the key fragment already exists in the node, overwrite the existing
    /// child pointer.
    ///
    /// # Panics
    ///
    /// Panics when the node is full.
    pub fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<V>) {
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

    /// Return an iterator over all the children of this node with their
    /// associated key fragment
    pub fn iter(&self) -> impl Iterator<Item = (u8, OpaqueNodePtr<V>)> + '_ {
        let (keys, child_pointers) = self.initialized_portion();

        keys.iter().copied().zip(child_pointers.iter().copied())
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

    /// Grow this node into the next larger class, copying over children and
    /// prefix information.
    pub fn grow(&self) -> InnerNode48<V> {
        let mut header = self.header.clone();
        header.node_type = InnerNode48::<V>::TYPE;
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

impl<V> TaggedNode for InnerNode16<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Node16;
}

/// A restricted index only valid from 0 to LIMIT - 1.
#[derive(Debug, Clone, Copy, PartialEq)]
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
#[repr(C)]
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
            header: Header {
                node_type: NodeType::Node48,
                ..Header::default()
            },
            child_indices: [RestrictedNodeIndex::<48>::EMPTY; 256],
            child_pointers: MaybeUninit::uninit_array(),
        }
    }

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    pub fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<V>> {
        let index = &self.child_indices[usize::from(key_fragment)];
        let child_pointers = self.initialized_child_pointers();
        if *index != RestrictedNodeIndex::<48>::EMPTY {
            Some(child_pointers[usize::from(u8::from(*index))])
        } else {
            None
        }
    }

    /// Write a child pointer with key fragment to this inner node.
    ///
    /// If the key fragment already exists in the node, overwrite the existing
    /// child pointer.
    ///
    /// # Panics
    ///
    /// Panics when the node is full.
    pub fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<V>) {
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
            usize::from(u8::from(self.child_indices[key_fragment_idx]))
        };
        self.child_pointers[child_index].write(child_pointer);
    }

    /// Return an iterator over all the children of this node with their
    /// associated key fragment
    pub fn iter(&self) -> impl Iterator<Item = (u8, OpaqueNodePtr<V>)> + '_ {
        let child_pointers = self.initialized_child_pointers();

        self.child_indices
            .iter()
            .enumerate()
            .filter(|(_, index)| **index != RestrictedNodeIndex::<48>::EMPTY)
            .map(|(key_fragment, index)| {
                (
                    // PANIC SAFETY: The length of the `self.child_indices` array is 256, so the
                    // `key_fragment` derived from `enumerate()` will never exceed the bounds of a
                    // u8
                    u8::try_from(key_fragment).unwrap(),
                    child_pointers[usize::from(u8::from(*index))],
                )
            })
    }

    /// Return the initialized portions of the child pointer array.
    pub fn initialized_child_pointers(&self) -> &[OpaqueNodePtr<V>] {
        // SAFETY: The array prefix with length `header.num_children` is guaranteed to
        // be initialized
        unsafe {
            MaybeUninit::slice_assume_init_ref(&self.child_pointers[0..self.header.num_children()])
        }
    }

    /// Grow this node into the next larger class, copying over children and
    /// prefix information.
    pub fn grow(&self) -> InnerNode256<V> {
        let mut header = self.header.clone();
        header.node_type = InnerNode256::<V>::TYPE;
        let mut child_pointers = [None; 256];

        for (key_fragment, child_pointer) in self.iter() {
            child_pointers[usize::from(key_fragment)] = Some(child_pointer);
        }

        InnerNode256 {
            header,
            child_pointers,
        }
    }
}

impl<V> TaggedNode for InnerNode48<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Node48;
}

/// Node that references between 49 and 256 children
#[repr(C)]
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
            header: Header {
                node_type: NodeType::Node256,
                ..Header::default()
            },
            child_pointers: [None; 256],
        }
    }

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    pub fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<V>> {
        self.child_pointers[key_fragment as usize]
    }

    /// Write a child pointer with key fragment to this inner node.
    ///
    /// If the key fragment already exists in the node, overwrite the existing
    /// child pointer.
    pub fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<V>) {
        let key_fragment_idx = usize::from(key_fragment);
        let existing_pointer = self.child_pointers[key_fragment_idx];
        self.child_pointers[key_fragment_idx] = Some(child_pointer);
        if existing_pointer.is_none() {
            self.header.num_children += 1;
        }
    }

    /// Return an iterator over all the children of this node with their
    /// associated key fragment
    pub fn iter(&self) -> impl Iterator<Item = (u8, OpaqueNodePtr<V>)> + '_ {
        self.child_pointers
            .iter()
            .enumerate()
            .filter_map(|(key_fragment, child_pointer)| {
                child_pointer.map(|child_pointer| {
                    (
                        // PANIC SAFETY: The length of the `self.child_pointers` array is 256, so
                        // the `key_fragment` derived from `enumerate()`
                        // will never exceed the bounds of a u8
                        u8::try_from(key_fragment).unwrap(),
                        child_pointer,
                    )
                })
            })
    }
}

impl<V> TaggedNode for InnerNode256<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Node256;
}

/// Node that contains a single leaf value.
#[derive(Debug, Clone)]
#[repr(C)]
pub struct LeafNode<V> {
    /// The common node fields.
    pub header: Header,
    /// The leaf value.
    pub value: V,
    /// The full key that the `value` was stored with.
    pub key: Box<[u8]>,
}

impl<V> LeafNode<V> {
    /// Create a new leaf node with the given value.
    pub fn new(key: Box<[u8]>, value: V) -> Self {
        LeafNode {
            value,
            key,
            header: Header {
                node_type: NodeType::Leaf,
                ..Header::default()
            },
        }
    }

    /// Check that the provided key is the same one as the stored key.
    pub fn matches_key(&self, possible_key: &[u8]) -> bool {
        self.key.as_ref().eq(possible_key)
    }
}

impl<V> TaggedNode for LeafNode<V> {
    type Value = V;

    const TYPE: NodeType = NodeType::Leaf;
}

#[cfg(test)]
mod tests;
