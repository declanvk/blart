//! Trie node representation

use std::{
    cmp,
    error::Error,
    fmt,
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
    /// The lower and upper bounds on the number of child nodes that this
    /// NodeType can have.
    pub const fn capacity_bounds(self) -> (usize, usize) {
        match self {
            NodeType::Node4 => (2, 4),
            NodeType::Node16 => (5, 16),
            NodeType::Node48 => (17, 48),
            NodeType::Node256 => (49, 256),
            NodeType::Leaf => (0, 0),
        }
    }
}

/// The common header for all inner nodes
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct Header {
    /// The size (in bytes) of the prefix stored in the header
    pub prefix_size: u32,
    /// Number of children this internal node points to
    pub num_children: u8,
    /// The type of representation for this current node
    pub node_type: NodeType,
    /// The key prefix for this node.
    ///
    /// Only the first `prefix_size` bytes are guaranteed to be initialized.
    pub prefix: [MaybeUninit<u8>; NUM_PREFIX_BYTES],
}

impl Header {
    /// Create a new `Header` for an empty node.
    pub fn empty() -> Self {
        Header {
            prefix_size: 0,
            num_children: 0,
            node_type: NodeType::Node4,
            prefix: MaybeUninit::uninit_array(),
        }
    }

    /// Write a new prefix to this header, updating the existing prefix if
    /// present.
    pub fn write_prefix(&mut self, new_bytes: &[u8]) {
        let prefix_size = usize::try_from(self.prefix_size).unwrap();
        if prefix_size < self.prefix.len() {
            // There is still space left in the actual prefix storage
            let bytes_to_write = cmp::min(new_bytes.len(), self.prefix.len() - prefix_size);

            MaybeUninit::write_slice(
                &mut self.prefix[prefix_size..(prefix_size + bytes_to_write)],
                &new_bytes[..bytes_to_write],
            );
        }
        self.prefix_size += u32::try_from(new_bytes.len()).unwrap();
    }

    /// The number of bytes from the start of the prefix.
    ///
    /// # Panics
    ///
    ///  - Panics if the starting point is greater than or equal to the prefix
    ///    size
    ///  - Panics if the prefix size is greater than NUM_PREFIX_BYTES (there are
    ///    bytes represented by the prefix that are not present in memory).
    pub fn ltrim_prefix(&mut self, num_bytes: usize) {
        assert!(
            num_bytes <= usize::try_from(self.prefix_size).unwrap(),
            "Number of bytes to trim [{}] must be less than or equal to prefix size [{}].",
            num_bytes,
            self.prefix_size
        );
        assert!(
            usize::try_from(self.prefix_size).unwrap() <= NUM_PREFIX_BYTES,
            "Cannot trim prefix when the prefix size [{}] is greater than the number of stored \
             bytes [{}].",
            self.prefix_size,
            NUM_PREFIX_BYTES
        );

        self.prefix_size -= u32::try_from(num_bytes).unwrap();
        unsafe {
            // SAFETY:
            //   - self.prefix is valid for writes and aligned
            ptr::copy(
                self.prefix
                    .as_ptr()
                    .offset(isize::try_from(num_bytes).unwrap()),
                self.prefix.as_mut_ptr(),
                usize::try_from(self.prefix_size).unwrap(),
            )
        }
    }

    /// Read the initialized portion of the prefix present in the header.
    ///
    /// The `prefix_size` can be larger than the `read_prefix().len()` because
    /// only NUM_PREFIX_BYTES are stored.
    pub fn read_prefix(&self) -> &[u8] {
        // SAFETY: The array prefix with length `header.prefix_size` is guaranteed to
        // be initialized up to NUM_PREFIX_BYTES bytes (the max length of the array).
        unsafe {
            MaybeUninit::slice_assume_init_ref(
                &self.prefix[..cmp::min(NUM_PREFIX_BYTES, self.prefix_size as usize)],
            )
        }
    }

    /// Compares the compressed path of a node with the key and returns the
    /// number of equal bytes.
    pub fn match_prefix(&self, possible_key: &[u8]) -> u32 {
        let inited_prefix = self.read_prefix();

        let mut num_matching_bytes: u32 = 0;
        for index in 0..cmp::min(inited_prefix.len(), possible_key.len()) {
            if inited_prefix[index] != possible_key[index] {
                break;
            }

            num_matching_bytes += 1;
        }

        if usize::try_from(num_matching_bytes).unwrap() == NUM_PREFIX_BYTES
            && self.prefix_size > num_matching_bytes
        {
            // If we've matched the max number of bytes, but there are still more in the
            // conceptual prefix we just assume that the prefix matches and continue on.
            // This will be checked in the end by a final comparison vs the key stored
            // alongside the value
            cmp::min(self.prefix_size, u32::try_from(possible_key.len()).unwrap())
        } else {
            num_matching_bytes
        }
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct OpaqueNodePtr(NonNull<Header>);

impl OpaqueNodePtr {
    /// Return `true` if this Node_ pointer points to the specified concrete
    /// NodeType.
    pub fn is<N: TaggedNode>(&self) -> bool {
        // SAFETY: inner pointer is guaranteed not to be null by `NonNull` wrapper.
        unsafe { (*self.0.as_ptr()).node_type == N::TYPE }
    }

    /// Create a non-opaque node pointer that will eliminate future type
    /// assertions, if the type of the pointed node matches the given
    /// node type.
    pub fn cast<N: TaggedNode>(&self) -> Option<NodePtr<N>> {
        if self.is::<N>() {
            // SAFETY: This cast is safe because all Node_ types have `repr(C)`
            // and have the `Header` field first.
            Some(NodePtr(self.0.cast::<N>()))
        } else {
            None
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

    /// Acquires the underlying *mut pointer.
    pub fn to_ptr(self) -> *mut Header {
        self.0.as_ptr()
    }
}

/// A pointer to a Node{4,16,48,256}.
#[derive(Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct NodePtr<N: TaggedNode>(NonNull<N>);

impl<N: TaggedNode> NodePtr<N> {
    /// Create a safe pointer to a Node_.
    ///
    /// # Safety
    ///
    /// Given pointer must be non-null, aligned, and point to a valid value of
    /// N.
    pub unsafe fn new(ptr: *mut N) -> Self {
        NodePtr(NonNull::new_unchecked(ptr))
    }

    /// Cast node pointer back to an opaque version, losing type information
    pub fn to_opaque(self) -> OpaqueNodePtr {
        // SAFETY: This cast is safe because all Node_ types have `repr(C)`
        // and have the `Header` field first.
        OpaqueNodePtr(self.0.cast::<Header>())
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

    /// Acquires the underlying *mut pointer.
    pub fn to_ptr(self) -> *mut N {
        self.0.as_ptr()
    }
}

impl<N: TaggedNode> Clone for NodePtr<N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
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

/// All nodes which contain a runtime tag that validates their type.
pub trait TaggedNode {
    /// The runtime type of the node.
    const TYPE: NodeType;
}

/// Node that references between 2 and 4 children
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct InnerNode4 {
    /// The common node fields.
    pub header: Header,
    /// An array that contains single key bytes in the same index as the
    /// `child_pointers` array contains the matching child tree.
    ///
    /// This array will only be initialized for the first `header.num_children`
    /// values.
    pub keys: [MaybeUninit<u8>; 4],
    /// An array that contains the child data.
    ///
    /// This array will only be initialized for the first`header.num_children`
    /// values.
    pub child_pointers: [MaybeUninit<OpaqueNodePtr>; 4],
}

impl InnerNode4 {
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
    pub fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr> {
        // SAFETY: The array prefix with length `header.num_children` is guaranteed to
        // be initialized
        let keys = unsafe {
            MaybeUninit::slice_assume_init_ref(&self.keys[0..self.header.num_children as usize])
        };

        for (child_index, key) in keys.iter().enumerate() {
            if *key == key_fragment {
                // SAFETY: The `child_pointers` array is initialized to a matching length with
                // the `keys` array.
                let child = unsafe { MaybeUninit::assume_init(self.child_pointers[child_index]) };

                return Some(child);
            }
        }

        return None;
    }

    /// Write a new child pointer with key fragment to this inner node.
    ///
    /// # Panics
    ///
    /// Panics when the node is full.
    pub fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr) {
        let child_index = self.header.num_children;
        self.keys[usize::from(child_index)].write(key_fragment);
        self.child_pointers[usize::from(child_index)].write(child_pointer);
        self.header.num_children += 1;
    }
}

impl TaggedNode for InnerNode4 {
    const TYPE: NodeType = NodeType::Node4;
}

/// Node that references between 5 and 16 children
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct InnerNode16 {
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
    pub child_pointers: [MaybeUninit<OpaqueNodePtr>; 16],
}

impl InnerNode16 {
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
    pub fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr> {
        // SAFETY: The array prefix with length `header.num_children` is guaranteed to
        // be initialized
        unsafe {
            MaybeUninit::slice_assume_init_ref(&self.keys[0..self.header.num_children as usize])
        }
        .binary_search(&key_fragment)
        .map(|child_index| {
            // SAFETY: The `child_pointers` array is initialized to a matching length with
            // the `keys` array.
            unsafe { MaybeUninit::assume_init(self.child_pointers[child_index]) }
        })
        .ok()
    }

    /// Write a new child pointer with key fragment to this inner node.
    ///
    /// # Panics
    ///
    /// Panics when the node is full.
    pub fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr) {
        let child_index = self.header.num_children;
        self.keys[usize::from(child_index)].write(key_fragment);
        self.child_pointers[usize::from(child_index)].write(child_pointer);
        self.header.num_children += 1;
    }
}

impl TaggedNode for InnerNode16 {
    const TYPE: NodeType = NodeType::Node16;
}

/// A restricted index only valid from 0 to 47.
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(transparent)]
pub struct Node48Index(u8);

impl Node48Index {
    /// A placeholder index value that indicates
    pub const EMPTY: Self = Node48Index(255);
}

impl From<Node48Index> for u8 {
    fn from(src: Node48Index) -> Self {
        src.0
    }
}

impl TryFrom<u8> for Node48Index {
    type Error = TryFromByteError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value < 48 {
            Ok(Node48Index(value))
        } else {
            Err(TryFromByteError(value))
        }
    }
}

/// The error type returned when attempting to construct an index outside the
/// accepted range of a Node48Index.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TryFromByteError(u8);

impl fmt::Display for TryFromByteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Input value [{}] is outside the allowed value range of Node48Index.",
            self.0
        )
    }
}

impl Error for TryFromByteError {}

/// Node that references between 17 and 49 children
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct InnerNode48 {
    /// The common node fields.
    pub header: Header,
    /// An array that maps key bytes (as the index) to the index value in the
    /// `child_pointers` array.
    ///
    /// All the `child_indices` values are guaranteed to be `Node48Index::EMPTY`
    /// when the node is constructed.
    pub child_indices: [Node48Index; 256],
    /// For each element in this array, it is assumed to be initialized if there
    /// is a index in the `child_indices` array that points to it
    pub child_pointers: [MaybeUninit<OpaqueNodePtr>; 48],
}

impl InnerNode48 {
    /// Create an empty `Node48`.
    pub fn empty() -> Self {
        InnerNode48 {
            header: Header {
                node_type: NodeType::Node48,
                ..Header::default()
            },
            child_indices: [Node48Index::EMPTY; 256],
            child_pointers: MaybeUninit::uninit_array(),
        }
    }

    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    pub fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr> {
        let index = &self.child_indices[key_fragment as usize];
        if *index != Node48Index::EMPTY {
            let child_index = usize::from(u8::from(*index));
            // SAFETY: This type requires all slots in the `self.child_pointers` array to be
            // initialized if they are pointed to by a non-Node48Index::EMPTY child index.
            let child = unsafe { MaybeUninit::assume_init(self.child_pointers[child_index]) };
            Some(child)
        } else {
            None
        }
    }

    /// Write a new child pointer with key fragment to this inner node.
    ///
    /// # Panics
    ///
    /// Panics when the node is full.
    pub fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr) {
        let child_index = self.header.num_children;
        self.child_indices[usize::from(key_fragment)] = Node48Index::try_from(child_index).unwrap();
        self.child_pointers[usize::from(child_index)].write(child_pointer);
        self.header.num_children += 1;
    }
}

impl TaggedNode for InnerNode48 {
    const TYPE: NodeType = NodeType::Node48;
}

/// Node that references between 49 and 256 children
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct InnerNode256 {
    /// The common node fields.
    pub header: Header,
    /// An array that directly maps a key byte (as index) to a child node.
    pub child_pointers: [Option<OpaqueNodePtr>; 256],
}

impl InnerNode256 {
    /// Create an empty `Node48`.
    pub fn empty() -> Self {
        InnerNode256 {
            header: Header {
                node_type: NodeType::Node256,
                ..Header::default()
            },
            child_pointers: [None; 256],
        }
    }
}

impl InnerNode256 {
    /// Search through this node for a child node that corresponds to the given
    /// key fragment.
    pub fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr> {
        self.child_pointers[key_fragment as usize]
    }

    /// Write a new child pointer with key fragment to this inner node.
    pub fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr) {
        self.child_pointers[usize::from(key_fragment)] = Some(child_pointer);
        self.header.num_children += 1;
    }
}

impl TaggedNode for InnerNode256 {
    const TYPE: NodeType = NodeType::Node256;
}

/// Node that contains a single leaf value.
#[derive(Debug)]
#[repr(C)]
pub struct LeafNode<T> {
    /// The common node fields.
    pub header: Header,
    /// The leaf value.
    pub value: T,
    /// The full key that the `value` was stored with.
    pub key: Vec<u8>,
}

impl<T> LeafNode<T> {
    /// Create a new leaf node with the given value.
    pub fn new(key: impl Into<Vec<u8>>, value: T) -> Self {
        LeafNode {
            value,
            key: key.into(),
            header: Header {
                node_type: NodeType::Leaf,
                ..Header::default()
            },
        }
    }

    /// Check that the provided key is the same one as the stored key.
    pub fn matches_key(&self, possible_key: &[u8]) -> bool {
        self.key.eq(&possible_key)
    }
}

impl<T> TaggedNode for LeafNode<T> {
    const TYPE: NodeType = NodeType::Leaf;
}

#[cfg(test)]
mod tests {
    use std::mem;

    use super::*;

    #[test]
    fn opaque_node_ptr_is_correct() {
        let mut n4 = InnerNode4::empty();
        let mut n16 = InnerNode16::empty();
        let mut n48 = InnerNode48::empty();
        let mut n256 = InnerNode256::empty();

        let n4_ptr = NodePtr::from(&mut n4);
        let n16_ptr = NodePtr::from(&mut n16);
        let n48_ptr = NodePtr::from(&mut n48);
        let n256_ptr = NodePtr::from(&mut n256);

        let opaque_n4_ptr = n4_ptr.to_opaque();
        let opaque_n16_ptr = n16_ptr.to_opaque();
        let opaque_n48_ptr = n48_ptr.to_opaque();
        let opaque_n256_ptr = n256_ptr.to_opaque();

        assert!(opaque_n4_ptr.is::<InnerNode4>());
        assert!(opaque_n16_ptr.is::<InnerNode16>());
        assert!(opaque_n48_ptr.is::<InnerNode48>());
        assert!(opaque_n256_ptr.is::<InnerNode256>());
    }

    #[test]
    fn node_sizes() {
        assert_eq!(mem::size_of::<Header>(), 16);
        assert_eq!(mem::size_of::<InnerNode4>(), 56);
        assert_eq!(mem::size_of::<InnerNode16>(), 160);
        assert_eq!(mem::size_of::<InnerNode48>(), 656);
        assert_eq!(mem::size_of::<InnerNode256>(), 2064);
    }

    #[test]
    fn node4_lookup() {
        let mut n = InnerNode4::empty();
        let mut l1 = LeafNode::new(vec![], ());
        let mut l2 = LeafNode::new(vec![], ());
        let mut l3 = LeafNode::new(vec![], ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        assert!(n.lookup_child(123).is_none());

        n.header.num_children = 3;
        n.keys[0].write(3);
        n.keys[1].write(123);
        n.keys[2].write(1);

        n.child_pointers[0].write(l1_ptr);
        n.child_pointers[1].write(l2_ptr);
        n.child_pointers[2].write(l3_ptr);

        assert_eq!(n.lookup_child(123), Some(l2_ptr));
    }

    #[test]
    fn node16_lookup() {
        let mut n = InnerNode16::empty();
        let mut l1 = LeafNode::new(&[][..], ());
        let mut l2 = LeafNode::new(&[][..], ());
        let mut l3 = LeafNode::new(&[][..], ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        assert!(n.lookup_child(123).is_none());

        n.header.num_children = 3;
        n.keys[0].write(3);
        n.keys[1].write(123);
        n.keys[2].write(1);

        n.child_pointers[0].write(l1_ptr);
        n.child_pointers[1].write(l2_ptr);
        n.child_pointers[2].write(l3_ptr);

        assert_eq!(n.lookup_child(123), Some(l2_ptr));
    }

    #[test]
    fn node48_lookup() {
        let mut n = InnerNode48::empty();
        let mut l1 = LeafNode::new(&[][..], ());
        let mut l2 = LeafNode::new(&[][..], ());
        let mut l3 = LeafNode::new(&[][..], ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        assert!(n.lookup_child(123).is_none());

        n.header.num_children = 3;

        n.child_indices[1] = 2.try_into().unwrap();
        n.child_indices[3] = 0.try_into().unwrap();
        n.child_indices[123] = 1.try_into().unwrap();

        n.child_pointers[0].write(l1_ptr);
        n.child_pointers[1].write(l2_ptr);
        n.child_pointers[2].write(l3_ptr);

        assert_eq!(n.lookup_child(123), Some(l2_ptr));
    }

    #[test]
    fn node256_lookup() {
        let mut n = InnerNode256::empty();
        let mut l1 = LeafNode::new(&[][..], ());
        let mut l2 = LeafNode::new(&[][..], ());
        let mut l3 = LeafNode::new(&[][..], ());
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();

        assert!(n.lookup_child(123).is_none());

        n.header.num_children = 3;

        n.child_pointers[1] = Some(l1_ptr);
        n.child_pointers[123] = Some(l2_ptr);
        n.child_pointers[3] = Some(l3_ptr);

        assert_eq!(n.lookup_child(123), Some(l2_ptr));
    }

    #[test]
    fn header_read_write_prefix() {
        let mut h = Header::empty();

        assert_eq!(h.prefix_size, 0);
        assert_eq!(h.read_prefix(), &[]);

        h.write_prefix(&[1, 2, 3]);

        assert_eq!(h.prefix_size, 3);
        assert_eq!(h.read_prefix(), &[1, 2, 3]);

        h.write_prefix(&[4, 5, 6]);

        assert_eq!(h.prefix_size, 6);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6]);

        h.write_prefix(&[7, 8]);

        assert_eq!(h.prefix_size, 8);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);

        h.write_prefix(&[9, 10, 11, 12]);

        assert_eq!(h.prefix_size, 12);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);

        h.write_prefix(&[]);

        assert_eq!(h.prefix_size, 12);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    }

    #[test]
    fn header_check_prefix() {
        let mut h = Header::empty();

        h.write_prefix(&[1, 2, 3]);

        assert_eq!(h.match_prefix(&[1, 2, 3]), 3);
        assert_eq!(h.match_prefix(&[0, 1, 2]), 0);
        assert_eq!(h.match_prefix(&[1, 2]), 2);
        assert_eq!(h.match_prefix(&[]), 0);

        h.write_prefix(&[4, 5, 6, 7, 8, 9, 10, 11, 12]);

        assert_eq!(h.match_prefix(&[1, 2, 3]), 3);
        assert_eq!(h.match_prefix(&[0, 1, 2]), 0);
        assert_eq!(h.match_prefix(&[1, 2]), 2);
        assert_eq!(h.match_prefix(&[]), 0);

        assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]), 8);
        assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]), 12);
        assert_eq!(
            h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]),
            12
        );
        assert_eq!(
            h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 100, 200, 254, 255]),
            12
        );
    }

    #[test]
    fn header_delete_prefix() {
        let mut h = Header::empty();
        h.write_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_size, 8);

        h.ltrim_prefix(0);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_size, 8);

        h.ltrim_prefix(3);
        assert_eq!(h.read_prefix(), &[4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_size, 5);

        h.ltrim_prefix(1);
        assert_eq!(h.read_prefix(), &[5, 6, 7, 8]);
        assert_eq!(h.prefix_size, 4);

        h.ltrim_prefix(4);
        assert_eq!(h.read_prefix(), &[]);
        assert_eq!(h.prefix_size, 0);
    }

    #[test]
    #[should_panic]
    fn header_ltrim_prefix_too_many_bytes_panic() {
        let mut h = Header::empty();
        h.write_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_size, 8);

        h.ltrim_prefix(10);
    }

    #[test]
    #[should_panic]
    fn header_ltrim_prefix_non_stored_bytes_panic() {
        let mut h = Header::empty();
        h.write_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_size, 8);

        h.ltrim_prefix(0);
    }
}
