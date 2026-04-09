//! This module contains definitions of pointers types used in the tree.

use core::{
    alloc::Layout,
    fmt,
    hash::Hash,
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ptr::{self, NonNull},
};

use crate::{
    allocator::{do_alloc, Allocator},
    raw::{
        Header, InnerNode16, InnerNode4, InnerNode48, InnerNodeDirect, LeafNode, Node, NodeType,
    },
    tagged_pointer::TaggedPointer,
};

/// A placeholder type that has the required amount of alignment.
///
/// An alignment of 8 gives us 3 unused bits in any pointer to this type.
#[derive(Debug)]
#[repr(align(8))]
pub(super) struct OpaqueValue;

/// An opaque pointer to a [`Node`].
///
/// Could be any one of the [`NodeType`]s, need to perform check on the runtime
/// type and then cast to a [`NodePtr`].
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
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
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
        let mut tagged_ptr = TaggedPointer::from(pointer.cast::<OpaqueValue>());
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
    #[inline]
    pub fn cast<N: Node<PREFIX_LEN>>(self) -> Option<NodePtr<PREFIX_LEN, N>> {
        if self.is::<N>() {
            Some(NodePtr(self.0.to_ptr().cast::<N>()))
        } else {
            None
        }
    }

    /// Retrieve the runtime node type information.
    #[inline]
    pub fn node_type(self) -> NodeType {
        // SAFETY: We know that we can convert the usize into a `NodeType` because
        // we have only stored `NodeType` values into this pointer
        unsafe { NodeType::from_u8(self.0.to_data() as u8) }
    }

    /// Get a mutable reference to the header, this doesn't check if the
    /// pointer is to an inner node.
    ///
    /// # Safety
    ///  - The pointer must be to a type which implements
    ///    [`InnerNode`][super::InnerNode].
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'h is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get accessed
    ///    (read or written) through any other pointer.
    pub(crate) unsafe fn header_mut_unchecked<'h>(self) -> &'h mut Header<PREFIX_LEN> {
        unsafe { self.0.to_ptr().cast::<Header<PREFIX_LEN>>().as_mut() }
    }

    /// Get a shared reference to the header, this doesn't check if the
    /// pointer is to an inner node.
    ///
    /// # Safety
    ///  - The pointer must be to a type which implements
    ///    [`InnerNode`][super::InnerNode].
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'h is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not be mutated
    ///    through any other pointer.
    pub(crate) unsafe fn header_ref_unchecked<'h>(self) -> &'h Header<PREFIX_LEN> {
        unsafe { self.0.to_ptr().cast::<Header<PREFIX_LEN>>().as_ref() }
    }
}

macro_rules! impl_concrete_node_ptr {
    ($($variant:ident $node_ty:ty;)+) => {
        impl<K, V, const PREFIX_LEN: usize> OpaqueNodePtr<K, V, PREFIX_LEN> {
            /// Cast this opaque pointer type an enum that contains a pointer to the
            /// concrete node type.
            pub fn to_node_ptr(self) -> ConcreteNodePtr<K, V, PREFIX_LEN> {
                match self.node_type() {
                    $(
                        NodeType::$variant => {
                            ConcreteNodePtr::$variant(NodePtr(
                                self.0.to_ptr().cast::<$node_ty>(),
                            ))
                        },
                    )+
                    NodeType::Leaf => {
                        ConcreteNodePtr::LeafNode(NodePtr(
                            self.0.to_ptr().cast::<LeafNode<K, V, PREFIX_LEN>>(),
                        ))
                    },
                }
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
                    $(
                        | NodeType::$variant
                    )+ => unsafe { self.header_mut_unchecked() },
                    NodeType::Leaf => {
                        return None;
                    },
                };

                // SAFETY: The pointer is properly aligned and points to a initialized instance
                // of Header that is dereferenceable. The lifetime safety requirements are
                // passed up to the caller of this function.
                Some(header_ptr)
            }
        }

        /// An enum that encapsulates pointers to every type of [`Node`]
        pub enum ConcreteNodePtr<K, V, const PREFIX_LEN: usize> {
            $(
                #[doc = concat!("A pointer to a [`", stringify!($node_ty),"`]")]
                $variant(NodePtr<PREFIX_LEN, $node_ty>),
            )+
            /// A pointer to a [`LeafNode`]
            LeafNode(NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>),
        }

        macro_rules! match_concrete_node_ptr {
            (
                match ($match_e:expr) {
                    InnerNode($inner_node_i:ident) => $inner_node_e:expr,
                    LeafNode( $leaf_i:ident) => $leaf_e:expr,
                }
            ) => {
                match $match_e {
                    $(
                        ConcreteNodePtr::$variant($inner_node_i) => $inner_node_e,
                    )+
                    ConcreteNodePtr::LeafNode($leaf_i) => $leaf_e,
                }

            };
        }
        pub(crate) use match_concrete_node_ptr;

        impl<K, V, const PREFIX_LEN: usize> ConcreteNodePtr<K, V, PREFIX_LEN> {
            /// Convert this node pointer with node type information into an
            /// [`OpaqueNodePtr`] with the type information stored in the pointer.
            pub fn to_opaque(self) -> OpaqueNodePtr<K, V, PREFIX_LEN> {
                match_concrete_node_ptr! {
                    match (self) {
                        InnerNode(inner_ptr) => inner_ptr.to_opaque(),
                        LeafNode(leaf_ptr) => leaf_ptr.to_opaque(),
                    }
                }
            }
        }

        impl<K, V, const PREFIX_LEN: usize> fmt::Debug for ConcreteNodePtr<K, V, PREFIX_LEN> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    $(
                        Self::$variant(arg0) => f.debug_tuple(stringify!($variant)).field(arg0).finish(),
                    )+
                    Self::LeafNode(arg0) => f.debug_tuple("LeafNode").field(arg0).finish(),
                }
            }
        }

        impl<K, V, const PREFIX_LEN: usize> Copy for ConcreteNodePtr<K, V, PREFIX_LEN> {}

        impl<K, V, const PREFIX_LEN: usize> Clone for ConcreteNodePtr<K, V, PREFIX_LEN> {
            fn clone(&self) -> Self {
                *self
            }
        }

        $(
            impl<K, V, const PREFIX_LEN: usize> From<NodePtr<PREFIX_LEN, $node_ty>> for ConcreteNodePtr<K, V, PREFIX_LEN> {
                fn from(value: NodePtr<PREFIX_LEN, $node_ty>) -> Self {
                    ConcreteNodePtr::$variant(value)
                }
            }
        )+
        impl<K, V, const PREFIX_LEN: usize> From<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>> for ConcreteNodePtr<K, V, PREFIX_LEN> {
            fn from(value: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>) -> Self {
                ConcreteNodePtr::LeafNode(value)
            }
        }

        /// An enum that encapsulates pointers to every type of [`InnerNode`][super::InnerNode]
        pub enum ConcreteInnerNodePtr<K, V, const PREFIX_LEN: usize> {
            $(
                #[doc = concat!("A pointer to a [`", stringify!($node_ty),"`]")]
                $variant(NodePtr<PREFIX_LEN, $node_ty>),
            )+
        }

        macro_rules! match_concrete_inner_node_ptr {
            (
                match ($match_e:expr) {
                    InnerNode($inner_node_i:ident) => $inner_node_e:expr,
                }
            ) => {
                match $match_e {
                    $(
                        ConcreteInnerNodePtr::$variant($inner_node_i) => $inner_node_e,
                    )+
                }

            };
        }
        pub(crate) use match_concrete_inner_node_ptr;

        impl<K, V, const PREFIX_LEN: usize> Copy for ConcreteInnerNodePtr<K, V, PREFIX_LEN> {}

        impl<K, V, const PREFIX_LEN: usize> Clone for ConcreteInnerNodePtr<K, V, PREFIX_LEN> {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<K, V, const PREFIX_LEN: usize> fmt::Debug for ConcreteInnerNodePtr<K, V, PREFIX_LEN> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    $(
                        Self::$variant(arg0) => f.debug_tuple(stringify!($variant)).field(arg0).finish(),
                    )+
                }
            }
        }

        $(
            impl<K, V, const PREFIX_LEN: usize> From<NodePtr<PREFIX_LEN, $node_ty>> for ConcreteInnerNodePtr<K, V, PREFIX_LEN> {
                fn from(value: NodePtr<PREFIX_LEN, $node_ty>) -> Self {
                    ConcreteInnerNodePtr::$variant(value)
                }
            }
        )+

        impl<K, V, const PREFIX_LEN: usize> From<ConcreteInnerNodePtr<K, V, PREFIX_LEN>>
            for ConcreteNodePtr<K, V, PREFIX_LEN>
        {
            fn from(value: ConcreteInnerNodePtr<K, V, PREFIX_LEN>) -> Self {
                match value {
                    $(
                        ConcreteInnerNodePtr::$variant(inner_ptr) => ConcreteNodePtr::$variant(inner_ptr),
                    )+
                }
            }
        }
    };
}

impl_concrete_node_ptr!(
    Node4 InnerNode4<K, V, PREFIX_LEN>;
    Node16 InnerNode16<K, V, PREFIX_LEN>;
    Node48 InnerNode48<K, V, PREFIX_LEN>;
    Node256 InnerNodeDirect<K, V, PREFIX_LEN>;
);

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

    /// Allocate the given [`Node`] on the [`alloc::alloc::Global`] heap and
    /// return a [`NodePtr`] that wrap the raw pointer.
    ///
    /// # Panics
    /// This function will panic if the underlying allocate function returns an
    /// error.
    pub fn allocate_node_ptr(node: N, alloc: &impl Allocator) -> Self {
        let layout = Layout::new::<mem::MaybeUninit<N>>();
        let mut ptr: NonNull<mem::MaybeUninit<N>> =
            do_alloc(alloc, layout).expect("memory is infinite").cast();

        // SAFETY: The pointer from [`Box::into_raw`] is non-null, aligned, and valid
        // for reads and writes of the [`Node`] `N`.
        let ptr: NonNull<N> = unsafe {
            ptr.as_mut().write(node);
            ptr.cast()
        };

        NodePtr(ptr)
    }

    /// Deallocate a [`Node`] object created with the
    /// [`NodePtr::allocate_node_ptr`] function.
    ///
    /// # Safety
    ///  - This function can only be called once for a given node object.
    ///  - The given allocator must be the same one that was used in the call to
    ///    [`NodePtr::allocate_node_ptr`]
    #[must_use]
    pub unsafe fn deallocate_node_ptr(node: Self, alloc: &impl Allocator) -> N {
        // Read the value out onto the stack
        // SAFETY: From the constructors (`new`/`allocate_node_ptr`) we know that this
        // pointer will valid for reads, properly aligned, and initialized. We prevent
        // double drop by deallocating the memory in the following lines without ever
        // calling `drop_in_place`.
        let value = unsafe { ptr::read(node.0.as_ptr()) };

        let layout = Layout::new::<N>();
        if layout.size() != 0 {
            // If the value has a non-zero size (should be true of all nodes),
            // then deallocate the node object without dropping it (even) though
            // all `Node`s don't implement drop.

            // SAFETY:
            //  - The safety condition on this function requires that this allocator is the
            //    same one which initially allocated the memory block
            //  - The layout fits the block of memory because it was the same layout used to
            //    create the block (in `allocate_node_ptr`).
            unsafe {
                alloc.deallocate(node.0.cast(), layout);
            }
        }
        value
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

    /// Reads the Node from self without moving it. This leaves the memory
    /// in self unchanged.
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
    ///    (except inside `UnsafeCell`).
    pub unsafe fn as_ref<'a>(self) -> &'a N {
        // SAFETY: The pointer is properly aligned and points to a initialized instance
        // of N that is dereferenceable. The lifetime safety requirements are passed up
        // to the invoker of this function.
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
        // to the invoker of this function.
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
    ///    (except inside `UnsafeCell`).
    pub unsafe fn as_key_value_ref<'a>(self) -> (&'a K, &'a V) {
        // SAFETY: Safety requirements are covered by the containing function.
        let leaf = unsafe { self.as_ref() };

        (leaf.key_ref(), leaf.value_ref())
    }

    /// Returns a unique mutable reference to the key and value of the
    /// pointed to [`LeafNode`].
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

    /// Returns a unique mutable reference to the key and value of the
    /// pointed to [`LeafNode`].
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get mutated
    ///    (except inside `UnsafeCell`).
    pub unsafe fn as_key_ref<'a>(self) -> &'a K
    where
        V: 'a,
    {
        // SAFETY: Safety requirements are covered by the containing function.
        let leaf = unsafe { self.as_ref() };

        leaf.key_ref()
    }

    /// Returns a unique mutable reference to the key and value of the
    /// pointed to [`LeafNode`].
    ///
    /// # Safety
    ///  - You must enforce Rust’s aliasing rules, since the returned lifetime
    ///    'a is arbitrarily chosen and does not necessarily reflect the actual
    ///    lifetime of the data. In particular, for the duration of this
    ///    lifetime, the memory the pointer points to must not get mutated
    ///    (except inside `UnsafeCell`).
    pub unsafe fn as_value_ref<'a>(self) -> &'a V
    where
        K: 'a,
        V: 'a,
    {
        // SAFETY: Safety requirements are covered by the containing function.
        let leaf = unsafe { self.as_ref() };

        leaf.value_ref()
    }

    /// Returns a unique mutable reference to the key and value of the
    /// pointed to [`LeafNode`].
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
        unsafe { NodePtr::new(ptr::from_mut(node_ref)) }
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

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;

    use super::*;
    use crate::raw::InnerNodeCommon;

    #[test]
    fn opaque_node_ptr_is_correct() {
        let mut n4 = InnerNode4::<Box<[u8]>, usize, 16>::empty();
        let mut n16 = InnerNode16::<Box<[u8]>, usize, 16>::empty();
        let mut n48 = InnerNode48::<Box<[u8]>, usize, 16>::empty();
        let mut n256 = InnerNodeDirect::<Box<[u8]>, usize, 16>::empty();

        let n4_ptr = NodePtr::from(&mut n4).to_opaque();
        let n16_ptr = NodePtr::from(&mut n16).to_opaque();
        let n48_ptr = NodePtr::from(&mut n48).to_opaque();
        let n256_ptr = NodePtr::from(&mut n256).to_opaque();

        assert!(n4_ptr.is::<InnerNode4<Box<[u8]>, usize, 16>>());
        assert!(n16_ptr.is::<InnerNode16<Box<[u8]>, usize, 16>>());
        assert!(n48_ptr.is::<InnerNode48<Box<[u8]>, usize, 16>>());
        assert!(n256_ptr.is::<InnerNodeDirect<Box<[u8]>, usize, 16>>());
    }
}
