use crate::{
    rust_nightly_apis::maybe_uninit_uninit_array, AsBytes, Header, InnerNode, InnerNode48, Node,
    NodePtr, NodeType, OpaqueNodePtr, RestrictedNodeIndex,
};
use std::{
    fmt,
    iter::{Enumerate, FusedIterator},
    slice::Iter,
};

#[cfg(feature = "nightly")]
use std::{
    iter::FilterMap,
    simd::{cmp::SimdPartialEq, usizex64},
};

/// Node that references between 49 and 256 children
#[repr(C, align(8))]
pub struct InnerNode256<K: AsBytes, V, const PREFIX_LEN: usize> {
    /// The common node fields.
    pub header: Header<PREFIX_LEN>,
    /// An array that directly maps a key byte (as index) to a child node.
    pub child_pointers: [Option<OpaqueNodePtr<K, V, PREFIX_LEN>>; 256],
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> fmt::Debug for InnerNode256<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InnerNode256")
            .field("header", &self.header)
            .field("child_pointers", &self.child_pointers)
            .finish()
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> Clone for InnerNode256<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        Self {
            header: self.header.clone(),
            child_pointers: self.child_pointers,
        }
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> Node<PREFIX_LEN> for InnerNode256<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Node256;
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> InnerNode<PREFIX_LEN>
    for InnerNode256<K, V, PREFIX_LEN>
{
    type GrownNode = Self;
    #[cfg(not(feature = "nightly"))]
    type Iter<'a> = Node256Iter<'a, K, V, PREFIX_LEN> where Self: 'a;
    #[cfg(feature = "nightly")]
    type Iter<'a> = FilterMap<Enumerate<Iter<'a, Option<OpaqueNodePtr<K, V, PREFIX_LEN>>>>, impl FnMut((usize, &'a Option<OpaqueNodePtr<K, V, PREFIX_LEN>>)) -> Option<(u8, OpaqueNodePtr<K, V, PREFIX_LEN>)>> where Self: 'a;
    type ShrunkNode = InnerNode48<K, V, PREFIX_LEN>;

    fn header(&self) -> &Header<PREFIX_LEN> {
        &self.header
    }

    fn from_header(header: Header<PREFIX_LEN>) -> Self {
        InnerNode256 {
            header,
            child_pointers: [None; 256],
        }
    }

    fn lookup_child(&self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        self.child_pointers[usize::from(key_fragment)]
    }

    fn write_child(&mut self, key_fragment: u8, child_pointer: OpaqueNodePtr<K, V, PREFIX_LEN>) {
        let key_fragment_idx = usize::from(key_fragment);
        let existing_pointer = self.child_pointers[key_fragment_idx];
        self.child_pointers[key_fragment_idx] = Some(child_pointer);
        if existing_pointer.is_none() {
            self.header.inc_num_children();
        }
    }

    fn remove_child(&mut self, key_fragment: u8) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
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
            Node256Iter {
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
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        use crate::rust_nightly_apis::assume;

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
            // at least one inner child, it's guarantee to be in bounds
            assume!(key < self.child_pointers.len());
        }

        // SAFETY: Covered by the containing function
        (key as u8, unsafe {
            self.child_pointers[key].unwrap_unchecked()
        })
    }

    #[cfg(not(feature = "nightly"))]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        for (key, child_pointer) in self.child_pointers.iter().enumerate() {
            match child_pointer {
                Some(child_pointer) => return (key as u8, *child_pointer),
                None => continue,
            }
        }
        unreachable!()
    }

    #[cfg(feature = "nightly")]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        use crate::rust_nightly_apis::assume;

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

        // SAFETY: covered by the containing function
        (key as u8, unsafe {
            self.child_pointers[key].unwrap_unchecked()
        })
    }

    #[cfg(not(feature = "nightly"))]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PREFIX_LEN>) {
        for (key, child_pointer) in self.child_pointers.iter().enumerate().rev() {
            match child_pointer {
                Some(child_pointer) => return (key as u8, *child_pointer),
                None => continue,
            }
        }
        unreachable!()
    }

    #[inline(always)]
    fn deep_clone(&self) -> NodePtr<PREFIX_LEN, Self>
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

/// TODO
#[cfg(not(feature = "nightly"))]
pub struct Node256Iter<'a, K: AsBytes, V, const PREFIX_LEN: usize> {
    pub(crate) it: Enumerate<Iter<'a, Option<OpaqueNodePtr<K, V, PREFIX_LEN>>>>,
}

#[cfg(not(feature = "nightly"))]
impl<'a, K: AsBytes, V, const PREFIX_LEN: usize> Iterator for Node256Iter<'a, K, V, PREFIX_LEN> {
    type Item = (u8, OpaqueNodePtr<K, V, PREFIX_LEN>);

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

#[cfg(not(feature = "nightly"))]
impl<'a, K: AsBytes, V, const PREFIX_LEN: usize> DoubleEndedIterator
    for Node256Iter<'a, K, V, PREFIX_LEN>
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

#[cfg(not(feature = "nightly"))]
impl<'a, K: AsBytes, V, const PREFIX_LEN: usize> FusedIterator
    for Node256Iter<'a, K, V, PREFIX_LEN>
{
}
