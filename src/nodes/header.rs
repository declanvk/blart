//! Different header type

use std::{fmt::Debug, marker::PhantomData};

use crate::{
    minimum_unchecked,
    rust_nightly_apis::{assume, likely},
    AsBytes, InnerNode, LeafNode, NodePtr,
};

/// The common header for all inner nodes
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(align(8))]
struct RawHeader<const NUM_PREFIX_BYTES: usize> {
    /// Number of children of this inner node. This field has no meaning for
    /// a leaf node.
    ///
    /// This needs to be a [`u16`], since a node 256 can hold up to 256 children
    /// if this was a [`u8`] (0-255) it would overflow when adding the last
    /// element
    num_children: u16,
    /// Number of bytes used by the prefix
    prefix_len: u32,
    /// The key prefix for this node.
    prefix: [u8; NUM_PREFIX_BYTES],
}

impl<const NUM_PREFIX_BYTES: usize> RawHeader<NUM_PREFIX_BYTES> {
    #[inline(always)]
    fn new(prefix: &[u8], prefix_len: usize) -> Self {
        let mut header = Self {
            num_children: 0,
            prefix_len: prefix_len as u32,
            prefix: [0; NUM_PREFIX_BYTES],
        };
        let len = prefix.len().min(NUM_PREFIX_BYTES);
        header.prefix[..len].copy_from_slice(&prefix[..len]);

        header
    }

    /// Create a new `Header` for an empty node.
    #[inline(always)]
    fn empty() -> Self {
        Self {
            num_children: 0,
            prefix_len: 0,
            prefix: [0; NUM_PREFIX_BYTES],
        }
    }

    /// Read the initialized portion of the prefix present in the header.
    #[inline(always)]
    fn read_prefix(&self) -> &[u8] {
        &self.prefix[0..self.capped_prefix_len()]
    }

    /// Get the number of bytes in the prefix.
    #[inline(always)]
    fn prefix_len(&self) -> usize {
        self.prefix_len as usize
    }

    /// Minimum between [`Self::prefix_len`] and [`NUM_PREFIX_BYTES`]
    #[inline(always)]
    fn capped_prefix_len(&self) -> usize {
        (self.prefix_len as usize).min(NUM_PREFIX_BYTES)
    }

    /// Return the number of children of this node.
    #[inline(always)]
    fn num_children(&self) -> usize {
        usize::from(self.num_children)
    }

    /// Left trim by `len`, copies the remaining data to the beging of the
    /// prefix
    ///
    /// # PANICS
    ///  - If `len` > length of the prefix
    #[inline(always)]
    fn ltrim_by(&mut self, len: usize) {
        self.prefix_len -= len as u32;

        let begin = len;
        let end = begin + self.capped_prefix_len();

        #[cfg_attr(not(feature = "nightly"), allow(unused_unsafe))]
        unsafe {
            // SAFETY: This function is called when mismatch happened and
            // we used the node to match the number of bytes,
            // by this we know that len < prefix len, but since we + 1,
            // to skip the key byte we have that len <= prefix len
            assume!(end <= self.prefix.len());

            // SAFETY: This is by construction end = begin + len
            assume!(begin <= end);
        }
        self.prefix.copy_within(begin..end, 0);
    }

    /// Set the length of the prefix to 0 and returns a copy of the
    /// prefix, length and capped length
    #[inline(always)]
    fn clear_prefix(&mut self) -> ([u8; NUM_PREFIX_BYTES], usize, usize) {
        let len = self.prefix_len();
        let capped_len = self.capped_prefix_len();
        self.prefix_len = 0;

        (self.prefix, len, capped_len)
    }

    /// Append `new` to the prefix and sums `new_len` to the prefix length
    #[inline(always)]
    fn push_prefix(&mut self, new: &[u8], new_len: usize) {
        let begin = self.capped_prefix_len();
        let end = (begin + new.len()).min(NUM_PREFIX_BYTES);
        let len = end - begin;
        self.prefix[begin..end].copy_from_slice(&new[..len]);
        self.prefix_len += new_len as u32;
    }

    /// Increments the number of children
    #[inline(always)]
    fn inc_num_children(&mut self) {
        self.num_children += 1;
    }

    /// Decrements the number of children
    #[inline(always)]
    fn dec_num_children(&mut self) {
        self.num_children -= 1;
    }
}

macro_rules! define_common_node_header_methods {
    () => {
        #[inline(always)]
        fn read_prefix(&self) -> &[u8] {
            &self.0.read_prefix()
        }

        #[inline(always)]
        fn prefix_len(&self) -> usize {
            self.0.prefix_len()
        }

        #[inline(always)]
        fn capped_prefix_len(&self) -> usize {
            self.0.capped_prefix_len()
        }

        #[inline(always)]
        fn num_children(&self) -> usize {
            self.0.num_children()
        }

        #[inline(always)]
        fn ltrim_by(&mut self, len: usize) {
            self.0.ltrim_by(len)
        }

        #[inline(always)]
        fn clear_prefix(&mut self) -> ([u8; NUM_PREFIX_BYTES], usize, usize) {
            self.0.clear_prefix()
        }

        #[inline(always)]
        fn inc_num_children(&mut self) {
            self.0.inc_num_children()
        }

        #[inline(always)]
        fn dec_num_children(&mut self) {
            self.0.dec_num_children()
        }

        #[inline(always)]
        fn push_prefix(&mut self, new: &[u8], new_len: usize) {
            self.0.push_prefix(new, new_len)
        }
    };
}

/// Specifies the behaviour of different headers types
pub trait NodeHeader<const NUM_PREFIX_BYTES: usize>: Debug + Clone + PartialEq + Eq {
    /// Create a new `Header` using
    /// `prefix` as the node prefix and
    /// `prefix_len` as the node prefix length and
    ///
    /// This is done because when a prefix mismatch happens
    /// the length of the mismatch can be grater or equal to
    /// prefix size, since we search for the first child of the
    /// node to recreate the prefix, that's why we don't use
    /// `prefix.len()` as the node prefix length
    fn new(prefix: &[u8], prefix_len: usize) -> Self;

    /// Create a new `Header` for an empty node.
    fn empty() -> Self;

    /// Read the initialized portion of the prefix present in the header.
    fn read_prefix(&self) -> &[u8];

    /// Get the number of bytes in the prefix.
    fn prefix_len(&self) -> usize;

    /// Minimum between [`NodeHeader::prefix_len`] and `NUM_PREFIX_BYTES`
    fn capped_prefix_len(&self) -> usize;

    /// Return the number of children of this node.
    fn num_children(&self) -> usize;

    /// Left trim by `len`, copies the remaining data to the beging of the
    /// prefix
    ///
    /// # PANICS
    ///  - If `len` > length of the prefix
    fn ltrim_by(&mut self, len: usize);

    /// Left trim by `len`, copies the remaining data to the beging of the
    /// prefix, in this case we use a leaf to achieve this, we also need the
    /// `depth` (a.k.a how many bytes of the leaf have already been used)
    fn ltrim_by_with_leaf<K: AsBytes, V, H: NodeHeader<NUM_PREFIX_BYTES>>(
        &mut self,
        len: usize,
        depth: usize,
        leaf_ptr: NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>,
    );

    /// Append `new` to the prefix and sums `new_len` to the prefix length
    fn push_prefix(&mut self, new: &[u8], new_len: usize);

    /// Set the length of the prefix to 0 and returns a copy of the
    /// prefix, length and capped length
    fn clear_prefix(&mut self) -> ([u8; NUM_PREFIX_BYTES], usize, usize);

    /// Increment the number of children in the header
    fn inc_num_children(&mut self);

    /// Decrement the number of children in the header
    fn dec_num_children(&mut self);

    /// Reads the prefix as a whole without capping it
    fn inner_read_full_prefix<'a, N: InnerNode<NUM_PREFIX_BYTES>>(
        &'a self,
        node: &'a N,
        current_depth: usize,
    ) -> (
        &'a [u8],
        Option<NodePtr<NUM_PREFIX_BYTES, LeafNode<N::Key, N::Value, NUM_PREFIX_BYTES, N::Header>>>,
    );
}

/// This header should be used with variable length keys
/// Since the key can be reconstructed from a leaf
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct VariableKeyHeader<const NUM_PREFIX_BYTES: usize>(RawHeader<NUM_PREFIX_BYTES>);

impl<const NUM_PREFIX_BYTES: usize> NodeHeader<NUM_PREFIX_BYTES>
    for VariableKeyHeader<NUM_PREFIX_BYTES>
{
    define_common_node_header_methods!();

    #[inline(always)]
    fn new(prefix: &[u8], prefix_len: usize) -> Self {
        Self(RawHeader::new(prefix, prefix_len))
    }

    #[inline(always)]
    fn empty() -> Self {
        Self(RawHeader::empty())
    }

    #[inline(always)]
    fn ltrim_by_with_leaf<K: AsBytes, V, H: NodeHeader<NUM_PREFIX_BYTES>>(
        &mut self,
        len: usize,
        depth: usize,
        leaf_ptr: NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>,
    ) {
        self.0.prefix_len -= len as u32;

        // SAFETY: Since have a mutable reference
        // is safe to create a shared reference from it
        let leaf_key = unsafe { leaf_ptr.as_key_ref().as_bytes() };

        let begin = depth + len;
        let end = begin + self.capped_prefix_len();
        let len = end - begin;

        #[cfg_attr(not(feature = "nightly"), allow(unused_unsafe))]
        unsafe {
            // SAFETY: This function is called a mismatch happened and
            // we used the leaf to match the number of matching bytes,
            // by this we know that len < prefix len, but since we + 1,
            // to skip the key byte we have that len <= prefix len
            assume!(end <= leaf_key.len());

            // SAFETY: This is by construction end = begin + len
            assume!(begin <= end);
        }

        let leaf_key = &leaf_key[begin..end];
        let leaf_key = &leaf_key[..leaf_key.len().min(NUM_PREFIX_BYTES)];
        self.0.prefix[..len.min(NUM_PREFIX_BYTES)].copy_from_slice(leaf_key)
    }

    #[inline(always)]
    fn inner_read_full_prefix<'a, N: InnerNode<NUM_PREFIX_BYTES>>(
        &'a self,
        node: &'a N,
        current_depth: usize,
    ) -> (
        &'a [u8],
        Option<NodePtr<NUM_PREFIX_BYTES, LeafNode<N::Key, N::Value, NUM_PREFIX_BYTES, N::Header>>>,
    ) {
        let len = self.prefix_len();
        if likely!(len <= NUM_PREFIX_BYTES) {
            (self.read_prefix(), None)
        } else {
            // SAFETY: By construction a InnerNode, must have >= 1 childs, this
            // is even more strict since in the case of 1 child the node can be
            // collapsed, so a InnserNode must have >= 2 childs, so it's safe
            // to search for the minium. And the same applies to the `minimum_unchecked`
            // function
            let (_, min_child) = node.min();
            let leaf_ptr = unsafe { minimum_unchecked(min_child) };

            // SAFETY: Since have a shared reference
            // is safe to create a shared reference from it
            let leaf = unsafe { leaf_ptr.as_ref() };
            let leaf = leaf.key_ref().as_bytes();

            #[cfg_attr(not(feature = "nightly"), allow(unused_unsafe))]
            unsafe {
                // SAFETY: Since we are iterating the key and prefixes, we
                // expect that the depth never exceeds the key len.
                // Because if this happens we ran out of bytes in the key to match
                // and the whole process should be already finished
                assume!(current_depth <= leaf.len());

                // SAFETY: By the construction of the prefix we know that this is inbounds
                // since the prefix len guarantees it to us
                assume!(current_depth + len <= leaf.len());

                // SAFETY: This can't overflow since len comes from a u32
                assume!(current_depth <= current_depth + len);
            }
            let leaf = &leaf[current_depth..(current_depth + len)];
            (leaf, Some(leaf_ptr))
        }
    }
}

/// This header should be used with **fixed** length keys
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct FixedKeyHeader<const NUM_PREFIX_BYTES: usize, K1: Copy + Eq + Debug + Sized>(
    RawHeader<NUM_PREFIX_BYTES>,
    PhantomData<K1>,
);

impl<const NUM_PREFIX_BYTES: usize, K1: Copy + Eq + Debug + Sized> NodeHeader<NUM_PREFIX_BYTES>
    for FixedKeyHeader<NUM_PREFIX_BYTES, K1>
{
    define_common_node_header_methods!();

    #[inline(always)]
    fn new(prefix: &[u8], prefix_len: usize) -> Self {
        Self(RawHeader::new(prefix, prefix_len), PhantomData)
    }

    #[inline(always)]
    fn empty() -> Self {
        Self(RawHeader::empty(), PhantomData)
    }

    #[inline(always)]
    fn ltrim_by_with_leaf<K: AsBytes, V, H: NodeHeader<NUM_PREFIX_BYTES>>(
        &mut self,
        _len: usize,
        _depth: usize,
        _leaf_ptr: NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>,
    ) {
        debug_assert!(
            false,
            "FixedKeyHeader::ltrim_by_with_leaf should never be called"
        );

        // SAFETY: By the definition of the FixedKeyHeader we know that the maximum
        // key legnth is <= NUM_PREFIX_BYTES, so we will never have to reconstruct
        // the key from a leaf, so it's safe to assume that this function is never called
        #[cfg(not(debug_assertions))]
        unsafe {
            std::hint::unreachable_unchecked()
        };
    }

    #[inline(always)]
    fn inner_read_full_prefix<'a, N: InnerNode<NUM_PREFIX_BYTES>>(
        &'a self,
        _node: &'a N,
        _current_depth: usize,
    ) -> (
        &'a [u8],
        Option<NodePtr<NUM_PREFIX_BYTES, LeafNode<N::Key, N::Value, NUM_PREFIX_BYTES, N::Header>>>,
    ) {
        debug_assert!(
            self.prefix_len() <= NUM_PREFIX_BYTES,
            "Current prefix length should always be {} <= {} in a FixedKeyHeader",
            self.prefix_len(),
            NUM_PREFIX_BYTES
        );
        (self.read_prefix(), None)
    }
}
