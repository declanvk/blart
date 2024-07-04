//! Different header type

use std::fmt::Debug;

use crate::{
    minimum_unchecked,
    rust_nightly_apis::{assume, likely},
    AsBytes, InnerNode, LeafNode, NodePtr,
};

/// The common header for all inner nodes
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(align(8))]
pub struct Header<const PREFIX_LEN: usize> {
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
    prefix: [u8; PREFIX_LEN],
}

impl<const PREFIX_LEN: usize> Header<PREFIX_LEN> {
    #[inline(always)]
    pub fn new(prefix: &[u8], prefix_len: usize) -> Self {
        let mut header = Self {
            num_children: 0,
            prefix_len: prefix_len as u32,
            prefix: [0; PREFIX_LEN],
        };
        let len = prefix.len().min(PREFIX_LEN);
        header.prefix[..len].copy_from_slice(&prefix[..len]);

        header
    }

    /// Create a new `Header` for an empty node.
    #[inline(always)]
    pub fn empty() -> Self {
        Self {
            num_children: 0,
            prefix_len: 0,
            prefix: [0; PREFIX_LEN],
        }
    }

    /// Read the initialized portion of the prefix present in the header.
    #[inline(always)]
    pub fn read_prefix(&self) -> &[u8] {
        &self.prefix[0..self.capped_prefix_len()]
    }

    /// Get the number of bytes in the prefix.
    #[inline(always)]
    pub fn prefix_len(&self) -> usize {
        self.prefix_len as usize
    }

    /// Minimum between [`Self::prefix_len`] and [`PREFIX_LEN`]
    #[inline(always)]
    pub fn capped_prefix_len(&self) -> usize {
        (self.prefix_len as usize).min(PREFIX_LEN)
    }

    /// Return the number of children of this node.
    #[inline(always)]
    pub fn num_children(&self) -> usize {
        usize::from(self.num_children)
    }

    /// Left trim by `len`, copies the remaining data to the beging of the
    /// prefix
    ///
    /// # Panics
    ///  - If `len` > length of the prefix
    #[inline(always)]
    pub fn ltrim_by(&mut self, len: usize) {
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
    pub fn clear_prefix(&mut self) -> ([u8; PREFIX_LEN], usize, usize) {
        let len = self.prefix_len();
        let capped_len = self.capped_prefix_len();
        self.prefix_len = 0;

        (self.prefix, len, capped_len)
    }

    /// Append `new` to the prefix and sums `new_len` to the prefix length
    #[inline(always)]
    pub fn push_prefix(&mut self, new: &[u8], new_len: usize) {
        let begin = self.capped_prefix_len();
        let end = (begin + new.len()).min(PREFIX_LEN);
        let len = end - begin;
        self.prefix[begin..end].copy_from_slice(&new[..len]);
        self.prefix_len += new_len as u32;
    }

    /// Increments the number of children
    #[inline(always)]
    pub fn inc_num_children(&mut self) {
        self.num_children += 1;
    }

    /// Decrements the number of children
    #[inline(always)]
    pub fn dec_num_children(&mut self) {
        self.num_children -= 1;
    }

    #[inline(always)]
    pub fn ltrim_by_with_leaf<K: AsBytes, V>(
        &mut self,
        len: usize,
        depth: usize,
        leaf_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    ) {
        self.prefix_len -= len as u32;

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
        let leaf_key = &leaf_key[..leaf_key.len().min(PREFIX_LEN)];
        self.prefix[..len.min(PREFIX_LEN)].copy_from_slice(leaf_key)
    }

    #[inline(always)]
    pub fn inner_read_full_prefix<'a, N: InnerNode<PREFIX_LEN>>(
        &'a self,
        node: &'a N,
        current_depth: usize,
    ) -> (
        &'a [u8],
        Option<NodePtr<PREFIX_LEN, LeafNode<N::Key, N::Value, PREFIX_LEN>>>,
    ) {
        let len = self.prefix_len();
        if likely!(len <= PREFIX_LEN) {
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
