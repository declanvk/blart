use std::{fmt::Debug, intrinsics::{assume, likely}};

use crate::{minimum_unchecked, AsBytes, InnerNode, LeafNode, NodePtr};

/// The number of bytes stored for path compression in the node header.
pub const NUM_PREFIX_BYTES: usize = 16;

/// The common header for all inner nodes
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[repr(align(8))]
pub struct RawHeader {
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

pub trait NodeHeader: Debug + Clone + PartialEq + Eq {
    /// Create a new [`Header`] using
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

    /// Minimum between [`Self::prefix_len`] and [`NUM_PREFIX_BYTES`]
    fn capped_prefix_len(&self) -> usize;

    /// Return the number of children of this node.
    fn num_children(&self) -> usize;

    /// Left trim by `len`, copies the remaining data to the beging of the
    /// prefix
    ///
    /// # Panics
    ///
    /// If `len` > length of the prefix
    fn ltrim_by(&mut self, len: usize);

    /// Left trim by `len`, copies the remaining data to the beging of the
    /// prefix, in this case we use a leaf to achieve this, we also need the
    /// `depth` (a.k.a how many bytes of the leaf have already been used)
    fn ltrim_by_with_leaf<K: AsBytes, V, H: NodeHeader>(
        &mut self,
        len: usize,
        depth: usize,
        leaf_ptr: NodePtr<LeafNode<K, V, H>>,
    );

    /// Append `new` to the prefix and sums `new_len` to the prefix length
    fn push_prefix(&mut self, new: &[u8], new_len: usize);

    /// Set the length of the prefix to 0 and returns a copy of the
    /// prefix, length and capped length
    fn clear_prefix(&mut self) -> ([u8; NUM_PREFIX_BYTES], usize, usize);

    fn inc_num_children(&mut self);

    fn dec_num_children(&mut self);

    fn inner_read_full_prefix<N: InnerNode>(&self, node: &N, current_depth: usize) -> (
        &[u8],
        Option<NodePtr<LeafNode<N::Key, N::Value, N::Header>>>,
    );
}

impl NodeHeader for RawHeader {
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
    fn empty() -> Self {
        Self {
            num_children: 0,
            prefix_len: 0,
            prefix: [0; NUM_PREFIX_BYTES],
        }
    }

    /// Read the initialized portion of the prefix present in the header.
    fn read_prefix(&self) -> &[u8] {
        &self.prefix[0..self.capped_prefix_len()]
    }

    /// Get the number of bytes in the prefix.
    fn prefix_len(&self) -> usize {
        self.prefix_len as usize
    }

    /// Minimum between [`Self::prefix_len`] and [`NUM_PREFIX_BYTES`]
    fn capped_prefix_len(&self) -> usize {
        (self.prefix_len as usize).min(NUM_PREFIX_BYTES)
    }

    /// Return the number of children of this node.
    fn num_children(&self) -> usize {
        usize::from(self.num_children)
    }

    /// Left trim by `len`, copies the remaining data to the beging of the
    /// prefix
    ///
    /// # Panics
    ///
    /// If `len` > length of the prefix
    fn ltrim_by(&mut self, len: usize) {
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

    /// Left trim by `len`, copies the remaining data to the beging of the
    /// prefix, in this case we use a leaf to achieve this, we also need the
    /// `depth` (a.k.a how many bytes of the leaf have already been used)
    fn ltrim_by_with_leaf<K: AsBytes, V, H: NodeHeader>(
        &mut self,
        len: usize,
        depth: usize,
        leaf_ptr: NodePtr<LeafNode<K, V, H>>,
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

    /// Append `new` to the prefix and sums `new_len` to the prefix length
    fn push_prefix(&mut self, new: &[u8], new_len: usize) {
        let begin = self.capped_prefix_len();
        let end = (begin + new.len()).min(NUM_PREFIX_BYTES);
        let len = end - begin;
        self.prefix[begin..end].copy_from_slice(&new[..len]);
        self.prefix_len += new_len as u32;
    }

    /// Set the length of the prefix to 0 and returns a copy of the
    /// prefix, length and capped length
    fn clear_prefix(&mut self) -> ([u8; NUM_PREFIX_BYTES], usize, usize) {
        let len = self.prefix_len();
        let capped_len = self.capped_prefix_len();
        self.prefix_len = 0;

        (self.prefix, len, capped_len)
    }
    
    fn inc_num_children(&mut self) {
        self.num_children += 1;
    }
    
    fn dec_num_children(&mut self) {
        self.num_children -= 1;
    }

    #[inline(always)]
    fn inner_read_full_prefix<N: InnerNode>(&self, node: &N, current_depth: usize) -> (
        &[u8],
        Option<NodePtr<LeafNode<N::Key, N::Value, N::Header>>>,
    ) {
        let len = self.prefix_len();
        if likely(len <= NUM_PREFIX_BYTES) {
            (self.read_prefix(), None)
        } else {
            // SAFETY: By construction a InnerNode, must have >= 1 childs, this
            // is even more strict since in the case of 1 child the node can be
            // collapsed, so a InnserNode must have >= 2 childs, so it's safe
            // to search for the minium. And the same applies to the `minimum_unchecked`
            // function
            let (_, min_child) = node.min();
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
}