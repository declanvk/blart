//! Different header type

use core::fmt::Debug;

use crate::{
    raw::{minimum_unchecked, InnerNode, LeafNode, NodePtr},
    rust_nightly_apis::likely,
    AsBytes,
};

/// The common header for all inner nodes
#[derive(Clone, PartialEq, Eq)]
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
    #[inline]
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
    #[inline]
    pub fn empty() -> Self {
        Self {
            num_children: 0,
            prefix_len: 0,
            prefix: [0; PREFIX_LEN],
        }
    }

    /// Read the initialized portion of the prefix present in the header.
    #[inline]
    pub fn read_prefix(&self) -> &[u8] {
        &self.prefix[0..self.capped_prefix_len()]
    }

    /// Get the number of bytes in the prefix.
    #[inline]
    pub fn prefix_len(&self) -> usize {
        self.prefix_len as usize
    }

    /// Minimum between [`Self::prefix_len`] and `PREFIX_LEN`.
    #[inline]
    pub fn capped_prefix_len(&self) -> usize {
        (self.prefix_len as usize).min(PREFIX_LEN)
    }

    /// Return the number of children of this node.
    #[inline]
    pub fn num_children(&self) -> usize {
        usize::from(self.num_children)
    }

    /// Left trim by `len`, copies the remaining data to the beginning of the
    /// prefix
    ///
    /// # Panics
    ///  - If `len` > length of the prefix
    #[inline]
    pub fn ltrim_by(&mut self, len: usize) {
        assert!(
            (len as u32) <= self.prefix_len,
            "given length [{len}] must be less than or equal to the prefix length [{}]",
            self.prefix_len
        );
        self.prefix_len -= len as u32;

        let begin = len;
        let end = begin + self.capped_prefix_len();

        unsafe {
            // SAFETY: This function is called when mismatch happened and
            // we used the node to match the number of bytes,
            // by this we know that len < prefix len, but since we + 1,
            // to skip the key byte we have that len <= prefix len
            core::hint::assert_unchecked(end <= self.prefix.len());

            // SAFETY: This is by construction end = begin + len
            core::hint::assert_unchecked(begin <= end);
        }
        self.prefix.copy_within(begin..end, 0);
    }

    /// Set the length of the prefix to 0 and returns a copy of the
    /// prefix, length and capped length
    #[inline]
    pub fn clear_prefix(&mut self) -> ([u8; PREFIX_LEN], usize, usize) {
        let len = self.prefix_len();
        let capped_len = self.capped_prefix_len();
        self.prefix_len = 0;

        (self.prefix, len, capped_len)
    }

    /// Append `new` to the prefix and sums `new_len` to the prefix length
    #[inline]
    pub fn push_prefix(&mut self, new: &[u8], new_len: usize) {
        let begin = self.capped_prefix_len();
        let end = (begin + new.len()).min(PREFIX_LEN);
        let len = end - begin;
        self.prefix[begin..end].copy_from_slice(&new[..len]);
        self.prefix_len += new_len as u32;
    }

    /// Increments the number of children
    #[inline]
    pub fn inc_num_children(&mut self) {
        self.num_children += 1;
    }

    /// Decrements the number of children
    #[inline]
    pub fn dec_num_children(&mut self) {
        self.num_children -= 1;
    }

    /// Reset the number of children to 0.
    #[inline]
    pub fn reset_num_children(&mut self) {
        self.num_children = 0;
    }

    #[inline]
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

        unsafe {
            // SAFETY: This function is called a mismatch happened and
            // we used the leaf to match the number of matching bytes,
            // by this we know that len < prefix len, but since we + 1,
            // to skip the key byte we have that len <= prefix len
            core::hint::assert_unchecked(end <= leaf_key.len());

            // SAFETY: This is by construction end = begin + len
            core::hint::assert_unchecked(begin <= end);
        }

        let leaf_key = &leaf_key[begin..end];
        let leaf_key = &leaf_key[..leaf_key.len().min(PREFIX_LEN)];
        self.prefix[..len.min(PREFIX_LEN)].copy_from_slice(leaf_key)
    }

    #[inline]
    pub fn inner_read_full_prefix<'a, N: InnerNode<PREFIX_LEN>>(
        &'a self,
        node: &'a N,
        current_depth: usize,
    ) -> NodePrefix<'a, N::Key, N::Value, PREFIX_LEN>
    where
        N::Key: AsBytes,
    {
        let len = self.prefix_len();
        if likely!(len <= PREFIX_LEN) {
            (self.read_prefix(), None)
        } else {
            // SAFETY: By construction a InnerNode, must have >= 1 children, this
            // is even more strict since in the case of 1 child the node can be
            // collapsed, so a InnerNode must have >= 2 children, so it's safe
            // to search for the minium. And the same applies to the `minimum_unchecked`
            // function
            let (_, min_child) = node.min();
            let leaf_ptr = unsafe { minimum_unchecked(min_child) };

            // SAFETY: Since have a shared reference
            // is safe to create a shared reference from it
            let leaf = unsafe { leaf_ptr.as_ref() };
            let leaf = leaf.key_ref().as_bytes();

            unsafe {
                // SAFETY: Since we are iterating the key and prefixes, we
                // expect that the depth never exceeds the key len.
                // Because if this happens we ran out of bytes in the key to match
                // and the whole process should be already finished
                core::hint::assert_unchecked(current_depth <= leaf.len());

                // SAFETY: By the construction of the prefix we know that this is inbounds
                // since the prefix len guarantees it to us
                core::hint::assert_unchecked(current_depth + len <= leaf.len());

                // SAFETY: This can't overflow since len comes from a u32
                core::hint::assert_unchecked(current_depth <= current_depth + len);
            }
            let leaf = &leaf[current_depth..(current_depth + len)];
            (leaf, Some(leaf_ptr))
        }
    }
}

/// This type represents the contents of an [`InnerNode`] prefix, either read
/// directly from the prefix or fetched from a leaf node descendant.
///
/// The second value is the tuple will be `Some(_)` if the value was fetched
/// from a leaf node.
pub type NodePrefix<'a, K, V, const PREFIX_LEN: usize> = (
    &'a [u8],
    Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>>,
);

impl<const PREFIX_LEN: usize> Debug for Header<PREFIX_LEN> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Header")
            .field("num_children", &self.num_children)
            .field("prefix_len", &self.prefix_len)
            .field(
                "prefix",
                &&self.prefix[..(self.prefix_len as usize).min(self.prefix.len())],
            )
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_delete_prefix() {
        let mut h = Header::<16>::new(&[1, 2, 3, 4, 5, 6, 7, 8], 8);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 8);

        h.ltrim_by(0);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 8);

        h.ltrim_by(3);
        assert_eq!(h.read_prefix(), &[4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 5);

        h.ltrim_by(1);
        assert_eq!(h.read_prefix(), &[5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 4);

        h.ltrim_by(4);
        assert_eq!(h.read_prefix(), &[] as &[u8]);
        assert_eq!(h.prefix_len(), 0);
    }

    #[test]
    #[should_panic = "given length [10] must be less than or equal to the prefix length [8]"]
    fn header_ltrim_prefix_too_many_bytes_panic() {
        let mut h = Header::<16>::new(&[1, 2, 3, 4, 5, 6, 7, 8], 8);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 8);

        h.ltrim_by(10);
    }
}
