/// The number of bytes stored for path compression in the node header.
#[cfg(test)]
pub const NUM_PREFIX_BYTES: usize = 8;

/// The common header for all inner nodes
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Header {
    /// Number of children of this inner node and number of bytes populated in prefix array.
    num_children: u16,
    /// The key prefix for this node.
    prefix: Vec<u8>,
}

impl Header {
    /// Create a new `Header` for an empty node.
    pub fn empty() -> Self {
        Header {
            num_children: 0,
            prefix: Vec::new(),
        }
    }

    /// Write prefix bytes to this header, appending to existing bytes if
    /// present.
    pub fn extend_prefix(&mut self, new_bytes: &[u8]) {
        self.prefix.extend(new_bytes.iter().copied());
    }

    /// Write bytes to the start of the key prefix.
    pub fn prepend_prefix(&mut self, new_bytes: &[u8]) {
        self.prefix
            .splice(0..0, new_bytes.iter().copied())
            .for_each(|_| ());
    }

    /// Remove the specified number of bytes from the start of the prefix.
    ///
    /// # Panics
    ///
    ///  - Panics if the number of bytes to remove is greater than the prefix
    ///    size.
    pub fn ltrim_prefix(&mut self, num_bytes: usize) {
        self.prefix.drain(..num_bytes).for_each(|_| ())
    }

    /// Read the initialized portion of the prefix present in the header.
    pub fn read_prefix(&self) -> &[u8] {
        self.prefix.as_ref()
    }

    /// Compares the compressed path of a node with the key and returns the
    /// number of equal bytes.
    pub fn match_prefix(&self, possible_key: &[u8]) -> usize {
        let min_len = self.prefix.len().min(possible_key.len());

        for idx in 0..min_len {
            if self.prefix[idx] != possible_key[idx] {
                return idx;
            }
        }

        min_len
    }

    /// Return the number of children of this node.
    pub fn num_children(&self) -> usize {
        usize::from(self.num_children)
    }

    /// Modify the number of children of this node.
    ///
    /// # Panics
    ///
    /// This method will panic if the given `num_children` is larger than 256.
    pub fn set_num_children(&mut self, num_children: usize) {
        assert!(
            num_children <= 256,
            "The new number of children [{num_children}] is greater than 256"
        );
        let num_children = u16::try_from(num_children)
            .expect("num_children is less than 256, should fit in a u16");

        self.num_children = num_children;
    }

    /// Increase the number of children of this node by 1.
    ///
    /// # Panics
    ///
    /// This method will panic if the current number of children is 256.
    pub fn increment_num_children(&mut self) {
        assert!(
            self.num_children < 256,
            "Increment would overflow num_children, since it is currently 256"
        );

        self.num_children += 1;
    }

    /// Decrease the number of children of this node by 1.
    ///
    /// # Panics
    ///
    /// This method will panic if the current number of children is 0.
    pub fn decrement_num_children(&mut self) {
        assert!(
            self.num_children > 0,
            "Decrement would overflow num_children, since it is currently 0"
        );

        self.num_children -= 1;
    }

    /// Return the number of bytes in the prefix.
    pub fn prefix_len(&self) -> usize {
        self.prefix.len()
    }

    /// Return true if the prefix has spilled to the heap
    pub fn is_prefix_on_heap(&self) -> bool {
        true
    }

    /// Overwrite the prefix of this header with the prefix from `other`.
    pub fn copy_prefix_from(&mut self, other: &Self) {
        self.prefix.clone_from(&other.prefix);
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub(crate) const EXPECTED_HEADER_SIZE: usize = 32;

    #[test]
    fn size_and_alignment_match() {
        assert_eq!(std::mem::size_of::<Header>(), EXPECTED_HEADER_SIZE);
        assert_eq!(std::mem::align_of::<Header>(), 8);
    }

    #[test]
    fn read_write_prefix() {
        let mut h = Header::empty();

        assert_eq!(h.prefix_len(), 0);
        assert_eq!(h.read_prefix(), &[]);

        h.extend_prefix(&[1, 2, 3]);

        assert_eq!(h.prefix_len(), 3);
        assert_eq!(h.read_prefix(), &[1, 2, 3]);

        h.extend_prefix(&[4, 5, 6]);

        assert_eq!(h.prefix_len(), 6);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6]);

        h.extend_prefix(&[7, 8]);

        assert_eq!(h.prefix_len(), 8);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);

        h.extend_prefix(&[9, 10, 11, 12]);

        assert_eq!(h.prefix_len(), 12);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);

        h.extend_prefix(&[]);

        assert_eq!(h.prefix_len(), 12);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
    }

    #[test]
    fn prepend_prefix() {
        let mut h = Header::default();

        assert_eq!(h.prefix_len(), 0);
        assert_eq!(h.read_prefix(), &[]);

        h.prepend_prefix(&[]);

        assert_eq!(h.prefix_len(), 0);
        assert_eq!(h.read_prefix(), &[]);

        h.prepend_prefix(&[1, 2, 3]);

        assert_eq!(h.prefix_len(), 3);
        assert_eq!(h.read_prefix(), &[1, 2, 3]);

        h.prepend_prefix(&[4, 5, 6]);

        assert_eq!(h.prefix_len(), 6);
        assert_eq!(h.read_prefix(), &[4, 5, 6, 1, 2, 3]);

        h.extend_prefix(&[7, 8, 9]);

        assert_eq!(h.prefix_len(), 9);
        assert_eq!(h.read_prefix(), &[4, 5, 6, 1, 2, 3, 7, 8, 9]);
    }

    #[test]
    fn check_prefix() {
        let mut h = Header::empty();

        h.extend_prefix(&[1, 2, 3]);

        assert_eq!(h.match_prefix(&[1, 2, 3]), 3);
        assert_eq!(h.match_prefix(&[0, 1, 2]), 0);
        assert_eq!(h.match_prefix(&[1, 2]), 2);
        assert_eq!(h.match_prefix(&[]), 0);

        h.extend_prefix(&[4, 5, 6, 7, 8, 9, 10, 11, 12]);

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
            8
        );
    }

    #[test]
    fn empty_prefix_bytes_match() {
        let mut h = Header::empty();

        h.extend_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
        h.ltrim_prefix(NUM_PREFIX_BYTES);
        // 6 bytes are represented

        assert_eq!(h.match_prefix(&[1, 2, 3]), 0);
        assert_eq!(h.match_prefix(&[0]), 0);
        assert_eq!(h.match_prefix(&[]), 0);
        assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6]), 0);
        assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]), 0);

        assert_eq!(h.match_prefix(&[9, 10, 11, 12]), 4);
        assert_eq!(h.match_prefix(&[9, 10, 11, 12, 13, 14]), 6);
    }

    #[test]
    fn delete_prefix() {
        let mut h = Header::empty();
        h.extend_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 8);

        h.ltrim_prefix(0);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 8);

        h.ltrim_prefix(3);
        assert_eq!(h.read_prefix(), &[4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 5);

        h.ltrim_prefix(1);
        assert_eq!(h.read_prefix(), &[5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 4);

        h.ltrim_prefix(4);
        assert_eq!(h.read_prefix(), &[]);
        assert_eq!(h.prefix_len(), 0);
    }

    #[test]
    #[should_panic]
    fn ltrim_prefix_too_many_bytes_panic() {
        let mut h = Header::empty();
        h.extend_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 8);

        h.ltrim_prefix(10);
    }

    #[test]
    #[should_panic]
    fn ltrim_prefix_non_stored_bytes_panic() {
        let mut h = Header::empty();
        h.extend_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
        assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert_eq!(h.prefix_len(), 8);

        h.ltrim_prefix(0);
    }
}
