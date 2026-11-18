//! A fixed-size bitmap over all 256 possible key bytes.

use core::{
    fmt,
    iter::FusedIterator,
    ops::{Bound, RangeBounds},
};

/// The number of bits stored in each word of the [`Bitmap`].
const WORD_BITS: usize = u64::BITS as usize;

/// The number of words needed to store one bit per possible key byte.
const NUM_WORDS: usize = 256 / WORD_BITS;

/// A set of key bytes, stored as one bit per possible `u8` value.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct Bitmap {
    /// Bit `k` (counting from the least significant bit of `words[0]`) is set
    /// when the key byte `k` is a member of the set. This layout means that the
    /// ordering of key bytes matches the ordering of bits, so the minimum and
    /// maximum members can be found with trailing/leading zero counts.
    words: [u64; NUM_WORDS],
}

impl Bitmap {
    /// Create a new bitmap with no members.
    pub const fn new() -> Self {
        Bitmap {
            words: [0; NUM_WORDS],
        }
    }

    /// Return the index of the word containing `key`, and a mask selecting
    /// the bit for `key` in that word.
    #[inline]
    const fn locate(key: u8) -> (usize, u64) {
        let key = key as usize;
        (key / WORD_BITS, 1 << (key % WORD_BITS))
    }

    /// Return true if `key` is a member of this set.
    #[inline]
    pub fn contains(&self, key: u8) -> bool {
        let (word, mask) = Self::locate(key);
        (self.words[word] & mask) != 0
    }

    /// Add `key` to this set, returning `true` if it was not already present.
    #[inline]
    pub fn insert(&mut self, key: u8) -> bool {
        let (word, mask) = Self::locate(key);
        let was_absent = (self.words[word] & mask) == 0;
        self.words[word] |= mask;
        was_absent
    }

    /// Remove `key` from this set, returning `true` if it was present.
    #[inline]
    pub fn remove(&mut self, key: u8) -> bool {
        let (word, mask) = Self::locate(key);
        let was_present = (self.words[word] & mask) != 0;
        self.words[word] &= !mask;
        was_present
    }

    /// Return the number of members in this set.
    #[inline]
    pub fn len(&self) -> usize {
        self.words.iter().map(|w| w.count_ones() as usize).sum()
    }

    /// Return true if this set has no members.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.words.iter().all(|w| *w == 0)
    }

    /// Return the smallest member of this set, if any.
    #[inline]
    pub fn first(&self) -> Option<u8> {
        for (idx, word) in self.words.iter().enumerate() {
            if *word != 0 {
                return Some((idx * WORD_BITS + word.trailing_zeros() as usize) as u8);
            }
        }
        None
    }

    /// Return the largest member of this set, if any.
    #[inline]
    pub fn last(&self) -> Option<u8> {
        for (idx, word) in self.words.iter().enumerate().rev() {
            if *word != 0 {
                return Some(
                    (idx * WORD_BITS + (WORD_BITS - 1 - word.leading_zeros() as usize)) as u8,
                );
            }
        }
        None
    }

    /// Return the smallest member of this set which is strictly greater than
    /// `key`, if any.
    #[inline]
    pub fn next_after(&self, key: u8) -> Option<u8> {
        let start = usize::from(key) + 1;
        let first_word = start / WORD_BITS;
        if first_word >= NUM_WORDS {
            return None;
        }

        // Only consider bits at or above `start` in the first word
        let masked = self.words[first_word] & (u64::MAX << (start % WORD_BITS));
        if masked != 0 {
            return Some((first_word * WORD_BITS + masked.trailing_zeros() as usize) as u8);
        }

        for (offset, word) in self.words[(first_word + 1)..].iter().enumerate() {
            if *word != 0 {
                let idx = first_word + 1 + offset;
                return Some((idx * WORD_BITS + word.trailing_zeros() as usize) as u8);
            }
        }
        None
    }

    /// Return the largest member of this set which is strictly less than
    /// `key`, if any.
    #[inline]
    pub fn prev_before(&self, key: u8) -> Option<u8> {
        // `end` is the largest candidate member, inclusive
        let end = usize::from(key.checked_sub(1)?);
        let last_word = end / WORD_BITS;

        // Only consider bits at or below `end` in the last word
        let masked = self.words[last_word] & (u64::MAX >> (WORD_BITS - 1 - end % WORD_BITS));
        if masked != 0 {
            return Some(
                (last_word * WORD_BITS + (WORD_BITS - 1 - masked.leading_zeros() as usize)) as u8,
            );
        }

        for (idx, word) in self.words[..last_word].iter().enumerate().rev() {
            if *word != 0 {
                return Some(
                    (idx * WORD_BITS + (WORD_BITS - 1 - word.leading_zeros() as usize)) as u8,
                );
            }
        }
        None
    }

    /// Remove and return the smallest member of this set, if any.
    #[inline]
    pub fn pop_first(&mut self) -> Option<u8> {
        for (idx, word) in self.words.iter_mut().enumerate() {
            if *word != 0 {
                let key = (idx * WORD_BITS + word.trailing_zeros() as usize) as u8;
                *word &= *word - 1;
                return Some(key);
            }
        }
        None
    }

    /// Remove and return the largest member of this set, if any.
    #[inline]
    pub fn pop_last(&mut self) -> Option<u8> {
        for (idx, word) in self.words.iter_mut().enumerate().rev() {
            if *word != 0 {
                let bit = WORD_BITS - 1 - word.leading_zeros() as usize;
                *word &= !(1 << bit);
                return Some((idx * WORD_BITS + bit) as u8);
            }
        }
        None
    }

    /// Return a copy of this set which only contains the members that fall
    /// within `bound`.
    ///
    /// Any bound is accepted: a range that is empty or "backwards" will
    /// produce an empty set.
    #[inline]
    pub fn range(&self, bound: impl RangeBounds<u8>) -> Self {
        // `start` is inclusive and `end` is exclusive, both in `0..=256`
        let start = match bound.start_bound() {
            Bound::Included(key) => usize::from(*key),
            Bound::Excluded(key) => usize::from(*key) + 1,
            Bound::Unbounded => 0,
        };
        let end = match bound.end_bound() {
            Bound::Included(key) => usize::from(*key) + 1,
            Bound::Excluded(key) => usize::from(*key),
            Bound::Unbounded => 256,
        };

        let mut words = self.words;
        for (idx, word) in words.iter_mut().enumerate() {
            let word_start = idx * WORD_BITS;
            // Bit positions within this word, clamped to `0..=WORD_BITS`
            let lo = start.saturating_sub(word_start).min(WORD_BITS);
            let hi = end.saturating_sub(word_start).min(WORD_BITS);
            *word &= bits_between(lo, hi);
        }

        Bitmap { words }
    }

    /// Return an iterator over the members of this set, in ascending order.
    #[inline]
    pub fn iter(&self) -> Iter {
        Iter::new(*self)
    }
}

/// Return a mask with the bits in positions `lo..hi` set, where both `lo` and
/// `hi` are in `0..=64`.
#[inline]
const fn bits_between(lo: usize, hi: usize) -> u64 {
    if lo >= hi {
        0
    } else {
        // `hi - lo` is in `1..=64`, so this shift amount is in `0..=63`
        (u64::MAX >> (WORD_BITS - (hi - lo))) << lo
    }
}

impl fmt::Debug for Bitmap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl FromIterator<u8> for Bitmap {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        let mut bitmap = Bitmap::new();
        for key in iter {
            bitmap.insert(key);
        }
        bitmap
    }
}

impl IntoIterator for Bitmap {
    type IntoIter = Iter;
    type Item = u8;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

impl IntoIterator for &Bitmap {
    type IntoIter = Iter;
    type Item = u8;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over the members of a [`Bitmap`], in ascending order.
#[derive(Clone)]
pub struct Iter {
    /// The members which have not yet been yielded from either end.
    ///
    /// Yielding a member clears its bit, so the front and back of the
    /// iterator can never yield the same member twice.
    remaining: Bitmap,
    /// The index of the lowest word which may still have members. All words
    /// before this index are zero.
    front: usize,
    /// One past the index of the highest word which may still have members.
    /// All words at or after this index are zero.
    back: usize,
}

impl Iter {
    fn new(remaining: Bitmap) -> Self {
        Iter {
            remaining,
            front: 0,
            back: NUM_WORDS,
        }
    }
}

impl Iterator for Iter {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.front < self.back {
            let word = &mut self.remaining.words[self.front];
            if *word != 0 {
                let key = self.front * WORD_BITS + word.trailing_zeros() as usize;
                *word &= *word - 1;
                return Some(key as u8);
            }
            self.front += 1;
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.remaining.len();
        (len, Some(len))
    }

    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        let mut acc = init;
        let words = &self.remaining.words[self.front..self.back];
        for (offset, mut word) in words.iter().copied().enumerate() {
            let base = (self.front + offset) * WORD_BITS;
            if word == u64::MAX {
                // Fast path for completely full words, which are common in
                // nodes with dense keys
                for bit in 0..WORD_BITS {
                    acc = f(acc, (base + bit) as u8);
                }
                continue;
            }
            while word != 0 {
                let key = base + word.trailing_zeros() as usize;
                word &= word - 1;
                acc = f(acc, key as u8);
            }
        }
        acc
    }

    #[inline]
    fn min(mut self) -> Option<Self::Item> {
        self.next()
    }

    #[inline]
    fn max(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl DoubleEndedIterator for Iter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        while self.front < self.back {
            let word = &mut self.remaining.words[self.back - 1];
            if *word != 0 {
                let bit = WORD_BITS - 1 - word.leading_zeros() as usize;
                *word &= !(1 << bit);
                return Some(((self.back - 1) * WORD_BITS + bit) as u8);
            }
            self.back -= 1;
        }
        None
    }

    #[inline]
    fn rfold<B, F>(self, init: B, mut f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        let mut acc = init;
        let words = &self.remaining.words[self.front..self.back];
        for (offset, mut word) in words.iter().copied().enumerate().rev() {
            let base = (self.front + offset) * WORD_BITS;
            if word == u64::MAX {
                // Fast path for completely full words, see `fold`
                for bit in (0..WORD_BITS).rev() {
                    acc = f(acc, (base + bit) as u8);
                }
                continue;
            }
            while word != 0 {
                let bit = WORD_BITS - 1 - word.leading_zeros() as usize;
                word &= !(1 << bit);
                acc = f(acc, (base + bit) as u8);
            }
        }
        acc
    }
}

impl ExactSizeIterator for Iter {}

impl FusedIterator for Iter {}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::*;

    #[test]
    fn empty() {
        let bitmap = Bitmap::new();
        assert!(bitmap.is_empty());
        assert_eq!(bitmap.len(), 0);
        assert_eq!(bitmap.first(), None);
        assert_eq!(bitmap.last(), None);
        assert_eq!(bitmap.iter().next(), None);
        assert_eq!(bitmap.iter().next_back(), None);
        assert!((0..=u8::MAX).all(|key| !bitmap.contains(key)));
    }

    #[test]
    fn insert_remove_contains() {
        let mut bitmap = Bitmap::new();
        for key in [0u8, 63, 64, 127, 128, 200, 255] {
            assert!(!bitmap.contains(key));
            assert!(bitmap.insert(key));
            assert!(!bitmap.insert(key));
            assert!(bitmap.contains(key));
        }
        assert_eq!(bitmap.len(), 7);
        assert!(!bitmap.contains(1));
        assert!(!bitmap.contains(254));

        assert!(bitmap.remove(64));
        assert!(!bitmap.remove(64));
        assert!(!bitmap.contains(64));
        assert!(!bitmap.remove(65));
        assert_eq!(bitmap.len(), 6);
    }

    #[test]
    fn first_last_every_single_key() {
        for key in 0..=u8::MAX {
            let bitmap: Bitmap = [key].into_iter().collect();
            assert_eq!(bitmap.first(), Some(key));
            assert_eq!(bitmap.last(), Some(key));
            assert_eq!(bitmap.iter().collect::<Vec<_>>(), [key]);
        }
    }

    #[test]
    fn iterate_both_directions() {
        let keys = [0u8, 3, 63, 64, 85, 191, 192, 254, 255];
        let bitmap: Bitmap = keys.into_iter().collect();

        assert_eq!(bitmap.first(), Some(0));
        assert_eq!(bitmap.last(), Some(255));
        assert_eq!(bitmap.iter().collect::<Vec<_>>(), keys);
        assert_eq!(
            bitmap.iter().rev().collect::<Vec<_>>(),
            keys.iter().rev().copied().collect::<Vec<_>>()
        );
        assert_eq!(bitmap.iter().len(), keys.len());

        // Alternating ends should meet in the middle without duplicates
        let mut iter = bitmap.iter();
        let mut seen = Vec::new();
        while let Some(key) = iter.next() {
            seen.push(key);
            if let Some(key) = iter.next_back() {
                seen.push(key);
            }
        }
        seen.sort();
        assert_eq!(seen, keys);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn fold_after_partial_iteration() {
        let keys = [0u8, 3, 63, 64, 85, 191, 192, 254, 255];
        let bitmap: Bitmap = keys.into_iter().collect();

        for skip_front in 0..=keys.len() {
            for skip_back in 0..=(keys.len() - skip_front) {
                let expected = &keys[skip_front..(keys.len() - skip_back)];

                let mut iter = bitmap.iter();
                (0..skip_front).for_each(|_| assert!(iter.next().is_some()));
                (0..skip_back).for_each(|_| assert!(iter.next_back().is_some()));
                assert_eq!(iter.len(), expected.len());

                let forward = iter.clone().fold(Vec::new(), |mut acc, key| {
                    acc.push(key);
                    acc
                });
                assert_eq!(forward, expected);

                let mut backward = iter.rfold(Vec::new(), |mut acc, key| {
                    acc.push(key);
                    acc
                });
                backward.reverse();
                assert_eq!(backward, expected);
            }
        }
    }

    #[test]
    fn fold_full_words() {
        // A mix of completely full words and partial words, to exercise the
        // full-word fast path.
        let keys: Vec<u8> = (0..=127u8).chain([130, 150]).chain(192..=255).collect();
        let bitmap: Bitmap = keys.iter().copied().collect();

        for skip_front in [0, 1, 64, 65, keys.len()] {
            for skip_back in [0, 1, 63, 64] {
                if skip_front + skip_back > keys.len() {
                    continue;
                }
                let expected = &keys[skip_front..(keys.len() - skip_back)];

                let mut iter = bitmap.iter();
                (0..skip_front).for_each(|_| assert!(iter.next().is_some()));
                (0..skip_back).for_each(|_| assert!(iter.next_back().is_some()));

                let forward = iter.clone().fold(Vec::new(), |mut acc, key| {
                    acc.push(key);
                    acc
                });
                assert_eq!(forward, expected);

                let mut backward = iter.rfold(Vec::new(), |mut acc, key| {
                    acc.push(key);
                    acc
                });
                backward.reverse();
                assert_eq!(backward, expected);
            }
        }
    }

    #[test]
    fn next_after_prev_before() {
        let sets: [Bitmap; 4] = [
            Bitmap::new(),
            (0..=u8::MAX).collect(),
            [0u8, 1, 62, 63, 64, 65, 127, 128, 129, 254, 255]
                .into_iter()
                .collect(),
            [100u8].into_iter().collect(),
        ];

        for bitmap in sets {
            for key in 0..=u8::MAX {
                let expected_next = bitmap.iter().find(|member| *member > key);
                let expected_prev = bitmap.iter().rev().find(|member| *member < key);
                assert_eq!(bitmap.next_after(key), expected_next, "next_after({key})");
                assert_eq!(bitmap.prev_before(key), expected_prev, "prev_before({key})");
            }
        }
    }

    #[test]
    fn range_matches_filter() {
        let full: Bitmap = (0..=u8::MAX).collect();
        let sparse: Bitmap = [0u8, 1, 62, 63, 64, 65, 127, 128, 129, 254, 255]
            .into_iter()
            .collect();

        let edges = [
            0u8, 1, 2, 62, 63, 64, 65, 126, 127, 128, 129, 191, 192, 254, 255,
        ];
        let bounds = |key: u8| [Bound::Included(key), Bound::Excluded(key)];

        for bitmap in [full, sparse] {
            for &lo in &edges {
                for &hi in &edges {
                    for start in bounds(lo).into_iter().chain([Bound::Unbounded]) {
                        for end in bounds(hi).into_iter().chain([Bound::Unbounded]) {
                            let range = (start, end);
                            let expected = bitmap
                                .iter()
                                .filter(|key| range.contains(key))
                                .collect::<Vec<_>>();
                            assert_eq!(
                                bitmap.range(range).iter().collect::<Vec<_>>(),
                                expected,
                                "{range:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn debug_format() {
        let bitmap: Bitmap = [3u8, 1, 200].into_iter().collect();
        assert_eq!(alloc::format!("{bitmap:?}"), "{1, 3, 200}");
    }
}
