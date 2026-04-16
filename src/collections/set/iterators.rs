//! Module containing iterator types for
//! [`TreeSet`][crate::TreeSet][crate::TreeSet].

use core::{
    cmp::Ordering,
    iter::{FusedIterator, Peekable},
};

use crate::{
    allocator::{Allocator, Global},
    map::{self, DEFAULT_PREFIX_LEN},
    OrderedBytes,
};

/// An iterator over the items of a [`TreeSet`][crate::TreeSet].
///
/// This `struct` is created by the [`iter`][crate::TreeSet::iter] method on
/// [`TreeSet`][crate::TreeSet]. See its documentation for more.
pub struct Iter<'a, K, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global>(
    pub(super) map::Keys<'a, K, (), PREFIX_LEN, A>,
);

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> Iterator for Iter<'a, K, PREFIX_LEN, A> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    fn last(self) -> Option<Self::Item> {
        self.0.last()
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> DoubleEndedIterator
    for Iter<'a, K, PREFIX_LEN, A>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> ExactSizeIterator
    for Iter<'a, K, PREFIX_LEN, A>
{
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> FusedIterator for Iter<'a, K, PREFIX_LEN, A> {}

/// An owning iterator over the items of a [`TreeSet`][crate::TreeSet].
///
/// This `struct` is created by the `into_iter` method on
/// [`TreeSet`][crate::TreeSet] (via the [`IntoIterator`] trait). See its
/// documentation for more.
pub struct IntoIter<K, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global>(
    pub(super) map::IntoKeys<K, (), PREFIX_LEN, A>,
);

impl<K, const PREFIX_LEN: usize, A: Allocator> Iterator for IntoIter<K, PREFIX_LEN, A> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, const PREFIX_LEN: usize, A: Allocator> DoubleEndedIterator for IntoIter<K, PREFIX_LEN, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<K, const PREFIX_LEN: usize, A: Allocator> ExactSizeIterator for IntoIter<K, PREFIX_LEN, A> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<K, const PREFIX_LEN: usize, A: Allocator> FusedIterator for IntoIter<K, PREFIX_LEN, A> {}

/// An iterator over a sub-range of items in a [`TreeSet`][crate::TreeSet].
///
/// This `struct` is created by the [`range`][crate::TreeSet::range] method on
/// [`TreeSet`][crate::TreeSet]. See its documentation for more.
pub struct Range<'a, K, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global>(
    pub(super) map::Range<'a, K, (), PREFIX_LEN, A>,
);

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> Iterator for Range<'a, K, PREFIX_LEN, A> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> DoubleEndedIterator
    for Range<'a, K, PREFIX_LEN, A>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, _)| k)
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> FusedIterator for Range<'a, K, PREFIX_LEN, A> {}

/// An iterator that visits the items in a [`TreeSet`][crate::TreeSet] that are
/// not present in another set.
///
/// This `struct` is created by the [`difference`][crate::TreeSet::difference]
/// method on [`TreeSet`][crate::TreeSet]. See its documentation for more.
pub struct Difference<'a, K, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global> {
    pub(super) iter_self: Peekable<Iter<'a, K, PREFIX_LEN, A>>,
    pub(super) iter_other: Peekable<Iter<'a, K, PREFIX_LEN, A>>,
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> Iterator for Difference<'a, K, PREFIX_LEN, A>
where
    K: OrderedBytes,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match (self.iter_self.peek(), self.iter_other.peek()) {
                (None, _) => return None,
                (Some(_), None) => return self.iter_self.next(),
                (Some(a), Some(b)) => match a.cmp(b) {
                    Ordering::Less => return self.iter_self.next(),
                    Ordering::Equal => {
                        self.iter_self.next();
                        self.iter_other.next();
                    },
                    Ordering::Greater => {
                        self.iter_other.next();
                    },
                },
            }
        }
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> FusedIterator
    for Difference<'a, K, PREFIX_LEN, A>
where
    K: OrderedBytes,
{
}

/// An iterator that visits the items that are present in both a
/// [`TreeSet`][crate::TreeSet] and another set.
///
/// This `struct` is created by the
/// [`intersection`][crate::TreeSet::intersection] method on
/// [`TreeSet`][crate::TreeSet]. See its documentation for more.
pub struct Intersection<'a, K, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global>
{
    pub(super) iter_self: Peekable<Iter<'a, K, PREFIX_LEN, A>>,
    pub(super) iter_other: Peekable<Iter<'a, K, PREFIX_LEN, A>>,
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> Iterator for Intersection<'a, K, PREFIX_LEN, A>
where
    K: OrderedBytes,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match (self.iter_self.peek(), self.iter_other.peek()) {
                (None, _) | (_, None) => return None,
                (Some(a), Some(b)) => match a.cmp(b) {
                    Ordering::Less => {
                        self.iter_self.next();
                    },
                    Ordering::Equal => {
                        self.iter_other.next();
                        return self.iter_self.next();
                    },
                    Ordering::Greater => {
                        self.iter_other.next();
                    },
                },
            }
        }
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> FusedIterator
    for Intersection<'a, K, PREFIX_LEN, A>
where
    K: OrderedBytes,
{
}

/// An iterator that visits all items present in a [`TreeSet`][crate::TreeSet]
/// or another set, without duplicates.
///
/// This `struct` is created by the [`union`][crate::TreeSet::union] method on
/// [`TreeSet`][crate::TreeSet]. See its documentation for more.
pub struct Union<'a, K, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global> {
    pub(super) iter_self: Peekable<Iter<'a, K, PREFIX_LEN, A>>,
    pub(super) iter_other: Peekable<Iter<'a, K, PREFIX_LEN, A>>,
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> Iterator for Union<'a, K, PREFIX_LEN, A>
where
    K: OrderedBytes,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter_self.peek(), self.iter_other.peek()) {
            (None, None) => None,
            (Some(_), None) => self.iter_self.next(),
            (None, Some(_)) => self.iter_other.next(),
            (Some(a), Some(b)) => match a.cmp(b) {
                Ordering::Less => self.iter_self.next(),
                Ordering::Equal => {
                    self.iter_other.next();
                    self.iter_self.next()
                },
                Ordering::Greater => self.iter_other.next(),
            },
        }
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> FusedIterator for Union<'a, K, PREFIX_LEN, A> where
    K: OrderedBytes
{
}

/// An iterator that visits the items present in exactly one of a
/// [`TreeSet`][crate::TreeSet] and another set.
///
/// This `struct` is created by the
/// [`symmetric_difference`][crate::TreeSet::symmetric_difference] method on
/// [`TreeSet`][crate::TreeSet]. See its documentation for more.
pub struct SymmetricDifference<
    'a,
    K,
    const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN,
    A: Allocator = Global,
> {
    pub(super) iter_self: Peekable<Iter<'a, K, PREFIX_LEN, A>>,
    pub(super) iter_other: Peekable<Iter<'a, K, PREFIX_LEN, A>>,
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> Iterator
    for SymmetricDifference<'a, K, PREFIX_LEN, A>
where
    K: OrderedBytes,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match (self.iter_self.peek(), self.iter_other.peek()) {
                (None, _) => return self.iter_other.next(),
                (_, None) => return self.iter_self.next(),
                (Some(a), Some(b)) => match a.cmp(b) {
                    Ordering::Less => return self.iter_self.next(),
                    Ordering::Equal => {
                        self.iter_self.next();
                        self.iter_other.next();
                    },
                    Ordering::Greater => return self.iter_other.next(),
                },
            }
        }
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> FusedIterator
    for SymmetricDifference<'a, K, PREFIX_LEN, A>
where
    K: OrderedBytes,
{
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TreeSet;

    #[test]
    fn iterators_are_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        is_send::<Iter<'_, u8>>();
        is_sync::<Iter<'_, u8>>();
        is_send::<IntoIter<u8>>();
        is_sync::<IntoIter<u8>>();
        is_send::<Range<'_, u8>>();
        is_sync::<Range<'_, u8>>();
        is_send::<Difference<'_, u8>>();
        is_sync::<Difference<'_, u8>>();
        is_send::<Intersection<'_, u8>>();
        is_sync::<Intersection<'_, u8>>();
        is_send::<Union<'_, u8>>();
        is_sync::<Union<'_, u8>>();
        is_send::<SymmetricDifference<'_, u8>>();
        is_sync::<SymmetricDifference<'_, u8>>();
    }

    fn make_set(values: &[u8]) -> TreeSet<u8> {
        values.iter().copied().collect()
    }

    #[test]
    fn difference_basic() {
        let a = make_set(&[1, 2, 3, 5]);
        let b = make_set(&[2, 4, 5, 6]);
        let diff: alloc::vec::Vec<_> = a.difference(&b).copied().collect();
        assert_eq!(diff, &[1, 3]);
    }

    #[test]
    fn intersection_basic() {
        let a = make_set(&[1, 2, 3, 5]);
        let b = make_set(&[2, 4, 5, 6]);
        let inter: alloc::vec::Vec<_> = a.intersection(&b).copied().collect();
        assert_eq!(inter, &[2, 5]);
    }

    #[test]
    fn union_basic() {
        let a = make_set(&[1, 2, 3, 5]);
        let b = make_set(&[2, 4, 5, 6]);
        let u: alloc::vec::Vec<_> = a.union(&b).copied().collect();
        assert_eq!(u, &[1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn symmetric_difference_basic() {
        let a = make_set(&[1, 2, 3, 5]);
        let b = make_set(&[2, 4, 5, 6]);
        let sd: alloc::vec::Vec<_> = a.symmetric_difference(&b).copied().collect();
        assert_eq!(sd, &[1, 3, 4, 6]);
    }

    #[test]
    fn difference_empty() {
        let a: TreeSet<u8> = TreeSet::new();
        let b = make_set(&[1, 2, 3]);
        let diff: alloc::vec::Vec<_> = a.difference(&b).copied().collect();
        assert_eq!(diff, &[] as &[u8]);

        let diff2: alloc::vec::Vec<_> = b.difference(&a).copied().collect();
        assert_eq!(diff2, &[1, 2, 3]);
    }

    #[test]
    fn union_empty() {
        let a: TreeSet<u8> = TreeSet::new();
        let b = make_set(&[1, 2, 3]);
        let u: alloc::vec::Vec<_> = a.union(&b).copied().collect();
        assert_eq!(u, &[1, 2, 3]);
    }

    #[test]
    fn iter_is_fused() {
        let set = make_set(&[1, 2]);
        let mut iter = set.iter();
        assert!(iter.next().is_some());
        assert!(iter.next().is_some());
        assert!(iter.next().is_none());
        assert!(iter.next().is_none());
    }

    #[test]
    fn iter_double_ended() {
        let set = make_set(&[1, 2, 3, 4, 5]);
        let mut iter = set.iter();
        assert_eq!(iter.next(), Some(&1u8));
        assert_eq!(iter.next_back(), Some(&5u8));
        assert_eq!(iter.next(), Some(&2u8));
        assert_eq!(iter.next_back(), Some(&4u8));
        assert_eq!(iter.next(), Some(&3u8));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn range_basic() {
        let set = make_set(&[1u8, 2, 3, 4, 5]);
        let range: alloc::vec::Vec<_> = set.range(2u8..=4u8).copied().collect();
        assert_eq!(range, &[2u8, 3, 4]);
    }
}
