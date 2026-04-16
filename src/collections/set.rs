//! Module containing the implementation of the [`TreeSet`] and associated
//! iterators.

use core::{
    borrow::Borrow,
    fmt::{self, Debug},
    hash::Hash,
    ops::RangeBounds,
};

use crate::{
    allocator::{Allocator, Global},
    map::DEFAULT_PREFIX_LEN,
    raw::InsertPrefixError,
    rust_nightly_apis::hasher_write_length_prefix,
    AsBytes, NoPrefixesBytes, OrderedBytes, TreeMap,
};

mod iterators;
pub use iterators::*;

/// An ordered set backed by an adaptive radix trie.
pub struct TreeSet<K, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global> {
    map: TreeMap<K, (), PREFIX_LEN, A>,
}

impl<K> TreeSet<K> {
    /// Creates a new, empty [`TreeSet`] with the default prefix length (16).
    ///
    /// This function will not pre-allocate anything.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let set = TreeSet::<u8>::new();
    /// assert!(set.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::with_prefix_len()
    }
}

impl<K, A: Allocator> TreeSet<K, DEFAULT_PREFIX_LEN, A> {
    /// Creates a new, empty [`TreeSet`] with the default prefix length (16),
    /// using the given allocator.
    ///
    /// This function will not pre-allocate anything.
    #[cfg_attr(
        any(feature = "nightly", feature = "allocator-api2"),
        doc = r##"
# Examples

```rust
use blart::{TreeSet, map::DEFAULT_PREFIX_LEN};
use std::alloc::System;

let set = TreeSet::<u8, DEFAULT_PREFIX_LEN, _>::new_in(System);
assert!(set.is_empty());
```
    "##
    )]
    pub fn new_in(alloc: A) -> Self {
        Self::with_prefix_len_in(alloc)
    }
}

impl<K, const PREFIX_LEN: usize> TreeSet<K, PREFIX_LEN> {
    /// Creates a new, empty [`TreeSet`] with a non-default node prefix length.
    ///
    /// The prefix length is inferred as a const-generic parameter on the type.
    /// This function will not pre-allocate anything.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let set = TreeSet::<u8, 8>::with_prefix_len();
    /// assert!(set.is_empty());
    /// ```
    pub fn with_prefix_len() -> Self {
        TreeSet {
            map: TreeMap::with_prefix_len(),
        }
    }
}

impl<K, const PREFIX_LEN: usize, A: Allocator> TreeSet<K, PREFIX_LEN, A> {
    /// Creates a new, empty [`TreeSet`] with a non-default node prefix length
    /// and a custom allocator.
    ///
    /// The prefix length is inferred as a const-generic parameter on the type.
    /// This function will not pre-allocate anything.
    pub fn with_prefix_len_in(alloc: A) -> Self {
        TreeSet {
            map: TreeMap::with_prefix_len_in(alloc),
        }
    }

    /// Returns a reference to the underlying allocator.
    pub fn allocator(&self) -> &A {
        self.map.allocator()
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set = TreeSet::new();
    /// set.insert(1u8);
    /// set.insert(2u8);
    /// assert_eq!(set.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set = TreeSet::<u8>::new();
    /// assert!(set.is_empty());
    /// set.insert(1u8);
    /// assert!(!set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clears the set, removing all elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// assert_eq!(set.len(), 3);
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.map.clear()
    }

    /// Returns `true` if the set contains the given value.
    ///
    /// The value may be any borrowed form of the set's element type, but
    /// [`AsBytes`] on the borrowed form must match that of the element type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// assert!(set.contains(&2u8));
    /// assert!(!set.contains(&4u8));
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        self.map.contains_key(value)
    }

    /// Returns a reference to the element in the set, if any, that is equal to
    /// the given value.
    ///
    /// The value may be any borrowed form of the set's element type, but
    /// [`AsBytes`] on the borrowed form must match that of the element type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// assert_eq!(set.get(&2u8), Some(&2u8));
    /// assert_eq!(set.get(&4u8), None);
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&K>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        Some(self.map.get_key_value(value)?.0)
    }

    /// Returns a reference to the first (lexicographically smallest) element
    /// in the set.
    ///
    /// Returns `None` if the set is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let set: TreeSet<u8> = [3, 1, 2].into_iter().collect();
    /// assert_eq!(set.first(), Some(&1u8));
    /// ```
    pub fn first(&self) -> Option<&K>
    where
        K: AsBytes,
    {
        Some(self.map.first_key_value()?.0)
    }

    /// Returns a reference to the last (lexicographically greatest) element
    /// in the set.
    ///
    /// Returns `None` if the set is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let set: TreeSet<u8> = [3, 1, 2].into_iter().collect();
    /// assert_eq!(set.last(), Some(&3u8));
    /// ```
    pub fn last(&self) -> Option<&K>
    where
        K: AsBytes,
    {
        Some(self.map.last_key_value()?.0)
    }

    /// Removes the first element from the set and returns it, if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set: TreeSet<u8> = [3, 1, 2].into_iter().collect();
    /// assert_eq!(set.pop_first(), Some(1u8));
    /// assert_eq!(set.pop_first(), Some(2u8));
    /// assert_eq!(set.pop_first(), Some(3u8));
    /// assert_eq!(set.pop_first(), None);
    /// ```
    pub fn pop_first(&mut self) -> Option<K>
    where
        K: AsBytes,
    {
        Some(self.map.pop_first()?.0)
    }

    /// Removes the last element from the set and returns it, if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set: TreeSet<u8> = [3, 1, 2].into_iter().collect();
    /// assert_eq!(set.pop_last(), Some(3u8));
    /// assert_eq!(set.pop_last(), Some(2u8));
    /// assert_eq!(set.pop_last(), Some(1u8));
    /// assert_eq!(set.pop_last(), None);
    /// ```
    pub fn pop_last(&mut self) -> Option<K>
    where
        K: AsBytes,
    {
        Some(self.map.pop_last()?.0)
    }

    /// Adds a value to the set.
    ///
    /// Returns `true` if the value was not already present, `false` if it was.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set = TreeSet::new();
    /// assert!(set.insert(1u8));
    /// assert!(!set.insert(1u8));
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: K) -> bool
    where
        K: NoPrefixesBytes,
    {
        self.map.insert(value, ()).is_none()
    }

    /// Attempt to add a value to the set.
    ///
    /// If the set did not have this value `Ok(true)` is returned, if it was
    /// present `Ok(false)` is returned.
    ///
    /// # Errors
    ///
    /// If the map has an existing key, such that the new key is a prefix of
    /// the existing key or vice versa, then it returns an error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set = TreeSet::<Box<[u8]>>::new();
    ///
    /// assert!(set.try_insert(Box::new([1, 2, 3])).unwrap());
    /// assert!(set.try_insert(Box::new([2, 3, 4])).unwrap());
    /// // This function call errors because the key is a prefix of the existing key
    /// assert!(set.try_insert(Box::new([2, 3, 4, 5])).is_err());
    /// // This function call returns false because the value was already present in the set
    /// assert!(!set.try_insert(Box::new([2, 3, 4])).unwrap());
    ///
    /// assert_eq!(set.len(), 2);
    /// ```
    pub fn try_insert(&mut self, value: K) -> Result<bool, InsertPrefixError>
    where
        K: AsBytes,
    {
        self.map.try_insert(value, ()).map(|opt| opt.is_none())
    }

    /// Adds a value to the set, replacing the existing equal value if present.
    ///
    /// Returns the replaced value if the set contained an equal element.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// assert_eq!(set.replace(2u8), Some(2u8));
    /// assert_eq!(set.replace(4u8), None);
    /// ```
    pub fn replace(&mut self, value: K) -> Option<K>
    where
        K: NoPrefixesBytes,
    {
        let old = self.map.remove_entry(&value).map(|(k, ())| k);
        let _ = self.map.insert(value, ());
        old
    }

    /// Removes a value from the set.
    ///
    /// Returns `true` if the value was present in the set.
    ///
    /// The value may be any borrowed form of the set's element type, but
    /// [`AsBytes`] on the borrowed form must match that of the element type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// assert!(set.remove(&2u8));
    /// assert!(!set.remove(&2u8));
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        self.map.remove(value).is_some()
    }

    /// Removes and returns the element in the set, if any, that is equal to
    /// the given value.
    ///
    /// The value may be any borrowed form of the set's element type, but
    /// [`AsBytes`] on the borrowed form must match that of the element type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// assert_eq!(set.take(&2u8), Some(2u8));
    /// assert_eq!(set.take(&2u8), None);
    /// ```
    pub fn take<Q>(&mut self, value: &Q) -> Option<K>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        Some(self.map.remove_entry(value)?.0)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// Removes all elements for which `f(&element)` returns `false`. The
    /// elements are visited in ascending byte-sorted order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set: TreeSet<u8> = (0..8u8).collect();
    /// set.retain(|&x| x % 2 == 0);
    /// assert_eq!(set.iter().copied().collect::<Vec<_>>(), [0, 2, 4, 6]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        K: AsBytes,
        F: FnMut(&K) -> bool,
    {
        self.map.retain(|k, _| f(k))
    }

    /// Moves all elements from `other` into `self`, leaving `other` empty.
    ///
    /// If an element is present in both sets, the element from `other` is
    /// kept (overwrites the one from `self`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut a: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// let mut b: TreeSet<u8> = [3, 4, 5].into_iter().collect();
    /// a.append(&mut b);
    /// assert_eq!(a.len(), 5);
    /// assert!(b.is_empty());
    /// assert_eq!(
    ///     a.iter().copied().collect::<Vec<_>>(),
    ///     vec![1, 2, 3, 4, 5]
    /// );
    /// ```
    pub fn append(&mut self, other: &mut Self)
    where
        K: NoPrefixesBytes,
    {
        self.map.append(&mut other.map)
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the
    /// set.
    ///
    /// The simplest way is to use the range syntax `min..max`, thus
    /// `range(min..max)` will yield elements from min (inclusive) to max
    /// (exclusive). The range may also be entered as `(Bound<T>, Bound<T>)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let set: TreeSet<u8> = (1..=10u8).collect();
    /// let range: Vec<_> = set.range(3u8..=7u8).copied().collect();
    /// assert_eq!(range, [3, 4, 5, 6, 7]);
    /// ```
    pub fn range<Q, R>(&self, range: R) -> iterators::Range<'_, K, PREFIX_LEN, A>
    where
        Q: AsBytes + ?Sized,
        K: Borrow<Q> + AsBytes,
        R: RangeBounds<Q>,
    {
        iterators::Range(self.map.range(range))
    }

    /// Splits the set into two at the given value. Returns a new set
    /// containing all elements greater than or equal to the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut a: TreeSet<u8> = (0..8u8).collect();
    /// let b = a.split_off(&4u8);
    /// assert_eq!(a.iter().copied().collect::<Vec<_>>(), [0, 1, 2, 3]);
    /// assert_eq!(b.iter().copied().collect::<Vec<_>>(), [4, 5, 6, 7]);
    /// ```
    pub fn split_off<Q>(&mut self, split_key: &Q) -> Self
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
        A: Clone,
    {
        TreeSet {
            map: self.map.split_off(split_key),
        }
    }

    /// Creates an iterator that visits elements in ascending order and uses a
    /// closure to determine whether to remove them.
    ///
    /// If the closure returns `true`, the element is removed and yielded. If
    /// the closure returns `false`, the element is kept and the iterator moves
    /// on.
    ///
    /// If the returned iterator is dropped without being fully consumed, then
    /// the remaining elements will be retained.
    ///
    /// The `range` parameter allows filtering to a sub-range of the set.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let mut set: TreeSet<u8> = (0..8u8).collect();
    /// let evens: Vec<_> = set.extract_if(.., |x| x % 2 == 0).collect();
    /// assert_eq!(evens, [0, 2, 4, 6]);
    /// assert_eq!(set.iter().copied().collect::<Vec<_>>(), [1, 3, 5, 7]);
    /// ```
    pub fn extract_if<'a, R, F>(&'a mut self, range: R, mut pred: F) -> impl Iterator<Item = K> + 'a
    where
        K: AsBytes,
        R: RangeBounds<K>,
        F: FnMut(&K) -> bool + 'a,
    {
        self.map
            .extract_if(range, move |k, _| pred(k))
            .map(|(k, ())| k)
    }

    /// Gets an iterator that visits the elements of the set in ascending
    /// byte-sorted order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let set: TreeSet<u8> = [3, 1, 2].into_iter().collect();
    /// let items: Vec<_> = set.iter().copied().collect();
    /// assert_eq!(items, [1, 2, 3]);
    /// ```
    pub fn iter(&self) -> iterators::Iter<'_, K, PREFIX_LEN, A> {
        iterators::Iter(self.map.keys())
    }

    /// Visits the elements representing the difference, i.e., the elements that
    /// are in `self` but not in `other`, in ascending byte-sorted order.
    ///
    /// Requires `K: OrderedBytes` to guarantee that the byte-sorted iteration
    /// order matches the `Ord` order used by the merge algorithm.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let a: TreeSet<u8> = [1, 2, 3, 5].into_iter().collect();
    /// let b: TreeSet<u8> = [2, 4, 5, 6].into_iter().collect();
    /// let diff: Vec<_> = a.difference(&b).copied().collect();
    /// assert_eq!(diff, [1, 3]);
    /// ```
    pub fn difference<'a>(&'a self, other: &'a Self) -> iterators::Difference<'a, K, PREFIX_LEN, A>
    where
        K: OrderedBytes,
    {
        iterators::Difference {
            iter_self: self.iter().peekable(),
            iter_other: other.iter().peekable(),
        }
    }

    /// Visits the elements representing the symmetric difference, i.e., the
    /// elements that are in `self` or in `other` but not in both, in ascending
    /// byte-sorted order.
    ///
    /// Requires `K: OrderedBytes` to guarantee that the byte-sorted iteration
    /// order matches the `Ord` order used by the merge algorithm.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let a: TreeSet<u8> = [1, 2, 3, 5].into_iter().collect();
    /// let b: TreeSet<u8> = [2, 4, 5, 6].into_iter().collect();
    /// let sd: Vec<_> = a.symmetric_difference(&b).copied().collect();
    /// assert_eq!(sd, [1, 3, 4, 6]);
    /// ```
    pub fn symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> iterators::SymmetricDifference<'a, K, PREFIX_LEN, A>
    where
        K: OrderedBytes,
    {
        iterators::SymmetricDifference {
            iter_self: self.iter().peekable(),
            iter_other: other.iter().peekable(),
        }
    }

    /// Visits the elements representing the intersection, i.e., the elements
    /// that are both in `self` and `other`, in ascending byte-sorted order.
    ///
    /// Requires `K: OrderedBytes` to guarantee that the byte-sorted iteration
    /// order matches the `Ord` order used by the merge algorithm.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let a: TreeSet<u8> = [1, 2, 3, 5].into_iter().collect();
    /// let b: TreeSet<u8> = [2, 4, 5, 6].into_iter().collect();
    /// let inter: Vec<_> = a.intersection(&b).copied().collect();
    /// assert_eq!(inter, [2, 5]);
    /// ```
    pub fn intersection<'a>(
        &'a self,
        other: &'a Self,
    ) -> iterators::Intersection<'a, K, PREFIX_LEN, A>
    where
        K: OrderedBytes,
    {
        iterators::Intersection {
            iter_self: self.iter().peekable(),
            iter_other: other.iter().peekable(),
        }
    }

    /// Visits the elements representing the union, i.e., all the elements in
    /// `self` or `other`, without duplicates, in ascending byte-sorted order.
    ///
    /// Requires `K: OrderedBytes` to guarantee that the byte-sorted iteration
    /// order matches the `Ord` order used by the merge algorithm.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let a: TreeSet<u8> = [1, 2, 3, 5].into_iter().collect();
    /// let b: TreeSet<u8> = [2, 4, 5, 6].into_iter().collect();
    /// let u: Vec<_> = a.union(&b).copied().collect();
    /// assert_eq!(u, [1, 2, 3, 4, 5, 6]);
    /// ```
    pub fn union<'a>(&'a self, other: &'a Self) -> iterators::Union<'a, K, PREFIX_LEN, A>
    where
        K: OrderedBytes,
    {
        iterators::Union {
            iter_self: self.iter().peekable(),
            iter_other: other.iter().peekable(),
        }
    }

    /// Returns `true` if `self` and `other` have no elements in common.
    ///
    /// Requires `K: OrderedBytes` to guarantee that the byte-sorted iteration
    /// order matches the `Ord` order used by the merge algorithm.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let a: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// let b: TreeSet<u8> = [4, 5, 6].into_iter().collect();
    /// assert!(a.is_disjoint(&b));
    /// let c: TreeSet<u8> = [3, 4, 5].into_iter().collect();
    /// assert!(!a.is_disjoint(&c));
    /// ```
    pub fn is_disjoint(&self, other: &Self) -> bool
    where
        K: OrderedBytes,
    {
        self.intersection(other).next().is_none()
    }

    /// Returns `true` if every element of `self` is contained in `other`.
    ///
    /// Requires `K: OrderedBytes` to guarantee that the byte-sorted iteration
    /// order matches the `Ord` order used by the merge algorithm.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let a: TreeSet<u8> = [1, 2].into_iter().collect();
    /// let b: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// assert!(a.is_subset(&b));
    /// assert!(!b.is_subset(&a));
    /// ```
    pub fn is_subset(&self, other: &Self) -> bool
    where
        K: OrderedBytes,
    {
        self.difference(other).next().is_none()
    }

    /// Returns `true` if every element of `other` is contained in `self`.
    ///
    /// Requires `K: OrderedBytes` to guarantee that the byte-sorted iteration
    /// order matches the `Ord` order used by the merge algorithm.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeSet;
    ///
    /// let a: TreeSet<u8> = [1, 2, 3].into_iter().collect();
    /// let b: TreeSet<u8> = [1, 2].into_iter().collect();
    /// assert!(a.is_superset(&b));
    /// assert!(!b.is_superset(&a));
    /// ```
    pub fn is_superset(&self, other: &Self) -> bool
    where
        K: OrderedBytes,
    {
        other.is_subset(self)
    }
}

impl<K, A, const PREFIX_LEN: usize> Clone for TreeSet<K, PREFIX_LEN, A>
where
    K: Clone + AsBytes,
    A: Clone + Allocator,
{
    fn clone(&self) -> Self {
        TreeSet {
            map: self.map.clone(),
        }
    }
}

impl<K, A, const PREFIX_LEN: usize> Debug for TreeSet<K, PREFIX_LEN, A>
where
    K: Debug,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<K, const PREFIX_LEN: usize> Default for TreeSet<K, PREFIX_LEN> {
    fn default() -> Self {
        Self::with_prefix_len()
    }
}

impl<'a, K, A, const PREFIX_LEN: usize> Extend<&'a K> for TreeSet<K, PREFIX_LEN, A>
where
    K: Copy + NoPrefixesBytes,
    A: Allocator,
{
    fn extend<T: IntoIterator<Item = &'a K>>(&mut self, iter: T) {
        for &value in iter {
            let _ = self.insert(value);
        }
    }
}

impl<K, A, const PREFIX_LEN: usize> Extend<K> for TreeSet<K, PREFIX_LEN, A>
where
    K: NoPrefixesBytes,
    A: Allocator,
{
    fn extend<T: IntoIterator<Item = K>>(&mut self, iter: T) {
        for value in iter {
            let _ = self.insert(value);
        }
    }
}

impl<K, const PREFIX_LEN: usize, const N: usize> From<[K; N]> for TreeSet<K, PREFIX_LEN>
where
    K: NoPrefixesBytes,
{
    fn from(arr: [K; N]) -> Self {
        let mut set = TreeSet::with_prefix_len();
        for value in arr {
            let _ = set.insert(value);
        }
        set
    }
}

impl<K, const PREFIX_LEN: usize> From<alloc::vec::Vec<K>> for TreeSet<K, PREFIX_LEN>
where
    K: NoPrefixesBytes,
{
    fn from(vec: alloc::vec::Vec<K>) -> Self {
        let mut set = TreeSet::with_prefix_len();
        for value in vec {
            let _ = set.insert(value);
        }
        set
    }
}

impl<K, const PREFIX_LEN: usize> FromIterator<K> for TreeSet<K, PREFIX_LEN>
where
    K: NoPrefixesBytes,
{
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
        let mut set = TreeSet::with_prefix_len();
        for value in iter {
            let _ = set.insert(value);
        }
        set
    }
}

impl<K, A, const PREFIX_LEN: usize> Hash for TreeSet<K, PREFIX_LEN, A>
where
    K: Hash,
    A: Allocator,
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        hasher_write_length_prefix(state, self.map.len());
        for elt in self {
            elt.hash(state);
        }
    }
}

impl<'a, K, const PREFIX_LEN: usize, A: Allocator> IntoIterator for &'a TreeSet<K, PREFIX_LEN, A> {
    type IntoIter = iterators::Iter<'a, K, PREFIX_LEN, A>;
    type Item = &'a K;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K, const PREFIX_LEN: usize, A: Allocator> IntoIterator for TreeSet<K, PREFIX_LEN, A> {
    type IntoIter = iterators::IntoIter<K, PREFIX_LEN, A>;
    type Item = K;

    fn into_iter(self) -> Self::IntoIter {
        iterators::IntoIter(self.map.into_keys())
    }
}

impl<K, A, const PREFIX_LEN: usize> Ord for TreeSet<K, PREFIX_LEN, A>
where
    K: Ord,
    A: Allocator,
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<K, A, const PREFIX_LEN: usize> PartialOrd for TreeSet<K, PREFIX_LEN, A>
where
    K: PartialOrd,
    A: Allocator,
{
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K, A, const PREFIX_LEN: usize> Eq for TreeSet<K, PREFIX_LEN, A>
where
    K: Eq,
    A: Allocator,
{
}

impl<K, A, const PREFIX_LEN: usize> PartialEq for TreeSet<K, PREFIX_LEN, A>
where
    K: PartialEq,
    A: Allocator,
{
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

// SAFETY: This is safe to implement if `K` is also `Send`.
// This container is safe to `Send` for the same reasons as other containers.
unsafe impl<K, A, const PREFIX_LEN: usize> Send for TreeSet<K, PREFIX_LEN, A>
where
    K: Send,
    A: Send + Allocator,
{
}

// SAFETY: This is safe to implement if `K` is also `Sync`.
// This container is safe to `Sync` for the same reasons as other containers.
unsafe impl<K, A, const PREFIX_LEN: usize> Sync for TreeSet<K, PREFIX_LEN, A>
where
    K: Sync,
    A: Sync + Allocator,
{
}

impl<K, const PREFIX_LEN: usize, A: Allocator> core::ops::BitAnd<&TreeSet<K, PREFIX_LEN, A>>
    for &TreeSet<K, PREFIX_LEN, A>
where
    K: OrderedBytes + NoPrefixesBytes + Clone,
{
    type Output = TreeSet<K, PREFIX_LEN>;

    fn bitand(self, rhs: &TreeSet<K, PREFIX_LEN, A>) -> Self::Output {
        self.intersection(rhs).cloned().collect()
    }
}

impl<K, const PREFIX_LEN: usize, A: Allocator> core::ops::BitOr<&TreeSet<K, PREFIX_LEN, A>>
    for &TreeSet<K, PREFIX_LEN, A>
where
    K: OrderedBytes + NoPrefixesBytes + Clone,
{
    type Output = TreeSet<K, PREFIX_LEN>;

    fn bitor(self, rhs: &TreeSet<K, PREFIX_LEN, A>) -> Self::Output {
        self.union(rhs).cloned().collect()
    }
}

impl<K, const PREFIX_LEN: usize, A: Allocator> core::ops::BitXor<&TreeSet<K, PREFIX_LEN, A>>
    for &TreeSet<K, PREFIX_LEN, A>
where
    K: OrderedBytes + NoPrefixesBytes + Clone,
{
    type Output = TreeSet<K, PREFIX_LEN>;

    fn bitxor(self, rhs: &TreeSet<K, PREFIX_LEN, A>) -> Self::Output {
        self.symmetric_difference(rhs).cloned().collect()
    }
}

impl<K, const PREFIX_LEN: usize, A: Allocator> core::ops::Sub<&TreeSet<K, PREFIX_LEN, A>>
    for &TreeSet<K, PREFIX_LEN, A>
where
    K: OrderedBytes + NoPrefixesBytes + Clone,
{
    type Output = TreeSet<K, PREFIX_LEN>;

    fn sub(self, rhs: &TreeSet<K, PREFIX_LEN, A>) -> Self::Output {
        self.difference(rhs).cloned().collect()
    }
}

#[cfg(test)]
mod tests {
    use alloc::{vec, vec::Vec};

    use super::*;

    fn make_set(values: &[u8]) -> TreeSet<u8> {
        values.iter().copied().collect()
    }

    #[test]
    fn tree_set_is_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}
        fn is_unwind_safe<T: core::panic::UnwindSafe>() {}
        fn is_ref_unwind_safe<T: core::panic::RefUnwindSafe>() {}

        is_send::<TreeSet<u8>>();
        is_sync::<TreeSet<u8>>();
        is_unwind_safe::<TreeSet<u8>>();
        is_ref_unwind_safe::<TreeSet<u8>>();
    }

    #[test]
    fn new_empty_set() {
        let set = TreeSet::<u8>::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
        assert_eq!(set.first(), None);
        assert_eq!(set.last(), None);
    }

    #[test]
    fn insert_and_contains() {
        let mut set = TreeSet::new();
        assert!(set.insert(1u8));
        assert!(set.insert(2u8));
        assert!(set.insert(3u8));
        assert!(!set.insert(2u8)); // duplicate
        assert_eq!(set.len(), 3);
        assert!(set.contains(&1u8));
        assert!(set.contains(&2u8));
        assert!(set.contains(&3u8));
        assert!(!set.contains(&4u8));
    }

    #[test]
    fn get_returns_stored_key() {
        let set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        assert_eq!(set.get(&2u8), Some(&2u8));
        assert_eq!(set.get(&4u8), None);
    }

    #[test]
    fn first_and_last() {
        let set: TreeSet<u8> = [3, 1, 2].into_iter().collect();
        assert_eq!(set.first(), Some(&1u8));
        assert_eq!(set.last(), Some(&3u8));
    }

    #[test]
    fn pop_first_and_last() {
        let mut set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        assert_eq!(set.pop_first(), Some(1));
        assert_eq!(set.pop_last(), Some(3));
        assert_eq!(set.pop_first(), Some(2));
        assert_eq!(set.pop_first(), None);
        assert_eq!(set.pop_last(), None);
    }

    #[test]
    fn remove_and_take() {
        let mut set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        assert!(set.remove(&2u8));
        assert!(!set.remove(&2u8));
        assert_eq!(set.len(), 2);

        assert_eq!(set.take(&1u8), Some(1));
        assert_eq!(set.take(&1u8), None);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn replace() {
        let mut set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        // replace existing → returns old value
        assert_eq!(set.replace(2u8), Some(2u8));
        assert_eq!(set.len(), 3);
        // replace non-existing → returns None
        assert_eq!(set.replace(4u8), None);
        assert_eq!(set.len(), 4);
    }

    #[test]
    fn clear() {
        let mut set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        set.clear();
        assert!(set.is_empty());
    }

    #[test]
    fn retain() {
        let mut set: TreeSet<u8> = (0..8u8).collect();
        set.retain(|&x| x % 2 == 0);
        let items: Vec<_> = set.iter().copied().collect();
        assert_eq!(items, vec![0u8, 2, 4, 6]);
    }

    #[test]
    fn append() {
        let mut a: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        let mut b: TreeSet<u8> = [3, 4, 5].into_iter().collect();
        a.append(&mut b);
        assert_eq!(a.len(), 5);
        assert!(b.is_empty());
    }

    #[test]
    fn split_off() {
        let mut a: TreeSet<u8> = (0..8u8).collect();
        let b = a.split_off(&4u8);
        let a_items: Vec<_> = a.iter().copied().collect();
        let b_items: Vec<_> = b.iter().copied().collect();
        assert_eq!(a_items, vec![0u8, 1, 2, 3]);
        assert_eq!(b_items, vec![4u8, 5, 6, 7]);
    }

    #[test]
    fn range_iteration() {
        let set: TreeSet<u8> = (1..=10u8).collect();
        let range: Vec<_> = set.range(3u8..=7u8).copied().collect();
        assert_eq!(range, vec![3u8, 4, 5, 6, 7]);

        let range2: Vec<_> = set.range(3u8..7u8).copied().collect();
        assert_eq!(range2, vec![3u8, 4, 5, 6]);
    }

    #[test]
    fn extract_if_removes_matched() {
        let mut set: TreeSet<u8> = (0..8u8).collect();
        let evens: Vec<_> = set.extract_if(.., |x| x % 2 == 0).collect();
        assert_eq!(evens, vec![0u8, 2, 4, 6]);
        let remaining: Vec<_> = set.iter().copied().collect();
        assert_eq!(remaining, vec![1u8, 3, 5, 7]);
    }

    #[test]
    fn iter_order() {
        let set: TreeSet<u8> = [5, 3, 1, 4, 2].into_iter().collect();
        let items: Vec<_> = set.iter().copied().collect();
        assert_eq!(items, vec![1u8, 2, 3, 4, 5]);
    }

    #[test]
    fn into_iter_consuming() {
        let set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        let items: Vec<_> = set.into_iter().collect();
        assert_eq!(items, vec![1u8, 2, 3]);
    }

    #[test]
    fn is_disjoint() {
        let a: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        let b: TreeSet<u8> = [4, 5, 6].into_iter().collect();
        assert!(a.is_disjoint(&b));
        let c: TreeSet<u8> = [3, 4, 5].into_iter().collect();
        assert!(!a.is_disjoint(&c));
    }

    #[test]
    fn is_subset_superset() {
        let a: TreeSet<u8> = [1, 2].into_iter().collect();
        let b: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        assert!(a.is_subset(&b));
        assert!(b.is_superset(&a));
        assert!(!b.is_subset(&a));
        assert!(!a.is_superset(&b));

        // Every set is a subset of itself
        assert!(a.is_subset(&a));
        // Empty set is subset of everything
        let empty: TreeSet<u8> = TreeSet::new();
        assert!(empty.is_subset(&a));
        assert!(!a.is_subset(&empty));
    }

    #[test]
    fn difference() {
        let a = make_set(&[1, 2, 3, 5]);
        let b = make_set(&[2, 4, 5, 6]);
        let diff: Vec<_> = a.difference(&b).copied().collect();
        assert_eq!(diff, vec![1u8, 3]);
    }

    #[test]
    fn intersection() {
        let a = make_set(&[1, 2, 3, 5]);
        let b = make_set(&[2, 4, 5, 6]);
        let inter: Vec<_> = a.intersection(&b).copied().collect();
        assert_eq!(inter, vec![2u8, 5]);
    }

    #[test]
    fn union() {
        let a = make_set(&[1, 2, 3, 5]);
        let b = make_set(&[2, 4, 5, 6]);
        let u: Vec<_> = a.union(&b).copied().collect();
        assert_eq!(u, vec![1u8, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn symmetric_difference() {
        let a = make_set(&[1, 2, 3, 5]);
        let b = make_set(&[2, 4, 5, 6]);
        let sd: Vec<_> = a.symmetric_difference(&b).copied().collect();
        assert_eq!(sd, vec![1u8, 3, 4, 6]);
    }

    #[test]
    fn set_operators() {
        let a = make_set(&[1, 2, 3, 5]);
        let b = make_set(&[2, 4, 5, 6]);

        let inter: Vec<_> = (&a & &b).into_iter().collect();
        assert_eq!(inter, vec![2u8, 5]);

        let u: Vec<_> = (&a | &b).into_iter().collect();
        assert_eq!(u, vec![1u8, 2, 3, 4, 5, 6]);

        let sd: Vec<_> = (&a ^ &b).into_iter().collect();
        assert_eq!(sd, vec![1u8, 3, 4, 6]);

        let diff: Vec<_> = (&a - &b).into_iter().collect();
        assert_eq!(diff, vec![1u8, 3]);
    }

    #[test]
    fn clone_and_eq() {
        let a = make_set(&[1, 2, 3]);
        let b = a.clone();
        assert_eq!(a, b);
        let c = make_set(&[1, 2, 4]);
        assert_ne!(a, c);
    }

    #[test]
    fn debug_format() {
        let set: TreeSet<u8> = [1, 2, 3].into_iter().collect();
        let s = alloc::format!("{set:?}");
        assert!(s.contains('1') && s.contains('2') && s.contains('3'));
    }

    #[test]
    fn default_is_empty() {
        let set = TreeSet::<u8>::default();
        assert!(set.is_empty());
    }

    #[test]
    fn from_array_and_vec() {
        let a = TreeSet::<u8>::from([3u8, 1, 2]);
        let items: Vec<_> = a.iter().copied().collect();
        assert_eq!(items, vec![1u8, 2, 3]);

        let b = TreeSet::<u8>::from(vec![3u8, 1, 2]);
        assert_eq!(a, b);
    }

    #[test]
    fn extend() {
        let mut a = make_set(&[1, 2]);
        a.extend([3u8, 4]);
        assert_eq!(a.len(), 4);
        a.extend([&5u8, &6u8]);
        assert_eq!(a.len(), 6);
    }

    #[test]
    fn ord_comparison() {
        let a = make_set(&[1, 2, 3]);
        let b = make_set(&[1, 2, 4]);
        assert!(a < b);
        assert!(b > a);
        let c = make_set(&[1, 2, 3]);
        assert!(a <= c);
        assert!(a >= c);
    }

    #[test]
    fn empty_set_operations() {
        let empty: TreeSet<u8> = TreeSet::new();
        let a = make_set(&[1, 2, 3]);

        let diff: Vec<_> = empty.difference(&a).copied().collect();
        assert!(diff.is_empty());

        let diff2: Vec<_> = a.difference(&empty).copied().collect();
        assert_eq!(diff2, vec![1u8, 2, 3]);

        let inter: Vec<_> = empty.intersection(&a).copied().collect();
        assert!(inter.is_empty());

        let u: Vec<_> = empty.union(&a).copied().collect();
        assert_eq!(u, vec![1u8, 2, 3]);

        let sd: Vec<_> = empty.symmetric_difference(&a).copied().collect();
        assert_eq!(sd, vec![1u8, 2, 3]);
    }
}
