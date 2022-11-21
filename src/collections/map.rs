//! Module containing implementations of the `TreeMap` and associated
//! iterators/etc.

use crate::{
    deallocate_tree, delete_maximum_unchecked, delete_minimum_unchecked, delete_unchecked,
    insert_unchecked, maximum_unchecked, minimum_unchecked, search_unchecked, DeleteResult,
    InsertPrefixError, InsertResult, LeafNode, NodePtr, OpaqueNodePtr,
};
use std::{
    fmt::Debug,
    hash::Hash,
    ops::{Index, RangeBounds},
};

mod iterators;
pub use iterators::*;

/// An ordered map based on an adaptive radix tree.
pub struct TreeMap<V> {
    /// The number of entries present in the tree.
    num_entries: usize,
    /// A pointer to the tree root, if present.
    root: Option<OpaqueNodePtr<V>>,
}

impl<V> TreeMap<V> {
    /// Create a new, empty [`TreeMap`].
    ///
    /// This function will not pre-allocate anything.
    pub fn new() -> Self {
        TreeMap {
            num_entries: 0,
            root: None,
        }
    }

    /// Clear the map, removing all elements.
    pub fn clear(&mut self) {
        if let Some(root) = self.root {
            // SAFETY: Since we have a mutable reference to the map, we know that there are
            // no other mutable references to any node in the tree, meaning we can
            // deallocate all of them.
            unsafe {
                deallocate_tree(root);
            }

            self.num_entries = 0;
            self.root = None;
        }
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get<K>(&self, k: K) -> Option<&V>
    where
        K: AsRef<[u8]>,
    {
        Some(self.get_key_value(k)?.1)
    }

    /// Returns the key-value pair corresponding to the supplied key.
    pub fn get_key_value<K>(&self, k: K) -> Option<(&[u8], &V)>
    where
        K: AsRef<[u8]>,
    {
        if let Some(root) = self.root {
            let key = k.as_ref();

            // SAFETY: Since we have an immutable reference to the `TreeMap` object, that
            // means there can only exist other immutable references aside from this one,
            // and no mutable references. That means that no mutating operations can occur
            // on the root node or any child of the root node.
            let search_result = unsafe { search_unchecked(root, key)? };

            // SAFETY: The lifetime chosen the value reference is bounded by the lifetime of
            // the immutable reference to the `TreeMap`. The memory of the value will not be
            // mutated since it is only owned by the `TreeMap` and there can only be other
            // immutable references at this time (no mutable references to the `TreeMap`).
            let (key, value) = unsafe { search_result.as_key_value_ref() };
            Some((key.as_ref(), value))
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut<K>(&self, k: K) -> Option<&mut V>
    where
        K: AsRef<[u8]>,
    {
        if let Some(root) = self.root {
            let key = k.as_ref();

            // SAFETY: Since we have a mutable reference to the `TreeMap` object, that
            // means there cannot exist any other reference (mutable or immutable) to the
            // same `TreeMap`. Which means that no other mutating operations could be
            // happening during the `search_unchecked` call.
            let search_result = unsafe { search_unchecked(root, key)? };

            // SAFETY: The lifetime chosen the value reference is bounded by the lifetime of
            // the mutable reference to the `TreeMap`. The value pointed to by the returned
            // mutable reference will not be accessed (read or written) through any other
            // pointer because of the existing mutable reference on the `TreeMap`.
            let leaf_node_ref = unsafe { search_result.as_mut() };

            Some(&mut leaf_node_ref.value)
        } else {
            None
        }
    }

    /// Returns true if the map contains a value for the specified key.
    pub fn contains_key<K>(&self, k: K) -> bool
    where
        K: AsRef<[u8]>,
    {
        // TODO(#18): Optimize this with a specific underlying method which just check
        // for existing leaf, does not return it
        self.get(k).is_some()
    }

    /// Returns the first key-value pair in the map. The key in this pair is the
    /// minimum key in the map.
    ///
    /// If the tree is empty, returns None.
    pub fn first_key_value(&self) -> Option<(&[u8], &V)> {
        if let Some(root) = self.root {
            // SAFETY: Since we have an immutable reference to the `TreeMap` object, that
            // means there can only exist other immutable references aside from this one,
            // and no mutable references. That means that no mutating operations can occur
            // on the root node or any child of the root node.
            let minimum = unsafe { minimum_unchecked(root) };

            // SAFETY: The lifetime chosen the value reference is bounded by the lifetime of
            // the immutable reference to the `TreeMap`. The memory of the value will not be
            // mutated since it is only owned by the `TreeMap` and there can only be other
            // immutable references at this time (no mutable references to the `TreeMap`).
            let leaf_node_ref = unsafe { minimum.as_ref() };

            Some((leaf_node_ref.key.as_ref(), &leaf_node_ref.value))
        } else {
            None
        }
    }

    /// Removes and returns the first element in the map. The key of this
    /// element is the minimum key that was in the map.
    ///
    /// If the tree is empty, returns None.
    pub fn pop_first(&mut self) -> Option<(Box<[u8]>, V)> {
        if let Some(root) = self.root {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let DeleteResult {
                deleted_leaf,
                new_root,
            } = unsafe { delete_minimum_unchecked(root) };

            self.root = new_root;
            self.num_entries -= 1;
            Some((deleted_leaf.key, deleted_leaf.value))
        } else {
            None
        }
    }

    /// Returns the last key-value pair in the map. The key in this pair is the
    /// maximum key in the map.
    ///
    /// If the tree is empty, returns None.
    pub fn last_key_value(&self) -> Option<(&[u8], &V)> {
        if let Some(root) = self.root {
            // SAFETY: Since we have an immutable reference to the `TreeMap` object, that
            // means there can only exist other immutable references aside from this one,
            // and no mutable references. That means that no mutating operations can occur
            // on the root node or any child of the root node.
            let maximum = unsafe { maximum_unchecked(root) };

            // SAFETY: The lifetime chosen the value reference is bounded by the lifetime of
            // the immutable reference to the `TreeMap`. The memory of the value will not be
            // mutated since it is only owned by the `TreeMap` and there can only be other
            // immutable references at this time (no mutable references to the `TreeMap`).
            let leaf_node_ref = unsafe { maximum.as_ref() };

            Some((leaf_node_ref.key.as_ref(), &leaf_node_ref.value))
        } else {
            None
        }
    }

    /// Removes and returns the last element in the map. The key of this element
    /// is the maximum key that was in the map.
    ///
    /// If the tree is empty, returns None.
    pub fn pop_last(&mut self) -> Option<(Box<[u8]>, V)> {
        if let Some(root) = self.root {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let DeleteResult {
                deleted_leaf,
                new_root,
            } = unsafe { delete_maximum_unchecked(root) };

            self.root = new_root;
            self.num_entries -= 1;
            Some((deleted_leaf.key, deleted_leaf.value))
        } else {
            None
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, Ok(None) is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned.
    ///
    /// # Errors
    ///  - If the map has an existing key, such that the new key is a prefix of
    ///    the existing key or vice versa, then it returns an error.
    pub fn try_insert(&mut self, key: Box<[u8]>, value: V) -> Result<Option<V>, InsertPrefixError> {
        if let Some(root) = self.root {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let InsertResult {
                existing_leaf,
                new_root,
            } = unsafe { insert_unchecked(root, key, value)? };

            self.root = Some(new_root);

            if existing_leaf.is_none() {
                // this was a strict add, not a replace. If there was an existing leaf we are
                // removing and adding a leaf, so the number of entries stays the same
                self.num_entries = self
                    .num_entries
                    .checked_add(1)
                    .expect("should not overflow a usize");
            }

            Ok(existing_leaf.map(|leaf| leaf.value))
        } else {
            self.root = Some(NodePtr::allocate_node_ptr(LeafNode::new(key, value)).to_opaque());

            self.num_entries = 1;

            Ok(None)
        }
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
    pub fn remove_entry<K>(&mut self, k: K) -> Option<(Box<[u8]>, V)>
    where
        K: AsRef<[u8]>,
    {
        if let Some(root) = self.root {
            let key = k.as_ref();
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let DeleteResult {
                deleted_leaf,
                new_root,
            } = unsafe { delete_unchecked(root, key)? };

            // The `delete_unchecked` returns early if the key was not found, we are
            // guaranteed at this point that the leaf has been removed from the tree.
            self.num_entries = self
                .num_entries
                .checked_sub(1)
                .expect("should not underflow, inc/dec should be paired");

            self.root = new_root;
            Some((deleted_leaf.key, deleted_leaf.value))
        } else {
            None
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    pub fn remove<K>(&mut self, k: K) -> Option<V>
    where
        K: AsRef<[u8]>,
    {
        self.remove_entry(k).map(|(_, v)| v)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs (k, v) for which f(&k, &mut v) returns
    /// false. The elements are visited in ascending key order.
    pub fn retain<F>(&mut self, _f: F)
    where
        F: FnMut(&[u8], &mut V) -> bool,
    {
        // Special care needs to be taken to be panic-safe for the closure
        todo!()
    }

    /// Moves all elements from other into self, leaving other empty.
    pub fn append(&mut self, _other: &mut TreeMap<V>) {
        todo!()
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the
    /// map.
    ///
    /// The simplest way is to use the range syntax `min..max`, thus
    /// `range(min..max)` will yield elements from min (inclusive) to max
    /// (exclusive). The range may also be entered as `(Bound<T>, Bound<T>)`, so
    /// for example `range((Excluded(4), Included(10)))` will yield a
    /// left-exclusive, right-inclusive range from 4 to 10.
    pub fn range<R, K>(&self, _range: R) -> iterators::Range<V>
    where
        K: AsRef<[u8]>,
        R: RangeBounds<K>,
    {
        todo!()
    }

    /// Constructs a mutable double-ended iterator over a sub-range of elements
    /// in the map.
    ///
    /// The simplest way is to use the range syntax `min..max`, thus
    /// `range+_mut(min..max)` will yield elements from min (inclusive) to max
    /// (exclusive). The range may also be entered as `(Bound<T>, Bound<T>)`, so
    /// for example `range_mut((Excluded(4), Included(10)))` will yield a
    /// left-exclusive, right-inclusive range from 4 to 10.
    pub fn range_mut<R, K>(&mut self, _range: R) -> iterators::RangeMut<V>
    where
        K: AsRef<[u8]>,
        R: RangeBounds<K>,
    {
        todo!()
    }

    /// Splits the collection into two at the given key. Returns everything
    /// after the given key, including the key.
    pub fn split_off<K>(&mut self, _k: K) -> TreeMap<V>
    where
        K: AsRef<[u8]>,
    {
        todo!()
    }

    /// Creates an iterator that visits all elements (key-value pairs) in
    /// ascending key order and uses a closure to determine if an element should
    /// be removed.
    ///
    /// If the closure returns true, the element is removed from the map and
    /// yielded. If the closure returns false, or panics, the element
    /// remains in the map and will not be yielded.
    ///
    /// The iterator also lets you mutate the value of each element in the
    /// closure, regardless of whether you choose to keep or remove it.
    ///
    /// If the iterator is only partially consumed or not consumed at all, each
    /// of the remaining elements is still subjected to the closure, which may
    /// change its value and, by returning true, have the element removed and
    /// dropped.
    ///
    /// It is unspecified how many more elements will be subjected to the
    /// closure if a panic occurs in the closure, or a panic occurs while
    /// dropping an element, or if the DrainFilter value is leaked.
    pub fn drain_filter<F>(&mut self, _pred: F) -> iterators::DrainFilter<V>
    where
        F: FnMut(&[u8], &mut V) -> bool,
    {
        todo!()
    }

    /// Creates a consuming iterator visiting all the keys, in sorted order. The
    /// map cannot be used after calling this. The iterator element type is `K`.
    pub fn into_keys(self) -> iterators::IntoKeys<V> {
        iterators::IntoKeys::new(self)
    }

    /// Creates a consuming iterator visiting all the values, in order by key.
    /// The map cannot be used after calling this. The iterator element type is
    /// `V`.
    pub fn into_values(self) -> iterators::IntoValues<V> {
        iterators::IntoValues::new(self)
    }

    /// Gets an iterator over the entries of the map, sorted by key.
    pub fn iter(&self) -> iterators::Iter<'_, V> {
        iterators::Iter::new(self)
    }

    /// Gets a mutable iterator over the entries of the map, sorted by key.
    pub fn iter_mut(&mut self) -> iterators::IterMut<'_, V> {
        iterators::IterMut::new(self)
    }

    /// Gets an iterator over the keys of the map, in sorted order.
    pub fn keys(&self) -> iterators::Keys<'_, V> {
        iterators::Keys::new(self)
    }

    /// Gets an iterator over the values of the map, in order by key.
    pub fn values(&self) -> iterators::Values<'_, V> {
        iterators::Values::new(self)
    }

    /// Gets a mutable iterator over the values of the map, in order by key.
    pub fn values_mut(&mut self) -> iterators::ValuesMut<'_, V> {
        iterators::ValuesMut::new(self)
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.num_entries
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.num_entries == 0
    }
}

impl<V> Drop for TreeMap<V> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<V: Clone> Clone for TreeMap<V> {
    fn clone(&self) -> Self {
        // TODO(#17) Optimize clone operation with custom function
        self.iter()
            .map(|(key, value)| (Box::from(key), value.clone()))
            .collect()
    }
}

impl<V: Debug> Debug for TreeMap<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<V> Default for TreeMap<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, V: Copy> Extend<(&'a [u8], &'a V)> for TreeMap<V> {
    fn extend<T: IntoIterator<Item = (&'a [u8], &'a V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            // TODO(#16): We can create an infalliable version of this using `NoPrefixKey`
            // trait, which allow to remove the `expect`
            self.try_insert(key.to_owned().into_boxed_slice(), *value)
                .expect("should not fail extend");
        }
    }
}

impl<V> Extend<(Box<[u8]>, V)> for TreeMap<V> {
    fn extend<T: IntoIterator<Item = (Box<[u8]>, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            // TODO(#16): We can create an infalliable version of this using `NoPrefixKey`
            // trait, which allow to remove the `expect`
            self.try_insert(key, value).expect("should not fail extend");
        }
    }
}

impl<V, const N: usize> From<[(Box<[u8]>, V); N]> for TreeMap<V> {
    fn from(arr: [(Box<[u8]>, V); N]) -> Self {
        let mut map = TreeMap::new();
        for (key, value) in arr {
            // TODO(#16): We can create an infalliable version of this using `NoPrefixKey`
            // trait, which allow to remove the `expect`
            map.try_insert(key, value).expect("should not fail extend");
        }
        map
    }
}

impl<V> FromIterator<(Box<[u8]>, V)> for TreeMap<V> {
    fn from_iter<T: IntoIterator<Item = (Box<[u8]>, V)>>(iter: T) -> Self {
        let mut map = TreeMap::new();
        for (key, value) in iter {
            // TODO(#16): We can create an infalliable version of this using `NoPrefixKey`
            // trait, which allow to remove the `expect`
            map.try_insert(key, value).expect("should not fail extend");
        }
        map
    }
}

impl<V: Hash> Hash for TreeMap<V> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        crate::nightly_rust_apis::hasher_write_length_prefix(state, self.num_entries);
        for elt in self {
            elt.hash(state);
        }
    }
}

impl<K: AsRef<[u8]>, V> Index<&K> for TreeMap<V> {
    type Output = V;

    fn index(&self, index: &K) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<'a, V> IntoIterator for &'a TreeMap<V> {
    type IntoIter = iterators::Iter<'a, V>;
    type Item = (&'a [u8], &'a V);

    fn into_iter(self) -> Self::IntoIter {
        TreeMap::iter(self)
    }
}

impl<'a, V> IntoIterator for &'a mut TreeMap<V> {
    type IntoIter = iterators::IterMut<'a, V>;
    type Item = (&'a [u8], &'a mut V);

    fn into_iter(self) -> Self::IntoIter {
        TreeMap::iter_mut(self)
    }
}

impl<V> IntoIterator for TreeMap<V> {
    type IntoIter = iterators::IntoIter<V>;
    type Item = (Box<[u8]>, V);

    fn into_iter(self) -> Self::IntoIter {
        iterators::IntoIter::new(self)
    }
}

impl<V: Ord> Ord for TreeMap<V> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<V: PartialOrd> PartialOrd for TreeMap<V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<V: Eq> Eq for TreeMap<V> {}

impl<V: PartialEq> PartialEq for TreeMap<V> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

#[cfg(test)]
mod tests {
    use std::{
        cmp::Ordering,
        collections::hash_map::RandomState,
        hash::{BuildHasher, Hasher},
    };

    use super::*;

    #[test]
    fn tree_map_create_empty() {
        let map = TreeMap::<()>::new();

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn tree_map_get_non_existent_entry_different_keys_types() {
        let map = TreeMap::<()>::new();

        assert_eq!(map.get(b"123456789"), None);
        let k = b"123456789".into_iter().copied().collect::<Vec<_>>();
        assert_eq!(map.get(k), None);
        assert_eq!(map.get([1u8, 2, 3, 4, 5, 6, 7, 8, 9]), None);
    }

    #[test]
    fn tree_map_insert_get_modify_remove_len() {
        fn tree_map_test_insert_get_remove_len<const N: usize>(keys: [&[u8]; N]) {
            let mut map = TreeMap::new();

            assert!(map.is_empty());
            assert_eq!(map.len(), 0);

            for (index, key) in keys.iter().enumerate() {
                assert!(map.try_insert(Box::from(*key), index).unwrap().is_none());

                assert_eq!(map.len(), index + 1);

                for other_key in keys.iter().skip(index + 1) {
                    assert!(map.get(other_key).is_none(), "{:?} {:?}", map, other_key);
                }

                assert_eq!(*map.get(key).unwrap(), index);
            }

            assert_eq!(map.len(), keys.len());

            for (value, key) in keys.iter().enumerate() {
                assert_eq!(*map.get(key).unwrap(), value);

                let value = map.get_mut(key).unwrap();
                *value *= 2;
            }

            for (index, key) in keys.iter().enumerate() {
                assert_eq!(map.remove(key).unwrap(), index * 2);

                for other_key in keys.iter().skip(index + 1) {
                    assert!(map.get(other_key).is_some());
                }

                assert!(map.get(key).is_none());
            }

            assert!(map.is_empty());
            assert_eq!(map.len(), 0);
        }

        tree_map_test_insert_get_remove_len([
            b"0000", b"0001", b"0002", b"0003", b"0004", b"0010", b"0011", b"0012", b"0013",
            b"0014",
        ]);

        tree_map_test_insert_get_remove_len([
            b"0",
            b"10",
            b"110",
            b"1110",
            b"11110",
            b"111110",
            b"1111110",
            b"11111110",
            b"111111110",
            b"1111111110",
        ]);
    }

    fn build_tree_map<const N: usize>(keys: [&[u8]; N]) -> TreeMap<usize> {
        let mut map = TreeMap::new();

        for (value, key) in keys.into_iter().enumerate() {
            assert!(map.try_insert(key.into(), value).unwrap().is_none());
        }

        map
    }

    #[test]
    fn tree_map_iterators() {
        let mut map = build_tree_map([
            b"0000", b"0001", b"0002", b"0003", b"0004", b"0005", b"0010", b"0011", b"0012",
            b"0013", b"0014", b"0015",
        ]);

        let even_values: Vec<_> = map
            .values()
            .copied()
            .filter(|value| value % 2 == 0)
            .collect();
        assert_eq!(even_values, [0, 2, 4, 6, 8, 10]);

        map.values_mut()
            .filter(|value| **value % 2 == 1)
            .for_each(|value| {
                // mutate all odd values to make them even
                *value *= 2;
            });

        let keys_with_less_zeros: Vec<_> =
            map.keys().filter(|key| !key.starts_with(b"000")).collect();
        assert_eq!(
            keys_with_less_zeros,
            [b"0010", b"0011", b"0012", b"0013", b"0014", b"0015"]
        );

        for (key, value) in &map {
            assert!(key.starts_with(b"000") || key.starts_with(b"001"));
            assert_eq!(*value % 2, 0);
        }

        for (key, value) in &mut map {
            let key = String::from_utf8(key.into()).unwrap();
            let key_number_value =
                usize::from_str_radix(key.trim_start_matches("0"), 10).unwrap_or(0);

            if key_number_value == *value {
                *value = 999;
            } else if key_number_value >= 10 {
                *value += 50;
            } else {
                *value = 0;
            }
        }

        assert_eq!(
            map.iter()
                .map(|(key, value)| (key, *value))
                .collect::<Vec<_>>(),
            [
                (&b"0000"[..], 999),
                (b"0001", 0),
                (b"0002", 999),
                (b"0003", 0),
                (b"0004", 999),
                (b"0005", 0),
                (b"0010", 56),
                (b"0011", 64),
                (b"0012", 58),
                (b"0013", 68),
                (b"0014", 60),
                (b"0015", 72)
            ]
        );
    }

    #[test]
    fn tree_check_eq_with_reflexive() {
        let map_a = build_tree_map([
            b"0000", b"0001", b"0002", b"0003", b"0004", b"0005", b"0010", b"0011", b"0012",
            b"0013", b"0014", b"0015",
        ]);
        let map_b = build_tree_map([b"0003", b"0004", b"0005", b"0010", b"0011", b"0012"]);
        let map_c = build_tree_map([
            b"0000", b"0001", b"0002", b"0003", b"0004", b"0005", b"0010", b"0011", b"0012",
        ]);
        let map_d = build_tree_map([b"0003", b"0004", b"0005", b"0010", b"0011", b"0012"]);

        assert_eq!(map_a, map_a);
        assert_ne!(map_a, map_b);
        assert_ne!(map_a, map_c);
        assert_ne!(map_a, map_d);

        assert_ne!(map_b, map_a);
        assert_eq!(map_b, map_b);
        assert_ne!(map_b, map_c);
        assert_eq!(map_b, map_d);

        assert_ne!(map_c, map_a);
        assert_ne!(map_c, map_b);
        assert_eq!(map_c, map_c);
        assert_ne!(map_c, map_d);

        assert_ne!(map_d, map_a);
        assert_eq!(map_d, map_b);
        assert_ne!(map_d, map_c);
        assert_eq!(map_d, map_d);
    }

    #[test]
    fn tree_check_compare_with_reflexive() {
        let map_a = build_tree_map([
            b"0000", b"0001", b"0002", b"0003", b"0004", b"0005", b"0010", b"0011", b"0012",
            b"0013", b"0014", b"0015",
        ]);
        let map_b = build_tree_map([b"0003", b"0004", b"0005", b"0010", b"0011", b"0012"]);
        let map_c = build_tree_map([
            b"0000", b"0001", b"0002", b"0003", b"0004", b"0005", b"0010", b"0011", b"0012",
        ]);
        let map_d = build_tree_map([b"0003", b"0004", b"0005", b"0010", b"0011", b"0012"]);

        assert_eq!(map_a.cmp(&map_a), Ordering::Equal);
        assert_eq!(map_a.cmp(&map_b), Ordering::Less);
        assert_eq!(map_a.cmp(&map_c), Ordering::Greater);
        assert_eq!(map_a.cmp(&map_d), Ordering::Less);

        assert_eq!(map_b.cmp(&map_a), Ordering::Greater);
        assert_eq!(map_b.cmp(&map_b), Ordering::Equal);
        assert_eq!(map_b.cmp(&map_c), Ordering::Greater);
        assert_eq!(map_b.cmp(&map_d), Ordering::Equal);

        assert_eq!(map_c.cmp(&map_a), Ordering::Less);
        assert_eq!(map_c.cmp(&map_b), Ordering::Less);
        assert_eq!(map_c.cmp(&map_c), Ordering::Equal);
        assert_eq!(map_c.cmp(&map_d), Ordering::Less);

        assert_eq!(map_d.cmp(&map_a), Ordering::Greater);
        assert_eq!(map_d.cmp(&map_b), Ordering::Equal);
        assert_eq!(map_d.cmp(&map_c), Ordering::Greater);
        assert_eq!(map_d.cmp(&map_d), Ordering::Equal);
    }

    fn hash_one(hasher_builder: &impl BuildHasher, value: impl Hash) -> u64 {
        let mut hasher = hasher_builder.build_hasher();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn tree_hash_equals() {
        let mut tree_a = TreeMap::<i32>::new();

        let _ = tree_a.try_insert(Box::from([]), 0);
        let _ = tree_a.pop_first();

        let tree_b = tree_a.clone();

        let hasher_builder = RandomState::new();

        let hash_a = hash_one(&hasher_builder, &tree_a);
        let hash_b = hash_one(&hasher_builder, &tree_b);

        assert_eq!(hash_a, hash_b);
    }

    #[test]
    fn mutating_operations_modify_len() {
        let mut tree = TreeMap::<u8>::new();

        // check the normal state, a tree should never have any existing entries
        assert!(tree.len() == 0 && tree.is_empty());

        // regular insert
        assert_eq!(tree.try_insert(Box::new([1]), 0), Ok(None));

        assert_eq!(tree.len(), 1);

        // insert to existing leaf, should replace the key and value, and not change the
        // length
        assert_eq!(tree.try_insert(Box::new([1]), 1), Ok(Some(0)));

        assert_eq!(tree.len(), 1);

        // several more regular inserts, should add 3 to length
        assert_eq!(tree.try_insert(Box::new([0]), 2), Ok(None));
        assert_eq!(tree.try_insert(Box::new([2]), 3), Ok(None));
        assert_eq!(tree.try_insert(Box::new([3]), 4), Ok(None));

        assert_eq!(tree.len(), 4);

        // insert of key that is prefix, should not change length
        assert_eq!(
            tree.try_insert(Box::new([]), 5),
            Err(InsertPrefixError(Box::new([])))
        );

        assert_eq!(tree.len(), 4);

        // insert of key tat already exists, should not change length again
        assert_eq!(tree.try_insert(Box::new([1]), 6), Ok(Some(1)));

        assert_eq!(tree.len(), 4);

        // remove minimum, should reduce length by 1
        assert_eq!(tree.pop_first(), Some((Box::from([0]), 2)));

        assert_eq!(tree.len(), 3);

        // remove maximum, should reduce length by 1
        assert_eq!(tree.pop_last(), Some((Box::from([3]), 4)));

        assert_eq!(tree.len(), 2);

        // remove non-existent leaf, should not change length
        assert_eq!(tree.remove([]), None);

        assert_eq!(tree.len(), 2);

        // normal removes, should reduce length by 2
        assert_eq!(tree.remove([2]), Some(3));
        assert_eq!(tree.remove([1]), Some(6));

        assert_eq!(tree.len(), 0);
        assert!(tree.is_empty());

        // remove operations on an empty tree should not do anything
        assert_eq!(tree.pop_first(), None);
        assert_eq!(tree.pop_last(), None);
        assert_eq!(tree.remove([]), None);
    }
}