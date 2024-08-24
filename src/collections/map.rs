//! Module containing implementations of the `TreeMap` and associated
//! iterators/etc.

use crate::{
    deallocate_tree, find_maximum_to_delete, find_minimum_to_delete, maximum_unchecked,
    minimum_unchecked,
    rust_nightly_apis::hasher_write_length_prefix,
    search_for_delete_point, search_for_insert_point, search_unchecked,
    visitor::{MalformedTreeError, WellFormedChecker},
    AsBytes, DeletePoint, DeleteResult, InsertPoint, InsertPrefixError, InsertResult,
    InsertSearchResultType::Exact,
    LeafNode, NoPrefixesBytes, NodePtr, OpaqueNodePtr,
};
use std::{borrow::Borrow, fmt::Debug, hash::Hash, mem::ManuallyDrop, ops::Index};

mod entry;
mod entry_ref;
mod iterators;
pub use entry::*;
pub use entry_ref::*;
pub use iterators::*;

/// An ordered map based on an adaptive radix tree.
pub struct TreeMap<K, V, const PREFIX_LEN: usize = 16> {
    /// The number of entries present in the tree.
    num_entries: usize,
    /// A pointer to the tree root, if present.
    pub(crate) root: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
}

impl<K, V> TreeMap<K, V> {
    /// Create a new, empty [`crate::TreeMap`] with the default number of prefix
    /// bytes (16).
    ///
    /// This function will not pre-allocate anything.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map = TreeMap::<Box<[u8]>, ()>::new();
    /// assert_eq!(map, TreeMap::new());
    /// assert!(map.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::with_prefix_len()
    }
}

impl<K, V, const PREFIX_LEN: usize> TreeMap<K, V, PREFIX_LEN> {
    /// Create a new, empty [`crate::TreeMap`].
    ///
    /// This function will not pre-allocate anything.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map = TreeMap::<Box<[u8]>, (), 16>::with_prefix_len();
    /// assert_eq!(map, TreeMap::new());
    /// assert!(map.is_empty());
    /// ```
    pub fn with_prefix_len() -> Self {
        TreeMap {
            num_entries: 0,
            root: None,
        }
    }

    /// Clear the map, removing all elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// assert_eq!(map.len(), 1);
    ///
    /// map.clear();
    /// assert!(map.is_empty());
    /// assert!(map.get([1, 2, 3].as_ref()).is_none());
    /// ```
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

    /// Consume the tree, returning a raw pointer to the root node.
    ///
    /// If the results is `None`, this means the tree is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// assert_eq!(map.len(), 1);
    ///
    /// let root = TreeMap::into_raw(map);
    /// assert!(root.is_some());
    /// ```
    pub fn into_raw(tree: Self) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        // We need this `ManuallyDrop` so that the `TreeMap::drop` is not called.
        // Since the `root` field is `Copy`, it can be moved out of the tree without
        // inhibiting `Drop`
        let tree = ManuallyDrop::new(tree);
        tree.root
    }

    /// Constructs a [`TreeMap`] from a raw node pointer.
    ///
    /// # Safety
    ///
    /// The raw pointer must have been previously returned by a call to
    /// [`TreeMap::into_raw`].
    ///
    /// This function also requires that this the given `root` pointer is
    /// unique, and that there are no other pointers into the tree.
    ///
    /// # Errors
    ///
    /// This function runs a series of checks to ensure that the returned tree
    /// is well-formed. See [`WellFormedChecker`] for details on the
    /// requirements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// assert_eq!(map.len(), 1);
    ///
    /// let root = TreeMap::into_raw(map);
    /// assert!(root.is_some());
    ///
    /// // SAFETY: The root pointer came directly from the `into_raw` result.
    /// let _map = unsafe { TreeMap::from_raw(root) }.unwrap();
    /// ```
    pub unsafe fn from_raw(
        root: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
    ) -> Result<Self, MalformedTreeError<K, V, PREFIX_LEN>>
    where
        K: AsBytes,
    {
        match root {
            Some(root) => {
                // SAFETY: The safety doc of this function guarantees the uniqueness of the
                // `root` pointer, which means we won't have any other mutations
                let stats = unsafe { WellFormedChecker::check_tree(root)? };

                Ok(Self {
                    root: Some(root),
                    num_entries: stats.num_leaf,
                })
            },
            None => Ok(Self::with_prefix_len()),
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// assert_eq!(*map.get([1, 2, 3].as_ref()).unwrap(), 'a');
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        Some(self.get_key_value(key)?.1)
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// assert_eq!(map.get_key_value([1, 2, 3].as_ref()).unwrap(), (&Box::from([1, 2, 3]), &'a'));
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        if let Some(root) = self.root {
            // SAFETY: Since we have an immutable reference to the `TreeMap` object, that
            // means there can only exist other immutable references aside from this one,
            // and no mutable references. That means that no mutating operations can occur
            // on the root node or any child of the root node.
            let search_result = unsafe { search_unchecked(root, key.as_bytes())? };

            // SAFETY: The lifetime chosen the value reference is bounded by the lifetime of
            // the immutable reference to the `TreeMap`. The memory of the value will not be
            // mutated since it is only owned by the `TreeMap` and there can only be other
            // immutable references at this time (no mutable references to the `TreeMap`).
            let (key, value) = unsafe { search_result.as_key_value_ref() };
            Some((key, value))
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// assert_eq!(map[[1, 2, 3].as_ref()], 'a');
    ///
    /// *map.get_mut([1, 2, 3].as_ref()).unwrap() = 'b';
    /// assert_eq!(map[[1, 2, 3].as_ref()], 'b');
    /// ```
    ///
    /// While an element from the tree is mutably referenced, no other operation
    /// on the tree can happen.
    ///
    /// ```rust,compile_fail
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    ///
    ///
    /// let value = map.get_mut(&[1, 2, 3]).unwrap();
    /// assert_eq!(*value, 'a');
    ///
    /// assert_eq!(*map[[1, 2, 3].as_ref()], 'a');
    ///
    /// *value = 'b';
    /// drop(value);
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        if let Some(root) = self.root {
            // SAFETY: Since we have a mutable reference to the `TreeMap` object, that
            // means there cannot exist any other reference (mutable or immutable) to the
            // same `TreeMap`. Which means that no other mutating operations could be
            // happening during the `search_unchecked` call.
            let search_result = unsafe { search_unchecked(root, key.as_bytes())? };

            // SAFETY: The lifetime chosen the value reference is bounded by the lifetime of
            // the mutable reference to the `TreeMap`. The value pointed to by the returned
            // mutable reference will not be accessed (read or written) through any other
            // pointer because of the existing mutable reference on the `TreeMap`.
            let leaf_node_ref = unsafe { search_result.as_mut() };

            Some(leaf_node_ref.value_mut())
        } else {
            None
        }
    }

    /// Makes a fuzzy search in the tree by `key`,
    /// returning all keys and values that are
    /// less than or equal to `max_edit_dist`.
    ///
    /// This is done by using Levenshtein distance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map: TreeMap<_, _> = TreeMap::new();
    ///
    /// map.insert(c"abc", 0);
    /// map.insert(c"abd", 1);
    /// map.insert(c"abdefg", 2);
    ///
    /// let fuzzy: Vec<_> = map.fuzzy(c"ab", 2).collect();
    /// assert_eq!(fuzzy, vec![(&c"abd", &1), (&c"abc", &0)]);
    /// ```
    pub fn fuzzy<'a, 'b, Q>(
        &'a self,
        key: &'b Q,
        max_edit_dist: usize,
    ) -> Fuzzy<'a, 'b, K, V, PREFIX_LEN>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        Fuzzy::new(self, key.as_bytes(), max_edit_dist)
    }

    /// Makes a fuzzy search in the tree by `key`,
    /// returning all keys and values that are
    /// less than or equal to `max_edit_dist`.
    ///
    /// This is done by using Levenshtein distance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map: TreeMap<_, _> = TreeMap::new();
    ///
    /// map.insert(c"abc", 0);
    /// map.insert(c"abd", 1);
    /// map.insert(c"abdefg", 2);
    ///
    /// let fuzzy: Vec<_> = map.fuzzy_mut(c"ab", 2).collect();
    /// assert_eq!(fuzzy, vec![(&c"abd", &mut 1), (&c"abc", &mut 0)]);
    /// ```
    pub fn fuzzy_mut<'a, 'b, Q>(
        &'a mut self,
        key: &'b Q,
        max_edit_dist: usize,
    ) -> FuzzyMut<'a, 'b, K, V, PREFIX_LEN>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        FuzzyMut::new(self, key.as_bytes(), max_edit_dist)
    }

    /// Makes a fuzzy search in the tree by `key`,
    /// returning all keys and values that are
    /// less than or equal to `max_edit_dist`
    ///
    /// This is done by using Levenshtein distance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map: TreeMap<_, _> = TreeMap::new();
    ///
    /// map.insert(c"abc", 0);
    /// map.insert(c"abd", 1);
    /// map.insert(c"abdefg", 2);
    ///
    /// let fuzzy: Vec<_> = map.fuzzy_keys(c"ab", 2).collect();
    /// assert_eq!(fuzzy, vec![&c"abd", &c"abc"]);
    /// ```
    pub fn fuzzy_keys<'a, 'b, Q>(
        &'a self,
        key: &'b Q,
        max_edit_dist: usize,
    ) -> FuzzyKeys<'a, 'b, K, V, PREFIX_LEN>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        FuzzyKeys::new(self, key.as_bytes(), max_edit_dist)
    }

    /// Makes a fuzzy search in the tree by `key`,
    /// returning all keys and values that are
    /// less than or equal to `max_edit_dist`.
    ///
    /// This is done by using Levenshtein distance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map: TreeMap<_, _> = TreeMap::new();
    ///
    /// map.insert(c"abc", 0);
    /// map.insert(c"abd", 1);
    /// map.insert(c"abdefg", 2);
    ///
    /// let fuzzy: Vec<_> = map.fuzzy_values(c"ab", 2).collect();
    /// assert_eq!(fuzzy, vec![&1, &0]);
    /// ```
    pub fn fuzzy_values<'a, 'b, Q>(
        &'a self,
        key: &'b Q,
        max_edit_dist: usize,
    ) -> FuzzyValues<'a, 'b, K, V, PREFIX_LEN>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        FuzzyValues::new(self, key.as_bytes(), max_edit_dist)
    }

    /// Makes a fuzzy search in the tree by `key`,
    /// returning all keys and values that are
    /// less than or equal to `max_edit_dist`
    ///
    /// This is done by using Levenshtein distance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map: TreeMap<_, _> = TreeMap::new();
    ///
    /// map.insert(c"abc", 0);
    /// map.insert(c"abd", 1);
    /// map.insert(c"abdefg", 2);
    ///
    /// let fuzzy: Vec<_> = map.fuzzy_values(c"ab", 2).collect();
    /// assert_eq!(fuzzy, vec![&mut 1, &mut 0]);
    /// ```
    pub fn fuzzy_values_mut<'a, 'b, Q>(
        &'a mut self,
        key: &'b Q,
        max_edit_dist: usize,
    ) -> FuzzyValuesMut<'a, 'b, K, V, PREFIX_LEN>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        FuzzyValuesMut::new(self, key.as_bytes(), max_edit_dist)
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    ///
    /// assert!(map.contains_key([1, 2, 3].as_ref()));
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        // TODO(#18): Optimize this with a specific underlying method which just check
        // for existing leaf, does not return it
        self.get(key).is_some()
    }

    /// Returns the first key-value pair in the map. The key in this pair is the
    /// minimum key in the map.
    ///
    /// If the tree is empty, returns None.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    ///
    /// assert_eq!(map.first_key_value().unwrap(), (&[1, 2, 3].into(), &'a'));
    /// ```
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
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

            Some(leaf_node_ref.entry_ref())
        } else {
            None
        }
    }

    /// Removes and returns the first element in the map. The key of this
    /// element is the minimum key that was in the map.
    ///
    /// If the tree is empty, returns None.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    ///
    /// assert_eq!(map.pop_first().unwrap(), (Box::from([1, 2, 3]), 'a'));
    /// ```
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        if let Some(root) = self.root {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let delete_point = unsafe { find_minimum_to_delete(root) };
            let delete_result = self.apply_delete_point(delete_point);
            Some(delete_result.deleted_leaf.into_entry())
        } else {
            None
        }
    }

    /// Returns the last key-value pair in the map. The key in this pair is the
    /// maximum key in the map.
    ///
    /// If the tree is empty, returns None.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// map.try_insert(Box::new([2, 3, 4]), 'b').unwrap();
    ///
    /// assert_eq!(map.last_key_value().unwrap(), (&Box::from([2, 3, 4]), &'b'));
    /// ```
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
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

            Some(leaf_node_ref.entry_ref())
        } else {
            None
        }
    }

    /// Removes and returns the last element in the map. The key of this element
    /// is the maximum key that was in the map.
    ///
    /// If the tree is empty, returns None.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// map.try_insert(Box::new([2, 3, 4]), 'b').unwrap();
    ///
    /// assert_eq!(map.pop_last().unwrap(), (Box::from([2, 3, 4]), 'b'));
    /// ```
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        if let Some(root) = self.root {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let delete_point = unsafe { find_maximum_to_delete(root) };
            let delete_result = self.apply_delete_point(delete_point);
            Some(delete_result.deleted_leaf.into_entry())
        } else {
            None
        }
    }

    fn init_tree(&mut self, key: K, value: V) -> NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>> {
        // Since this is a singleton tree, the single leaf node has no siblings
        let leaf = NodePtr::allocate_node_ptr(LeafNode::with_no_siblings(key, value));
        self.root = Some(leaf.to_opaque());
        self.num_entries = 1;
        leaf
    }

    fn apply_insert_point(
        &mut self,
        insert_point: InsertPoint<K, V, PREFIX_LEN>,
        key: K,
        value: V,
    ) -> InsertResult<K, V, PREFIX_LEN>
    where
        K: AsBytes,
    {
        // SAFETY: This call is safe because we have a mutable reference on the tree, so
        // no other operation can be concurrent with this one.
        let insert_result = unsafe { insert_point.apply(key, value) };

        self.root = Some(insert_result.new_root);

        if insert_result.existing_leaf.is_none() {
            // this was a strict add, not a replace. If there was an existing leaf we are
            // removing and adding a leaf, so the number of entries stays the same
            self.num_entries += 1;
        }

        insert_result
    }

    fn apply_delete_point(
        &mut self,
        delete_point: DeletePoint<K, V, PREFIX_LEN>,
    ) -> DeleteResult<K, V, PREFIX_LEN> {
        // SAFETY: The root is sure to not be `None`, since the we somehow got a
        // `DeletePoint`. So the caller must have checked this. Also, since we have a
        // mutable reference to the tree, no other read or write operation can be
        // happening concurrently.
        let delete_result = unsafe { delete_point.apply(self.root.unwrap_unchecked()) };

        self.root = delete_result.new_root;

        self.num_entries -= 1;

        delete_result
    }

    /// Insert a key-value pair into the map.
    ///
    /// If the map did not have this key present, Ok(None) is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned.
    ///
    /// Unlike [`try_insert`][crate::TreeMap::try_insert], this function will
    /// not return an error, because the contract of the [`NoPrefixesBytes`]
    /// ensures that the given key type will never be a prefix of an existing
    /// value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<u128, char>::new();
    ///
    /// assert!(map.insert(123, 'a').is_none());
    /// assert!(map.insert(234, 'b').is_none());
    /// assert_eq!(map.insert(234, 'c'), Some('b'));
    ///
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: NoPrefixesBytes,
    {
        // This will never fail because of the safety contract of `NoPrefixesBytes`
        unsafe { self.try_insert(key, value).unwrap_unchecked() }
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// assert!(map.try_insert(Box::new([1, 2, 3]), 'a').unwrap().is_none());
    /// assert!(map.try_insert(Box::new([2, 3, 4]), 'b').unwrap().is_none());
    /// // This function call errors because the key is a prefix of the existing key
    /// assert!(map.try_insert(Box::new([2, 3, 4, 5]), 'c').is_err());
    /// assert_eq!(map.try_insert(Box::new([2, 3, 4]), 'd').unwrap(), Some('b'));
    ///
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn try_insert(&mut self, key: K, value: V) -> Result<Option<V>, InsertPrefixError>
    where
        K: AsBytes,
    {
        if let Some(root) = self.root {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let insert_result = unsafe {
                let insert_point = search_for_insert_point(root, key.as_bytes())?;
                self.apply_insert_point(insert_point, key, value)
            };
            Ok(insert_result.existing_leaf.map(|leaf| leaf.into_entry().1))
        } else {
            self.init_tree(key, value);
            Ok(None)
        }
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// map.try_insert(Box::new([2, 3, 4]), 'b').unwrap();
    ///
    /// assert_eq!(map.remove_entry([2, 3, 4].as_ref()).unwrap(), (Box::from([2, 3, 4]), 'b'))
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        if let Some(root) = self.root {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let delete_point = unsafe { search_for_delete_point(root, key.as_bytes())? };
            let delete_result = self.apply_delete_point(delete_point);
            Some(delete_result.deleted_leaf.into_entry())
        } else {
            None
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// map.try_insert(Box::new([2, 3, 4]), 'b').unwrap();
    ///
    /// assert_eq!(map.remove([2, 3, 4].as_ref()).unwrap(), 'b');
    /// assert_eq!(map.remove([2, 3, 4].as_ref()), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        self.remove_entry(key).map(|(_, v)| v)
    }

    /*
    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs (k, v) for which f(&k, &mut v) returns
    /// false. The elements are visited in ascending key order.
    pub(crate) fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.drain_filter(f).for_each(|_| ());
    }

    /// Moves all elements from other into self, leaving other empty.
    //
    // # Examples
    //
    // ```rust,should_panic
    // use blart::TreeMap;
    //
    // let mut a = TreeMap::<u128, _>::new();
    // a.try_insert(1, "a").unwrap();
    // a.try_insert(2, "b").unwrap();
    // a.try_insert(3, "c").unwrap(); // Note: Key (3) also present in b.
    //
    // let mut b = TreeMap::<u128, _>::new();
    // b.try_insert(3, "d").unwrap(); // Note: Key (3) also present in a.
    // b.try_insert(4, "e").unwrap();
    // b.try_insert(5, "f").unwrap();
    //
    // a.append(&mut b);
    //
    // assert_eq!(a.len(), 5);
    // assert_eq!(b.len(), 0);
    //
    // assert_eq!(a[&1], "a");
    // assert_eq!(a[&2], "b");
    // assert_eq!(a[&3], "d"); // Note: "c" has been overwritten.
    // assert_eq!(a[&4], "e");
    // assert_eq!(a[&5], "f");
    // ```
    #[allow(dead_code)]
    pub(crate) fn append(&mut self, other: &mut TreeMap<K, V, PREFIX_LEN>)
    where
        K: NoPrefixesBytes,
    {
        self.extend(other.drain_filter(|_, _| true))
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the
    /// map.
    ///
    /// The simplest way is to use the range syntax `min..max`, thus
    /// `range(min..max)` will yield elements from min (inclusive) to max
    /// (exclusive). The range may also be entered as `(Bound<T>, Bound<T>)`, so
    /// for example `range((Excluded(4), Included(10)))` will yield a
    /// left-exclusive, right-inclusive range from 4 to 10.
    //
    // # Examples
    //
    // ```rust,should_panic
    // use blart::TreeMap;
    // use std::ops::Bound::Included;
    //
    // let mut map = TreeMap::<u8, _>::new();
    // map.try_insert(3, "a").unwrap();
    // map.try_insert(5, "b").unwrap();
    // map.try_insert(8, "c").unwrap();
    //
    // for (key, &value) in map.range((Included(&4), Included(&8))) {
    //     println!("{key:?}: {value}");
    // }
    // assert_eq!(map.range(&4..).next(), Some((&5, &"b")));
    // ```
    #[allow(dead_code)]
    pub(crate) fn range<Q, R>(&self, _range: R) -> iterators::Range<K, V>
    where
        Q: AsBytes + ?Sized,
        K: Borrow<Q> + AsBytes,
        R: RangeBounds<Q>,
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
    //
    // # Examples
    //
    // ```rust,should_panic
    // use blart::TreeMap;
    //
    // let mut map: TreeMap<_, i32> = TreeMap::new();
    //
    // for (key, value) in [("Alice", 0), ("Bob", 0), ("Carol", 0), ("Cheryl", 0)] {
    //     let _ = map.try_insert(key, value).unwrap();
    // }
    //
    // for (name, balance) in map.range_mut("B".."Cheryl") {
    //     *balance += 100;
    //
    //     if name.starts_with('C') {
    //         *balance *= 2;
    //     }
    // }
    //
    // for (name, balance) in &map {
    //     println!("{name} => {balance}");
    // }
    //
    // assert_eq!(map["Alice"], 0);
    // assert_eq!(map["Bob"], 100);
    // assert_eq!(map["Carol"], 200);
    // assert_eq!(map["Cheryl"], 200);
    // ```
    #[allow(dead_code)]
    pub(crate) fn range_mut<Q, R>(&mut self, _range: R) -> iterators::RangeMut<K, V>
    where
        Q: AsBytes + ?Sized,
        K: Borrow<Q> + AsBytes,
        R: RangeBounds<Q>,
    {
        todo!()
    }

    /// Splits the collection into two at the given key. Returns everything
    /// after the given key, including the key.
    //
    // # Examples
    //
    // ```rust,should_panic
    // use blart::TreeMap;
    //
    // let mut a = TreeMap::new();
    // a.try_insert(Box::from([1]), "a").unwrap();
    // a.try_insert(Box::from([2]), "b").unwrap();
    // a.try_insert(Box::from([3]), "c").unwrap();
    // a.try_insert(Box::from([17]), "d").unwrap();
    // a.try_insert(Box::from([41]), "e").unwrap();
    //
    // let b = a.split_off([3].as_ref());
    //
    // assert_eq!(a.len(), 2);
    // assert_eq!(b.len(), 3);
    //
    // assert_eq!(a[[1].as_ref()], "a");
    // assert_eq!(a[[2].as_ref()], "b");
    //
    // assert_eq!(b[[3].as_ref()], "c");
    // assert_eq!(b[[17].as_ref()], "d");
    // assert_eq!(b[[41].as_ref()], "e");
    // ```
    #[allow(dead_code)]
    pub(crate) fn split_off<Q>(&mut self, split_key: &Q) -> TreeMap<K, V, PREFIX_LEN>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        let mut new_tree = TreeMap::new();

        for (key, value) in
            self.drain_filter(|key, _| split_key.as_bytes() <= key.borrow().as_bytes())
        {
            // PANIC SAFETY: This will not panic because the property of any existing tree
            // containing no keys that are prefixes of any other key holds when the tree is
            // split into any portion.
            let _ = new_tree.try_insert(key, value).unwrap();
        }

        new_tree
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
    /// dropping an element, or if the [`DrainFilter`] value is leaked.
    //
    // # Examples
    //
    // ```rust,should_panic
    // use blart::TreeMap;
    //
    // let mut map: TreeMap<u8, u8> = (0..8).map(|x| (x, x)).collect();
    // let evens: TreeMap<_, _> = map.drain_filter(|k, _v| k % 2 == 0).collect();
    // let odds = map;
    // assert_eq!(evens.keys().copied().collect::<Vec<_>>(), [0, 2, 4, 6]);
    // assert_eq!(odds.keys().copied().collect::<Vec<_>>(), [1, 3, 5, 7]);
    // ```
    #[allow(dead_code)]
    pub fn extract_if<'a, F>(&'a mut self, pred: F) -> ExtractIf<'a, K, V, F>
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        ExtractIf::new(self, pred)
    }
    */

    /// Creates a consuming iterator visiting all the keys, in sorted order. The
    /// map cannot be used after calling this. The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map: TreeMap<_, char> = ['d', 'c', 'b', 'a', 'z'].into_iter()
    ///     .enumerate()
    ///     .collect();
    ///
    /// let mut iter = map.into_keys();
    ///
    /// assert_eq!(iter.next().unwrap(), 0);
    /// assert_eq!(iter.next().unwrap(), 1);
    /// assert_eq!(iter.next().unwrap(), 2);
    /// assert_eq!(iter.next().unwrap(), 3);
    /// assert_eq!(iter.next().unwrap(), 4);
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn into_keys(self) -> iterators::IntoKeys<K, V, PREFIX_LEN> {
        iterators::IntoKeys::new(self)
    }

    /// Creates a consuming iterator visiting all the values, in order by key.
    /// The map cannot be used after calling this. The iterator element type is
    /// `V`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map: TreeMap<_, char> = ['d', 'c', 'b', 'a', 'z'].into_iter()
    ///     .enumerate()
    ///     .collect();
    ///
    /// let mut iter = map.into_values();
    ///
    /// assert_eq!(iter.next().unwrap(), 'd');
    /// assert_eq!(iter.next().unwrap(), 'c');
    /// assert_eq!(iter.next().unwrap(), 'b');
    /// assert_eq!(iter.next().unwrap(), 'a');
    /// assert_eq!(iter.next().unwrap(), 'z');
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn into_values(self) -> iterators::IntoValues<K, V, PREFIX_LEN> {
        iterators::IntoValues::new(self)
    }

    /// Gets an iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map: TreeMap<_, char> = ['d', 'c', 'b', 'a', 'z'].into_iter()
    ///     .enumerate()
    ///     .collect();
    ///
    /// let mut iter = map.iter();
    ///
    /// assert_eq!(iter.next().unwrap(), (&0, &'d'));
    /// assert_eq!(iter.next().unwrap(), (&1, &'c'));
    /// assert_eq!(iter.next().unwrap(), (&2, &'b'));
    /// assert_eq!(iter.next().unwrap(), (&3, &'a'));
    /// assert_eq!(iter.next().unwrap(), (&4, &'z'));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> TreeIterator<'_, K, V, PREFIX_LEN> {
        TreeIterator::new(self)
    }

    /// Gets a mutable iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map: TreeMap<_, char> = ['d', 'c', 'b', 'a', 'z'].into_iter()
    ///     .enumerate()
    ///     .collect();
    ///
    /// for (_key, value) in map.iter_mut() {
    ///     value.make_ascii_uppercase();
    /// }
    ///
    /// assert_eq!(map[&0], 'D');
    /// assert_eq!(map[&1], 'C');
    /// assert_eq!(map[&2], 'B');
    /// assert_eq!(map[&3], 'A');
    /// assert_eq!(map[&4], 'Z');
    /// ```
    pub fn iter_mut(&mut self) -> TreeIteratorMut<'_, K, V, PREFIX_LEN> {
        TreeIteratorMut::new(self)
    }

    /// Gets an iterator over the keys of the map, in sorted order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map: TreeMap<_, char> = ['d', 'c', 'b', 'a', 'z'].into_iter()
    ///     .enumerate()
    ///     .collect();
    ///
    /// let mut iter = map.keys();
    ///
    /// assert_eq!(iter.next().unwrap(), &0);
    /// assert_eq!(iter.next().unwrap(), &1);
    /// assert_eq!(iter.next().unwrap(), &2);
    /// assert_eq!(iter.next().unwrap(), &3);
    /// assert_eq!(iter.next().unwrap(), &4);
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V, PREFIX_LEN> {
        Keys::new(self)
    }

    /// Gets an iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map: TreeMap<_, char> = ['d', 'c', 'b', 'a', 'z'].into_iter()
    ///     .enumerate()
    ///     .collect();
    ///
    /// let mut iter = map.values();
    ///
    /// assert_eq!(iter.next().unwrap(), &'d');
    /// assert_eq!(iter.next().unwrap(), &'c');
    /// assert_eq!(iter.next().unwrap(), &'b');
    /// assert_eq!(iter.next().unwrap(), &'a');
    /// assert_eq!(iter.next().unwrap(), &'z');
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn values(&self) -> Values<'_, K, V, PREFIX_LEN> {
        Values::new(self)
    }

    /// Gets a mutable iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map: TreeMap<_, char> = ['d', 'c', 'b', 'a', 'z'].into_iter()
    ///     .enumerate()
    ///     .collect();
    ///
    /// for value in map.values_mut() {
    ///     value.make_ascii_uppercase();
    /// }
    ///
    /// assert_eq!(map[&0], 'D');
    /// assert_eq!(map[&1], 'C');
    /// assert_eq!(map[&2], 'B');
    /// assert_eq!(map[&3], 'A');
    /// assert_eq!(map[&4], 'Z');
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, PREFIX_LEN> {
        ValuesMut::new(self)
    }

    /// Gets an iterator over the entries of the map that start with `prefix`
    ///
    /// # Example
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(c"abcde", 0);
    /// map.insert(c"abcdexxx", 0);
    /// map.insert(c"abcdexxy", 0);
    /// map.insert(c"abcdx", 0);
    /// map.insert(c"abcx", 0);
    /// map.insert(c"bx", 0);
    ///
    /// let p: Vec<_> = map.prefix(c"abcde".to_bytes()).collect();
    ///
    /// assert_eq!(p, vec![(&c"abcde", &0), (&c"abcdexxx", &0), (&c"abcdexxy", &0)]);
    /// ```
    pub fn prefix<'a, 'b>(&'a self, prefix: &'b [u8]) -> Prefix<'a, 'b, K, V, PREFIX_LEN>
    where
        K: AsBytes,
    {
        Prefix::new(self, prefix)
    }

    /// Gets a mutable iterator over the entries of the map that start with
    /// `prefix`
    ///
    /// # Example
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(c"abcde", 0);
    /// map.insert(c"abcdexxx", 0);
    /// map.insert(c"abcdexxy", 0);
    /// map.insert(c"abcdx", 0);
    /// map.insert(c"abcx", 0);
    /// map.insert(c"bx", 0);
    ///
    /// let p: Vec<_> = map.prefix_mut(c"abcde".to_bytes()).collect();
    ///
    /// assert_eq!(p, vec![(&c"abcde", &mut 0), (&c"abcdexxx", &mut 0), (&c"abcdexxy", &mut 0)]);
    /// ```
    pub fn prefix_mut<'a, 'b>(&'a mut self, prefix: &'b [u8]) -> PrefixMut<'a, 'b, K, V, PREFIX_LEN>
    where
        K: AsBytes,
    {
        PrefixMut::new(self, prefix)
    }

    /// Gets an iterator over the keys of the map that start with `prefix`
    ///
    /// # Example
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(c"abcde", 0);
    /// map.insert(c"abcdexxx", 0);
    /// map.insert(c"abcdexxy", 0);
    /// map.insert(c"abcdx", 0);
    /// map.insert(c"abcx", 0);
    /// map.insert(c"bx", 0);
    ///
    /// let p: Vec<_> = map.prefix_keys(c"abcde".to_bytes()).collect();
    ///
    /// assert_eq!(p, vec![&c"abcde", &c"abcdexxx", &c"abcdexxy"]);
    /// ```
    pub fn prefix_keys<'a, 'b>(&'a self, prefix: &'b [u8]) -> PrefixKeys<'a, 'b, K, V, PREFIX_LEN>
    where
        K: AsBytes,
    {
        PrefixKeys::new(self, prefix)
    }

    /// Gets an iterator over the values of the map that start with `prefix`
    ///
    /// # Example
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(c"abcde", 0);
    /// map.insert(c"abcdexxx", 1);
    /// map.insert(c"abcdexxy", 2);
    /// map.insert(c"abcdx", 3);
    /// map.insert(c"abcx", 4);
    /// map.insert(c"bx", 5);
    ///
    /// let p: Vec<_> = map.prefix_values(c"abcde".to_bytes()).collect();
    ///
    /// assert_eq!(p, vec![&0, &1, &2]);
    /// ```
    pub fn prefix_values<'a, 'b>(
        &'a self,
        prefix: &'b [u8],
    ) -> PrefixValues<'a, 'b, K, V, PREFIX_LEN>
    where
        K: AsBytes,
    {
        PrefixValues::new(self, prefix)
    }

    /// Gets a mutable iterator over the values of the map that start with
    /// `prefix`
    ///
    /// # Example
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(c"abcde", 0);
    /// map.insert(c"abcdexxx", 1);
    /// map.insert(c"abcdexxy", 2);
    /// map.insert(c"abcdx", 3);
    /// map.insert(c"abcx", 4);
    /// map.insert(c"bx", 5);
    ///
    /// let p: Vec<_> = map.prefix_values(c"abcde".to_bytes()).collect();
    ///
    /// assert_eq!(p, vec![&mut 0, &mut 1, &mut 2]);
    /// ```
    pub fn prefix_values_mut<'a, 'b>(
        &'a mut self,
        prefix: &'b [u8],
    ) -> PrefixValuesMut<'a, 'b, K, V, PREFIX_LEN>
    where
        K: AsBytes,
    {
        PrefixValuesMut::new(self, prefix)
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map: TreeMap<_, char> = ['d', 'c', 'b', 'a', 'z'].into_iter()
    ///     .enumerate()
    ///     .collect();
    ///
    /// assert_eq!(map.len(), 5);
    /// ```
    pub fn len(&self) -> usize {
        self.num_entries
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map = TreeMap::<Box<[u8]>, ()>::new();
    /// assert!(map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.num_entries == 0
    }
}

impl<K, V, const PREFIX_LEN: usize> TreeMap<K, V, PREFIX_LEN> {
    /// Tries to get the given key’s corresponding entry in the map for in-place
    /// manipulation.
    pub fn try_entry(&mut self, key: K) -> Result<Entry<K, V, PREFIX_LEN>, InsertPrefixError>
    where
        K: AsBytes,
    {
        let entry = match self.root {
            Some(root) => {
                // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
                // that there are no other references (mutable or immutable) to this same
                // object. Meaning that our access to the root node is unique and there are no
                // other accesses to any node in the tree.
                let insert_point = unsafe { search_for_insert_point(root, key.as_bytes())? };
                match insert_point.insert_type {
                    Exact { leaf_node_ptr } => Entry::Occupied(OccupiedEntry {
                        map: self,
                        leaf_node_ptr,
                        grandparent_ptr_and_parent_key_byte: insert_point
                            .grandparent_ptr_and_parent_key_byte,
                        parent_ptr_and_child_key_byte: insert_point.parent_ptr_and_child_key_byte,
                    }),
                    _ => Entry::Vacant(VacantEntry {
                        key,
                        insert_point: Some(insert_point),
                        map: self,
                    }),
                }
            },
            None => Entry::Vacant(VacantEntry {
                key,
                insert_point: None,
                map: self,
            }),
        };
        Ok(entry)
    }

    /// Tries to get the given key’s corresponding entry in the map for in-place
    /// manipulation.
    pub fn try_entry_ref<'a, 'b, Q>(
        &'a mut self,
        key: &'b Q,
    ) -> Result<EntryRef<'a, 'b, K, V, Q, PREFIX_LEN>, InsertPrefixError>
    where
        K: AsBytes + Borrow<Q> + From<&'b Q>,
        Q: AsBytes + ?Sized,
    {
        let entry = match self.root {
            Some(root) => {
                // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
                // that there are no other references (mutable or immutable) to this same
                // object. Meaning that our access to the root node is unique and there are no
                // other accesses to any node in the tree.
                let insert_point = unsafe { search_for_insert_point(root, key.as_bytes())? };
                match insert_point.insert_type {
                    Exact { leaf_node_ptr } => EntryRef::Occupied(OccupiedEntryRef {
                        map: self,
                        leaf_node_ptr,
                        grandparent_ptr_and_parent_key_byte: insert_point
                            .grandparent_ptr_and_parent_key_byte,
                        parent_ptr_and_child_key_byte: insert_point.parent_ptr_and_child_key_byte,
                    }),
                    _ => EntryRef::Vacant(VacantEntryRef {
                        key,
                        insert_point: Some(insert_point),
                        map: self,
                    }),
                }
            },
            None => EntryRef::Vacant(VacantEntryRef {
                key,
                insert_point: None,
                map: self,
            }),
        };
        Ok(entry)
    }

    /// Gets the given key’s corresponding entry in the map for in-place
    /// manipulation.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, PREFIX_LEN>
    where
        K: NoPrefixesBytes,
    {
        // This will never fail because of the safety contract of `NoPrefixesBytes`
        unsafe { self.try_entry(key).unwrap_unchecked() }
    }

    /// Gets the given key’s corresponding entry in the map for in-place
    /// manipulation.
    pub fn entry_ref<'a, 'b, Q>(&'a mut self, key: &'b Q) -> EntryRef<'a, 'b, K, V, Q, PREFIX_LEN>
    where
        K: NoPrefixesBytes + Borrow<Q> + From<&'b Q>,
        Q: NoPrefixesBytes + ?Sized,
    {
        // This will never fail because of the safety contract of `NoPrefixesBytes`
        unsafe { self.try_entry_ref(key).unwrap_unchecked() }
    }
}

impl<K, V, const PREFIX_LEN: usize> Drop for TreeMap<K, V, PREFIX_LEN> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<K, V, const PREFIX_LEN: usize> Clone for TreeMap<K, V, PREFIX_LEN>
where
    K: Clone + AsBytes,
    V: Clone,
{
    fn clone(&self) -> Self {
        if let Some(root) = self.root {
            Self {
                root: Some(root.deep_clone()),
                num_entries: self.num_entries,
            }
        } else {
            Self::with_prefix_len()
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> Debug for TreeMap<K, V, PREFIX_LEN>
where
    K: Debug + AsBytes,
    V: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> Default for TreeMap<K, V, PREFIX_LEN> {
    fn default() -> Self {
        Self::with_prefix_len()
    }
}

impl<'a, K, V, const PREFIX_LEN: usize> Extend<(&'a K, &'a V)> for TreeMap<K, V, PREFIX_LEN>
where
    K: Copy + NoPrefixesBytes,
    V: Copy,
{
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            let _ = self.insert(*key, *value);
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> Extend<(K, V)> for TreeMap<K, V, PREFIX_LEN>
where
    K: NoPrefixesBytes,
{
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            let _ = self.insert(key, value);
        }
    }
}

impl<K, V, const PREFIX_LEN: usize, const N: usize> From<[(K, V); N]> for TreeMap<K, V, PREFIX_LEN>
where
    K: NoPrefixesBytes,
{
    fn from(arr: [(K, V); N]) -> Self {
        let mut map = TreeMap::with_prefix_len();
        for (key, value) in arr {
            let _ = map.insert(key, value);
        }
        map
    }
}

impl<K, V, const PREFIX_LEN: usize> FromIterator<(K, V)> for TreeMap<K, V, PREFIX_LEN>
where
    K: NoPrefixesBytes,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = TreeMap::with_prefix_len();
        for (key, value) in iter {
            let _ = map.insert(key, value);
        }
        map
    }
}

impl<K, V, const PREFIX_LEN: usize> Hash for TreeMap<K, V, PREFIX_LEN>
where
    K: Hash + AsBytes,
    V: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        hasher_write_length_prefix(state, self.num_entries);
        for elt in self {
            elt.hash(state);
        }
    }
}

impl<Q, K, V, const PREFIX_LEN: usize> Index<&Q> for TreeMap<K, V, PREFIX_LEN>
where
    K: Borrow<Q> + AsBytes,
    Q: AsBytes + ?Sized,
{
    type Output = V;

    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<'a, K: AsBytes, V, const PREFIX_LEN: usize> IntoIterator for &'a TreeMap<K, V, PREFIX_LEN> {
    type IntoIter = TreeIterator<'a, K, V, PREFIX_LEN>;
    type Item = (&'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K: AsBytes, V, const PREFIX_LEN: usize> IntoIterator
    for &'a mut TreeMap<K, V, PREFIX_LEN>
{
    type IntoIter = TreeIteratorMut<'a, K, V, PREFIX_LEN>;
    type Item = (&'a K, &'a mut V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> IntoIterator for TreeMap<K, V, PREFIX_LEN> {
    type IntoIter = iterators::IntoIter<K, V, PREFIX_LEN>;
    type Item = (K, V);

    fn into_iter(self) -> Self::IntoIter {
        iterators::IntoIter::new(self)
    }
}

impl<K, V, const PREFIX_LEN: usize> Ord for TreeMap<K, V, PREFIX_LEN>
where
    K: Ord + AsBytes,
    V: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<K, V, const PREFIX_LEN: usize> PartialOrd for TreeMap<K, V, PREFIX_LEN>
where
    K: PartialOrd + AsBytes,
    V: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K, V, const PREFIX_LEN: usize> Eq for TreeMap<K, V, PREFIX_LEN>
where
    K: Eq + AsBytes,
    V: Eq,
{
}

impl<K, V, const PREFIX_LEN: usize> PartialEq for TreeMap<K, V, PREFIX_LEN>
where
    K: PartialEq + AsBytes,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter()) && self.num_entries == other.num_entries
    }
}

// SAFETY: This is safe to implement if `K` and `V` are also `Send`.
// This container is safe to `Send` for the same reasons why other container
// are also safe
unsafe impl<K, V, const PREFIX_LEN: usize> Send for TreeMap<K, V, PREFIX_LEN>
where
    K: Send + AsBytes,
    V: Send,
{
}

// SAFETY: This is safe to implement if `K` and `V` are also `Sync`.
// This container is safe to `Sync` for the same reasons why other container
// are also safe
unsafe impl<K, V, const PREFIX_LEN: usize> Sync for TreeMap<K, V, PREFIX_LEN>
where
    K: Sync + AsBytes,
    V: Sync,
{
}

#[cfg(test)]
mod tests {
    use std::{cmp::Ordering, collections::hash_map::RandomState, hash::BuildHasher};

    use crate::{
        tests_common::{
            generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed,
            PrefixExpansion,
        },
        TreeMap,
    };

    use super::*;

    #[test]
    fn tree_map_create_empty() {
        let map = TreeMap::<Box<[u8]>, ()>::new();

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn tree_map_get_non_existent_entry_different_keys_types() {
        let map = TreeMap::<Box<[u8]>, ()>::new();

        assert_eq!(map.get(&Box::from(*b"123456789")), None);
        let k = b"123456789".to_vec();
        assert_eq!(map.get(k.as_slice()), None);
        assert_eq!(map.get([1u8, 2, 3, 4, 5, 6, 7, 8, 9].as_ref()), None);
    }

    #[test]
    fn tree_map_insert_get_modify_remove_len() {
        fn tree_map_test_insert_get_remove_len<const N: usize>(keys: [&[u8]; N]) {
            let mut map = TreeMap::<&[u8], _>::new();

            assert!(map.is_empty());
            assert_eq!(map.len(), 0);

            for (index, key) in keys.iter().enumerate() {
                assert!(map.try_insert(key, index).unwrap().is_none());

                assert_eq!(map.len(), index + 1);

                for other_key in keys.iter().skip(index + 1) {
                    assert!(map.get(other_key).is_none(), "{map:?} {other_key:?}");
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

    fn build_tree_map<const N: usize>(keys: [&[u8]; N]) -> TreeMap<Box<[u8]>, usize> {
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
            [
                &Box::from(*b"0010"),
                &Box::from(*b"0011"),
                &Box::from(*b"0012"),
                &Box::from(*b"0013"),
                &Box::from(*b"0014"),
                &Box::from(*b"0015")
            ]
        );

        for (key, value) in &map {
            assert!(key.starts_with(b"000") || key.starts_with(b"001"));
            assert_eq!(*value % 2, 0);
        }

        for (key, value) in &mut map {
            let key = String::from_utf8(Vec::from(key.as_ref())).unwrap();
            let key_number_value = key.trim_start_matches('0').parse::<usize>().unwrap_or(0);

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
                (&Box::from(*b"0000"), 999),
                (&Box::from(*b"0001"), 0),
                (&Box::from(*b"0002"), 999),
                (&Box::from(*b"0003"), 0),
                (&Box::from(*b"0004"), 999),
                (&Box::from(*b"0005"), 0),
                (&Box::from(*b"0010"), 56),
                (&Box::from(*b"0011"), 64),
                (&Box::from(*b"0012"), 58),
                (&Box::from(*b"0013"), 68),
                (&Box::from(*b"0014"), 60),
                (&Box::from(*b"0015"), 72)
            ]
        );
    }

    #[test]
    fn tree_into_iterator_removes_values_before_drop() {
        // This struct will panic on drop if the flag inside is true
        #[derive(Debug, PartialEq)]
        struct DropBomb(bool);

        impl Default for DropBomb {
            fn default() -> Self {
                DropBomb(true)
            }
        }

        impl DropBomb {
            fn defuse(&mut self) {
                self.0 = false;
            }
        }

        impl Drop for DropBomb {
            fn drop(&mut self) {
                if self.0 {
                    panic!("DropBomb was not disarmed!")
                }
            }
        }

        let mut map: TreeMap<_, _> = TreeMap::new();

        map.try_insert(Box::from(b"0000"), DropBomb::default())
            .unwrap();

        // Drop the tree and collect values into a vector (should not drop the key or
        // value)
        let mut entries = map.into_iter().collect::<Vec<_>>();

        assert_eq!(entries[0].0, Box::from(b"0000"));

        // Must defuse bomb before drop in Vector
        entries.iter_mut().for_each(|(_, bomb)| {
            bomb.defuse();
        })
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

    #[test]
    fn tree_hash_equals() {
        let mut tree_a = TreeMap::<[u8; 0], i32>::new();

        let _ = tree_a.try_insert([], 0);
        let _ = tree_a.pop_first();

        let tree_b = tree_a.clone();

        let hasher_builder = RandomState::new();

        let hash_a = hasher_builder.hash_one(&tree_a);
        let hash_b = hasher_builder.hash_one(&tree_b);

        assert_eq!(hash_a, hash_b);
    }

    #[test]
    fn mutating_operations_modify_len() {
        let mut tree = TreeMap::<Box<[u8]>, u8>::new();

        // check the normal state, a tree should never have any existing entries
        assert!(tree.is_empty());

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
            Err(InsertPrefixError {
                byte_repr: Box::new([])
            })
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
        assert_eq!(tree.remove(&Box::from([])), None);

        assert_eq!(tree.len(), 2);

        // normal removes, should reduce length by 2
        assert_eq!(tree.remove(&Box::from([2])), Some(3));
        assert_eq!(tree.remove(&Box::from([1])), Some(6));

        assert_eq!(tree.len(), 0);
        assert!(tree.is_empty());

        // remove operations on an empty tree should not do anything
        assert_eq!(tree.pop_first(), None);
        assert_eq!(tree.pop_last(), None);
        assert_eq!(tree.remove(&Box::from([])), None);
    }

    #[cfg(not(miri))]
    #[test]
    fn clone_tree_skewed() {
        let mut tree: TreeMap<Box<[u8]>, usize> = TreeMap::new();
        for (v, k) in generate_keys_skewed(u8::MAX as usize).enumerate() {
            tree.try_insert(k, v).unwrap();
        }
        let new_tree = tree.clone();
        assert!(tree == new_tree);
    }

    #[cfg(not(miri))]
    #[test]
    fn clone_tree_fixed_length() {
        let mut tree: TreeMap<_, usize> = TreeMap::new();
        for (v, k) in generate_key_fixed_length([2; 8]).enumerate() {
            tree.try_insert(k, v).unwrap();
        }
        let new_tree = tree.clone();
        assert!(tree == new_tree);
    }

    #[cfg(not(miri))]
    #[test]
    fn clone_tree_with_prefix() {
        let mut tree: TreeMap<Box<[u8]>, usize> = TreeMap::new();
        for (v, k) in generate_key_with_prefix(
            [2; 8],
            [
                PrefixExpansion {
                    base_index: 1,
                    expanded_length: 12,
                },
                PrefixExpansion {
                    base_index: 5,
                    expanded_length: 8,
                },
            ],
        )
        .enumerate()
        {
            tree.try_insert(k, v).unwrap();
        }
        let new_tree = tree.clone();
        assert!(tree == new_tree);
    }

    #[test]
    fn regression_29a4f553e0689f886010df5a425384b757d612ed() {
        // [
        //     Extend(
        //         [
        //             [
        //                 0,
        //             ],
        //             [
        //                 171,
        //                 171,
        //             ],
        //             [
        //                 65,
        //                 229,
        //             ],
        //         ],
        //     ),
        //     PopMinimum,
        //     Clone,
        //     PopMinimum,
        //     Clear,
        // ]

        let mut tree = TreeMap::<Box<[u8]>, u32>::new();
        let _ = tree.try_insert(Box::new([0]), 0);
        let _ = tree.try_insert(Box::new([171, 171]), 1);
        let _ = tree.try_insert(Box::new([65, 229]), 2);

        assert_eq!(tree.len(), 3);

        let minimum = tree.pop_first().unwrap();
        assert_eq!(minimum.0.as_ref(), &[0]);

        tree = tree.clone();

        let minimum = tree.pop_first().unwrap();
        assert_eq!(minimum.0.as_ref(), &[65, 229]);

        tree.clear();
        assert_eq!(tree.len(), 0);
        assert_eq!(tree.pop_first(), None);
    }
}
