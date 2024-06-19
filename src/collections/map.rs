//! Module containing implementations of the `TreeMap` and associated
//! iterators/etc.

use crate::{
    deallocate_tree, find_maximum_to_delete, find_minimum_to_delete, maximum_unchecked,
    minimum_unchecked,
    rust_nightly_apis::{box_new_uninit_slice, hasher_write_length_prefix},
    search_for_delete_point, search_for_insert_point, search_unchecked, AsBytes, ConcreteNodePtr,
    DeletePoint, DeleteResult, FuzzySearch, InsertPoint, InsertPrefixError, InsertResult,
    InsertSearchResultType::Exact,
    LeafNode, NoPrefixesBytes, NodeHeader, NodePtr, OpaqueNodePtr, StackArena,
};
use std::{
    borrow::Borrow,
    fmt::Debug,
    hash::{Hash, Hasher},
    ops::Index,
};

mod entry;
mod entry_ref;
mod iterators;
pub use entry::*;
pub use entry_ref::*;
pub use iterators::*;

/// An ordered map based on an adaptive radix tree.
pub struct RawTreeMap<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
{
    /// The number of entries present in the tree.
    num_entries: usize,
    /// A pointer to the tree root, if present.
    pub(crate) root: Option<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
{
    /// Create a new, empty [`crate::TreeMap`].
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
        RawTreeMap {
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
            let search_result = unsafe { search_unchecked(root, key)? };

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
            let search_result = unsafe { search_unchecked(root, key)? };

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
    /// less than or equal to `max_edit_dist`
    ///
    /// This is done by using Levenshtein distance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    /// use std::ffi::CString;

    /// let mut map: TreeMap<_, _> = TreeMap::new();

    /// map.insert(CString::from(c"abc"), 'a');
    /// map.insert(CString::from(c"abd"), 'b');
    /// map.insert(CString::from(c"abdefg"), 'c');

    /// // Returned kv would be ("abc", 'a'), ("abd", 'b')
    /// let fuzzy = map.get_fuzzy(c"ab", 2);
    /// assert_eq!(fuzzy.len(), 2);
    /// ```
    pub fn get_fuzzy<Q>(&self, key: &Q, max_edit_dist: usize) -> Vec<(&K, &V)>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        let Some(node) = self.root else {
            return vec![];
        };

        let key = key.as_bytes();
        let mut results = vec![];
        let mut nodes_to_search = vec![node];
        let mut arena = StackArena::new(key.len() + 1);
        let n = arena.size();
        let s = arena.push();

        #[allow(clippy::needless_range_loop)]
        for i in 0..n {
            s[i].write(i);
        }

        let mut old_row = box_new_uninit_slice(arena.size());
        let mut old_row = old_row.as_mut();
        let mut new_row = box_new_uninit_slice(arena.size());
        let mut new_row = new_row.as_mut();

        while let (Some(node), Some(old_row)) =
            (nodes_to_search.pop(), arena.pop_copy(&mut old_row))
        {
            match node.to_node_ptr() {
                ConcreteNodePtr::Node4(inner_ptr) => {
                    let inner_node = unsafe { inner_ptr.as_ref() };
                    inner_node.fuzzy_search(
                        &mut arena,
                        key,
                        old_row,
                        &mut new_row,
                        &mut nodes_to_search,
                        &mut results,
                        max_edit_dist,
                    );
                },
                ConcreteNodePtr::Node16(inner_ptr) => {
                    let inner_node = unsafe { inner_ptr.as_ref() };
                    inner_node.fuzzy_search(
                        &mut arena,
                        key,
                        old_row,
                        &mut new_row,
                        &mut nodes_to_search,
                        &mut results,
                        max_edit_dist,
                    );
                },
                ConcreteNodePtr::Node48(inner_ptr) => {
                    let inner_node = unsafe { inner_ptr.as_ref() };
                    inner_node.fuzzy_search(
                        &mut arena,
                        key,
                        old_row,
                        &mut new_row,
                        &mut nodes_to_search,
                        &mut results,
                        max_edit_dist,
                    );
                },
                ConcreteNodePtr::Node256(inner_ptr) => {
                    let inner_node = unsafe { inner_ptr.as_ref() };
                    inner_node.fuzzy_search(
                        &mut arena,
                        key,
                        old_row,
                        &mut new_row,
                        &mut nodes_to_search,
                        &mut results,
                        max_edit_dist,
                    );
                },
                ConcreteNodePtr::LeafNode(inner_ptr) => {
                    let inner_node = unsafe { inner_ptr.as_ref() };
                    inner_node.fuzzy_search(
                        &mut arena,
                        key,
                        old_row,
                        &mut new_row,
                        &mut nodes_to_search,
                        &mut results,
                        max_edit_dist,
                    );
                },
            };
        }
        results
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

    fn init_tree(
        &mut self,
        key: K,
        value: V,
    ) -> NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>> {
        let leaf = NodePtr::allocate_node_ptr(LeafNode::new(key, value));
        self.root = Some(leaf.to_opaque());
        self.num_entries = 1;
        leaf
    }

    fn apply_insert_point(
        &mut self,
        insert_point: InsertPoint<K, V, NUM_PREFIX_BYTES, H>,
        key: K,
        value: V,
    ) -> InsertResult<K, V, NUM_PREFIX_BYTES, H>
    where
        K: AsBytes,
    {
        let insert_result = insert_point.apply(key, value);

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
        delete_point: DeletePoint<K, V, NUM_PREFIX_BYTES, H>,
    ) -> DeleteResult<K, V, NUM_PREFIX_BYTES, H>
    where
        K: AsBytes,
    {
        let delete_result = delete_point.apply(unsafe { self.root.unwrap_unchecked() });

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
    /// not return an error, because the contract of the
    /// [`NoPrefixesBytes`][crate::bytes::NoPrefixesBytes] ensures that the
    /// given key type will never be a prefix of an existing value.
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
            let insert_point = unsafe { search_for_insert_point(root, &key)? };
            let insert_result = self.apply_insert_point(insert_point, key, value);
            Ok(insert_result.existing_leaf.map(|leaf| leaf.into_entry().1))
        } else {
            self.init_tree(key, value);
            Ok(None)
        }
    }

    /*
        #[inline(always)]
        #[allow(dead_code)]
        fn write_partitions<N, F>(
            header: Header,
            partitions: HashMap<u8, Vec<(K, V)>>,
            depth: usize,
            f: F,
        ) -> OpaqueNodePtr<K, V, H>
        where
            N: InnerNode<Key = K, Value = V, Header = H>,
            F: Fn(&mut N, u8, OpaqueNodePtr<K, V, H>),
        {
            let mut node = N::from_header(header);
            for (idx, partition) in partitions {
                let child = if partition.len() == 1 {
                    let (key, value) = partition.into_iter().next().unwrap();
                    NodePtr::allocate_node_ptr(LeafNode::new(key, value)).to_opaque()
                } else {
                    Self::inner_bulk_insert(partition, depth + 1)
                };
                f(&mut node, idx, child);
            }
            NodePtr::allocate_node_ptr(node).to_opaque()
        }

        #[allow(dead_code)]
        fn inner_bulk_insert(entries: Vec<(K, V)>, mut depth: usize) -> OpaqueNodePtr<K, V, H>
        where
            K: AsBytes,
        {
            unsafe {
                assume(entries.len() >= 2);
            }
            let first = entries.first().unwrap().0.as_bytes();
            let last = entries.last().unwrap().0.as_bytes();

            unsafe {
                assume(depth <= first.len());
                assume(depth <= last.len());
            }

            let lcp = first[depth..]
                .iter()
                .zip(&last[depth..])
                .take_while(|(a, b)| **a == **b)
                .count();

            unsafe {
                assume(depth + lcp <= first.len());
                assume(depth <= depth + lcp);
            }

            let header = Header::new(&first[depth..depth + lcp], lcp);
            depth += lcp;

            let mut partitions = HashMap::<u8, Vec<(K, V)>>::new();
            for entry in entries {
                unsafe {
                    let idx = *entry.0.as_bytes().get_unchecked(depth);
                    partitions.entry(idx).or_default().push(entry);
                }
            }

            let num_keys = partitions.len();
            if num_keys <= 4 {
                Self::write_partitions::<InnerNode4<K, V, H>, _>(
                    header,
                    partitions,
                    depth,
                    |node, idx, child| unsafe { node.write_child_unchecked(idx, child) },
                )
            } else if num_keys <= 16 {
                Self::write_partitions::<InnerNode16<K, V, H>, _>(
                    header,
                    partitions,
                    depth,
                    |node, idx, child| unsafe { node.write_child_unchecked(idx, child) },
                )
            } else if num_keys <= 48 {
                Self::write_partitions::<InnerNode48<K, V, H>, _>(
                    header,
                    partitions,
                    depth,
                    |node, idx, child| node.write_child(idx, child),
                )
            } else {
                Self::write_partitions::<InnerNode256<K, V, H>, _>(
                    header,
                    partitions,
                    depth,
                    |node, idx, child| node.write_child(idx, child),
                )
            }
        }

        #[allow(dead_code)]
        fn bulk_insert(mut entries: Vec<(K, V)>) -> Self
        where
            K: AsBytes,
        {
            if entries.is_empty() {
                return Self::new();
            }

            if entries.len() == 1 {
                let (key, value) = entries.into_iter().next().unwrap();
                return Self {
                    num_entries: 1,
                    root: Some(NodePtr::allocate_node_ptr(LeafNode::new(key, value)).to_opaque()),
                };
            }

            let num_entries = entries.len();
            entries.sort_by(|l1, l2| l1.0.as_bytes().cmp(l2.0.as_bytes()));
            let root = Self::inner_bulk_insert(entries, 0);
            Self {
                num_entries,
                root: Some(root),
            }
        }

        #[allow(dead_code)]
        fn bulk_insert_unchecked(entries: Vec<(K, V)>) -> Self
        where
            K: AsBytes,
        {
            if entries.is_empty() {
                return Self::new();
            }

            if entries.len() == 1 {
                let (key, value) = entries.into_iter().next().unwrap();
                return Self {
                    num_entries: 1,
                    root: Some(NodePtr::allocate_node_ptr(LeafNode::new(key, value)).to_opaque()),
                };
            }

            let num_entries = entries.len();
            let root = Self::inner_bulk_insert(entries, 0);
            Self {
                num_entries,
                root: Some(root),
            }
        }
    */

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
            let delete_point = unsafe { search_for_delete_point(root, key)? };
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
    #[allow(dead_code)]
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
    pub(crate) fn append(&mut self, other: &mut TreeMap<K, V, NUM_PREFIX_BYTES, H>)
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
    pub(crate) fn range<Q, R>(&self, _range: R) -> iterators::Range<K, V, H>
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
    pub(crate) fn range_mut<Q, R>(&mut self, _range: R) -> iterators::RangeMut<K, V, H>
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
    pub(crate) fn split_off<Q>(&mut self, split_key: &Q) -> TreeMap<K, V, NUM_PREFIX_BYTES, H>
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
    /// dropping an element, or if the DrainFilter value is leaked.
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
    pub fn into_keys(self) -> iterators::IntoKeys<K, V, NUM_PREFIX_BYTES, H> {
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
    pub fn into_values(self) -> iterators::IntoValues<K, V, NUM_PREFIX_BYTES, H> {
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
    pub fn iter(&self) -> TreeIterator<'_, K, V, NUM_PREFIX_BYTES, H> {
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
    pub fn iter_mut(&mut self) -> TreeIteratorMut<'_, K, V, NUM_PREFIX_BYTES, H> {
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
    pub fn keys(&self) -> Keys<'_, K, V, NUM_PREFIX_BYTES, H> {
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
    pub fn values(&self) -> Values<'_, K, V, NUM_PREFIX_BYTES, H> {
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
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, NUM_PREFIX_BYTES, H> {
        ValuesMut::new(self)
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

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
{
    /// Tries to get the given key’s corresponding entry in the map for in-place
    /// manipulation.
    pub fn try_entry(
        &mut self,
        key: K,
    ) -> Result<Entry<K, V, NUM_PREFIX_BYTES, H>, InsertPrefixError>
    where
        K: AsBytes,
    {
        let entry = match self.root {
            Some(root) => {
                let insert_point = unsafe { search_for_insert_point(root, &key)? };
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
    ) -> Result<EntryRef<'a, 'b, K, V, Q, NUM_PREFIX_BYTES, H>, InsertPrefixError>
    where
        K: AsBytes + Borrow<Q> + From<&'b Q>,
        Q: AsBytes + ?Sized,
    {
        let entry = match self.root {
            Some(root) => {
                let insert_point = unsafe { search_for_insert_point(root, key)? };
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
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, NUM_PREFIX_BYTES, H>
    where
        K: NoPrefixesBytes,
    {
        unsafe { self.try_entry(key).unwrap_unchecked() }
    }

    /// Gets the given key’s corresponding entry in the map for in-place
    /// manipulation.
    pub fn entry_ref<'a, 'b, Q>(
        &'a mut self,
        key: &'b Q,
    ) -> EntryRef<'a, 'b, K, V, Q, NUM_PREFIX_BYTES, H>
    where
        K: NoPrefixesBytes + Borrow<Q> + From<&'b Q>,
        Q: NoPrefixesBytes + ?Sized,
    {
        unsafe { self.try_entry_ref(key).unwrap_unchecked() }
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Drop
    for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
{
    fn drop(&mut self) {
        self.clear();
    }
}

impl<K, V, const NUM_PREFIX_BYTES: usize, H> Clone for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: Clone + AsBytes,
    V: Clone,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn clone(&self) -> Self {
        if let Some(root) = self.root {
            Self {
                root: Some(root.deep_clone()),
                num_entries: self.num_entries,
            }
        } else {
            Self::new()
        }
    }
}

impl<K, V, const NUM_PREFIX_BYTES: usize, H> Debug for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: Debug + AsBytes,
    V: Debug,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Default
    for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, K, V, const NUM_PREFIX_BYTES: usize, H> Extend<(&'a K, &'a V)>
    for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: Copy + NoPrefixesBytes,
    V: Copy,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            let _ = self.insert(*key, *value);
        }
    }
}

impl<K, V, const NUM_PREFIX_BYTES: usize, H> Extend<(K, V)>
    for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: NoPrefixesBytes,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            let _ = self.insert(key, value);
        }
    }
}

impl<K, V, const NUM_PREFIX_BYTES: usize, H, const N: usize> From<[(K, V); N]>
    for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: NoPrefixesBytes,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn from(arr: [(K, V); N]) -> Self {
        let mut map = RawTreeMap::new();
        for (key, value) in arr {
            let _ = map.insert(key, value);
        }
        map
    }
}

impl<K, V, const NUM_PREFIX_BYTES: usize, H> FromIterator<(K, V)>
    for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: NoPrefixesBytes,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = RawTreeMap::new();
        for (key, value) in iter {
            let _ = map.insert(key, value);
        }
        map
    }
}

impl<K, V, const NUM_PREFIX_BYTES: usize, H1> Hash for RawTreeMap<K, V, NUM_PREFIX_BYTES, H1>
where
    K: Hash + AsBytes,
    V: Hash,
    H1: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        hasher_write_length_prefix(state, self.num_entries);
        for elt in self {
            elt.hash(state);
        }
    }
}

impl<Q, K, V, const NUM_PREFIX_BYTES: usize, H> Index<&Q> for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: Borrow<Q> + AsBytes,
    Q: AsBytes + ?Sized,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    type Output = V;

    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> IntoIterator
    for &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
{
    type IntoIter = TreeIterator<'a, K, V, NUM_PREFIX_BYTES, H>;
    type Item = (&'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> IntoIterator
    for &'a mut RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
{
    type IntoIter = TreeIteratorMut<'a, K, V, NUM_PREFIX_BYTES, H>;
    type Item = (&'a K, &'a mut V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> IntoIterator
    for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
{
    type IntoIter = iterators::IntoIter<K, V, NUM_PREFIX_BYTES, H>;
    type Item = (K, V);

    fn into_iter(self) -> Self::IntoIter {
        iterators::IntoIter::new(self)
    }
}

impl<K, V, H, const NUM_PREFIX_BYTES: usize> Ord for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: Ord + AsBytes,
    V: Ord,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<K, V, H, const NUM_PREFIX_BYTES: usize> PartialOrd for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: PartialOrd + AsBytes,
    V: PartialOrd,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K, V, H, const NUM_PREFIX_BYTES: usize> Eq for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: Eq + AsBytes,
    V: Eq,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
}

impl<K, V, H, const NUM_PREFIX_BYTES: usize> PartialEq for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: PartialEq + AsBytes,
    V: PartialEq,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter()) && self.num_entries == other.num_entries
    }
}

unsafe impl<K, V, H, const NUM_PREFIX_BYTES: usize> Send for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: Send + AsBytes,
    V: Send,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
}

unsafe impl<K, V, H, const NUM_PREFIX_BYTES: usize> Sync for RawTreeMap<K, V, NUM_PREFIX_BYTES, H>
where
    K: Sync + AsBytes,
    V: Sync,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
}

#[cfg(test)]
mod tests {
    use std::{cmp::Ordering, collections::hash_map::RandomState, ffi::CString, hash::BuildHasher};

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
        let mut map = RawTreeMap::new();

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

    fn hash_one(hasher_builder: &impl BuildHasher, value: impl Hash) -> u64 {
        hasher_builder.hash_one(&value)
    }

    #[test]
    fn tree_hash_equals() {
        let mut tree_a = TreeMap::<[u8; 0], i32>::new();

        let _ = tree_a.try_insert([], 0);
        let _ = tree_a.pop_first();

        let tree_b = tree_a.clone();

        let hasher_builder = RandomState::new();

        let hash_a = hash_one(&hasher_builder, &tree_a);
        let hash_b = hash_one(&hasher_builder, &tree_b);

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

    #[test]
    fn get_fuzzy() {
        for n in [4, 5, 17, 49] {
            let it = 48u8..48 + n;
            let mut tree: TreeMap<CString, usize> = TreeMap::new();
            let search = CString::new("a").unwrap();
            for c in it.clone() {
                let c = c as char;
                let s = CString::new(format!("a{c}")).unwrap();
                tree.insert(s, 0usize);
            }
            let results = tree.get_fuzzy(&search, 1);
            for ((k, _), c) in results.into_iter().rev().zip(it.clone()) {
                let c = c as char;
                let s = CString::new(format!("a{c}")).unwrap();
                assert_eq!(k, &s);
            }

            let mut tree: TreeMap<CString, usize> = TreeMap::new();
            let search = CString::new("a").unwrap();
            for c in it.clone() {
                let s = if c % 2 == 0 {
                    let c = c as char;
                    CString::new(format!("a{c}")).unwrap()
                } else {
                    let c = c as char;
                    CString::new(format!("a{c}a")).unwrap()
                };
                tree.insert(s, 0usize);
            }
            let results = tree.get_fuzzy(&search, 1);
            for ((k, _), c) in results.into_iter().rev().zip((it.clone()).step_by(2)) {
                let c = c as char;
                let s = CString::new(format!("a{c}")).unwrap();
                assert_eq!(k, &s);
            }

            let mut tree: TreeMap<CString, usize> = TreeMap::new();
            let search = CString::new("a").unwrap();
            for c in it.clone() {
                let s = if c % 2 == 0 {
                    let c = c as char;
                    CString::new(format!("a{c}")).unwrap()
                } else {
                    let c = c as char;
                    CString::new(format!("a{c}a")).unwrap()
                };
                tree.insert(s, 0usize);
            }
            let results = tree.get_fuzzy(&search, 2);
            for ((k, _), c) in results.into_iter().rev().zip(it.clone()) {
                let s = if c % 2 == 0 {
                    let c = c as char;
                    CString::new(format!("a{c}")).unwrap()
                } else {
                    let c = c as char;
                    CString::new(format!("a{c}a")).unwrap()
                };
                assert_eq!(k, &s);
            }
        }
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
        let mut tree: TreeMap<Box<[u8]>, usize> = TreeMap::new();
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
}
