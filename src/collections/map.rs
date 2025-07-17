//! Module containing implementations of the `TreeMap` and associated
//! iterators/etc.

#[cfg(feature = "std")]
use crate::visitor::{MalformedTreeError, WellFormedChecker};
use crate::{
    allocator::{Allocator, Global},
    raw::{
        clone_unchecked, deallocate_tree, find_maximum_to_delete, find_minimum_to_delete,
        maximum_unchecked, minimum_unchecked, prefix_search_unchecked, search_for_delete_point,
        search_for_insert_point, search_for_prefix_insert_point, search_unchecked, CloneResult,
        DeletePoint, DeleteResult, InsertKind, InsertPoint, InsertPrefixError, InsertResult,
        LeafNode, NodePtr, OpaqueNodePtr, PrefixInsertPoint, RawIterator,
    },
    rust_nightly_apis::hasher_write_length_prefix,
    AsBytes, NoPrefixesBytes,
};
use alloc::vec::Vec;
use core::{
    borrow::Borrow,
    fmt::Debug,
    hash::Hash,
    mem::{self, ManuallyDrop},
    ops::{Index, RangeBounds},
    panic::UnwindSafe,
    ptr,
};

mod entry;
mod iterators;
mod prefix_entry;
pub use entry::*;
pub use iterators::*;
pub use prefix_entry::*;

/// This is the default number of bytes that are used in each inner node for
/// storing key prefixes.
pub const DEFAULT_PREFIX_LEN: usize = 16;

/// An ordered map based on an adaptive radix tree.
pub struct TreeMap<K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global> {
    /// The number of entries present in the tree.
    num_entries: usize,
    /// A pointer to the tree root, if present.
    pub(crate) state: Option<NonEmptyTree<K, V, PREFIX_LEN>>,
    /// The allocator which will be used to alloc and dealloc tree nodes.
    alloc: A,
}

pub(crate) struct NonEmptyTree<K, V, const PREFIX_LEN: usize> {
    pub(crate) root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    min_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    max_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
}

// Need to implement this manually because `NonEmptyTree` contains `NonNull`
// pointers which are used to mutate the tree.
//
// It is safe in this case since we always maintain a mutable reference to the
// tree as a whole when we do mutations.
impl<K: UnwindSafe, V: UnwindSafe, const PREFIX_LEN: usize> UnwindSafe
    for NonEmptyTree<K, V, PREFIX_LEN>
{
}

impl<K, V> TreeMap<K, V> {
    /// Create a new, empty [`TreeMap`] with the default number of prefix
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

impl<K, V, A: Allocator> TreeMap<K, V, DEFAULT_PREFIX_LEN, A> {
    /// Create a new, empty [`TreeMap`] with the default number of prefix bytes
    /// (16), which will allocate tree nodes using the given allocator.
    ///
    /// This function will not pre-allocate anything.
    #[cfg_attr(
        any(feature = "nightly", feature = "allocator-api2"),
        doc = r##"
# Examples

```rust
use blart::{TreeMap, map::DEFAULT_PREFIX_LEN};
use std::alloc::System;

let mut map = TreeMap::<_, i32, DEFAULT_PREFIX_LEN, _>::new_in(System);
assert!(map.is_empty());
map.insert(c"abc", 0);
assert_eq!(*map.get(c"abc").unwrap(), 0);
```
    "##
    )]
    pub fn new_in(alloc: A) -> Self {
        Self::with_prefix_len_in(alloc)
    }
}

impl<K, V, const PREFIX_LEN: usize> TreeMap<K, V, PREFIX_LEN> {
    /// Create a new, empty [`TreeMap`] with a non-default node prefix
    /// length.
    ///
    /// This function will not pre-allocate anything. The prefix length is
    /// inferred as a const-generic parameter on the type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let map = TreeMap::<Box<[u8]>, (), 8>::with_prefix_len();
    /// assert!(map.is_empty());
    /// ```
    pub fn with_prefix_len() -> Self {
        TreeMap {
            num_entries: 0,
            state: None,
            alloc: Global,
        }
    }

    /// Constructs a [`TreeMap`] from a raw node pointer.
    ///
    /// # Safety
    ///
    ///  - The raw pointer must have been previously returned by a call to
    ///    [`TreeMap::into_raw_with_allocator`] or [`TreeMap::into_raw`].
    ///     - The allocator of the previous tree must have been the "default"
    ///       allocator named `Global`.
    ///  - The given `root` pointer must be unique and there are no other
    ///    pointers into the tree.
    ///  - `root` must be a pointer to a well formed tree.
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
    /// let _map = unsafe { TreeMap::from_raw_unchecked(root) };
    /// ```
    pub unsafe fn from_raw_unchecked(root: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>) -> Self
    where
        K: AsBytes,
    {
        // SAFETY: The safety requirement of `from_raw_in` are a superset of the ones on
        // `from_raw`.
        unsafe { Self::from_raw_in_unchecked(root, Global) }
    }

    #[cfg(feature = "std")]
    /// Constructs a [`TreeMap`] from a raw node pointer.
    ///
    /// # Safety
    ///
    ///  - The raw pointer must have been previously returned by a call to
    ///    [`TreeMap::into_raw_with_allocator`] or [`TreeMap::into_raw`].
    ///     - The allocator of the previous tree must have been the "default"
    ///       allocator named `Global`.
    ///  - The given `root` pointer must be unique and there are no other
    ///    pointers into the tree.
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
        // SAFETY: The safety requirement of `from_raw_in` are a superset of the ones on
        // `from_raw`.
        unsafe { Self::from_raw_in(root, Global) }
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> TreeMap<K, V, PREFIX_LEN, A> {
    /// Returns a reference to the underlying allocator.
    #[cfg_attr(
        any(feature = "nightly", feature = "allocator-api2"),
        doc = r##"
# Examples

```rust
use blart::{TreeMap, map::DEFAULT_PREFIX_LEN};
use std::alloc::System;

let map = TreeMap::<Box<[u8]>, i32, DEFAULT_PREFIX_LEN, _>::new_in(System);
assert!(matches!(map.allocator(), &System));
```
    "##
    )]
    pub fn allocator(&self) -> &A {
        &self.alloc
    }

    /// Create a new, empty [`TreeMap`] with a non-default node prefix
    /// length, and the given allocator for allocating tree nodes.
    ///
    /// This function will not pre-allocate anything. The prefix length is
    /// inferred as a const-generic parameter on the type.
    #[cfg_attr(
        any(feature = "nightly", feature = "allocator-api2"),
        doc = r##"
# Examples

```rust
use blart::TreeMap;
use std::alloc::System;

let map = TreeMap::<Box<[u8]>, i32, 8, _>::with_prefix_len_in(System);
assert!(matches!(map.allocator(), &System));
```
    "##
    )]
    pub fn with_prefix_len_in(alloc: A) -> Self {
        TreeMap {
            num_entries: 0,
            state: None,
            alloc,
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
        if let Some(state) = &mut self.state {
            // SAFETY:
            //  - Since we have a mutable reference to the map, we know that there are no
            //    other mutable references to any node in the tree, meaning we can
            //    deallocate all of them.
            //  - `self.alloc` was used to allocate all the nodes of the tree
            unsafe {
                deallocate_tree(state.root, &self.alloc);
            }

            self.num_entries = 0;
            self.state = None;
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
    ///
    /// // SAFETY: The root pointer came directly from the `into_raw` result.
    /// let _map = unsafe { TreeMap::from_raw_unchecked(root) };
    /// ```
    pub fn into_raw(tree: Self) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>> {
        Self::into_raw_with_allocator(tree).0
    }

    /// Consume the tree, returning a raw pointer to the root node and the
    /// allocator of the tree.
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
    /// let (root, alloc) = TreeMap::into_raw_with_allocator(map);
    /// assert!(root.is_some());
    ///
    /// // SAFETY: The root pointer came directly from the `into_raw` result.
    /// let _map = unsafe { TreeMap::from_raw_in_unchecked(root, alloc) };
    /// ```
    pub fn into_raw_with_allocator(tree: Self) -> (Option<OpaqueNodePtr<K, V, PREFIX_LEN>>, A) {
        // We need this `ManuallyDrop` so that the `TreeMap::drop` is not called.
        // Since the `root` field is `Copy`, it can be moved out of the tree without
        // inhibiting `Drop`
        let tree = ManuallyDrop::new(tree);
        // SAFETY: Since we're reading from an `&A` that was coerced to a `*const A` we
        // know that the pointer is valid for reads, properly aligned, and properly
        // initialized.
        //
        // Also this is safe from a double-free since we're using `ManuallyDrop` to
        // inhibit the first copy of `A` (in the `tree` value) from doing anything.
        let alloc = unsafe { ptr::read(&tree.alloc) };
        let root = tree.state.as_ref().map(|state| state.root);

        (root, alloc)
    }

    /// Constructs a [`TreeMap`] from a raw node pointer and the given
    /// allocator.
    ///
    /// # Safety
    ///
    ///  - The raw pointer must have been previously returned by a call to
    ///    [`TreeMap::into_raw_with_allocator`] or [`TreeMap::into_raw`] with a
    ///    known allocator.
    ///  - The given `root` pointer must be unique and there are no other
    ///    pointers into the tree.
    ///  - The given `alloc` must have been used to allocate all of the nodes
    ///    referenced by the given `root` pointer.
    ///  - `root` must be a pointer to a well formed tree.
    pub unsafe fn from_raw_in_unchecked(
        root: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
        alloc: A,
    ) -> Self
    where
        K: AsBytes,
    {
        match root {
            Some(root) => {
                let (min_leaf, max_leaf) =
                    // SAFETY: The safety doc of this function guarantees the uniqueness of the
                    // `root` pointer, which means we won't have any other mutations
                    unsafe { (minimum_unchecked(root), maximum_unchecked(root)) };
                // SAFETY: satisfied by minimum_unchecked and maximum unchecked.
                let mut raw_iter = unsafe { RawIterator::new(min_leaf, max_leaf) };
                let mut num_entries = 0;
                // SAFETY: The safety doc of this function guarantees no concurrent access.
                while unsafe { raw_iter.next() }.is_some() {
                    num_entries += 1;
                }

                Self {
                    state: Some(NonEmptyTree {
                        root,
                        min_leaf,
                        max_leaf,
                    }),
                    num_entries,
                    alloc,
                }
            },
            None => Self::with_prefix_len_in(alloc),
        }
    }

    #[cfg(feature = "std")]
    /// Constructs a [`TreeMap`] from a raw node pointer and the given
    /// allocator.
    ///
    /// # Safety
    ///
    ///  - The raw pointer must have been previously returned by a call to
    ///    [`TreeMap::into_raw_with_allocator`] or [`TreeMap::into_raw`] with a
    ///    known allocator.
    ///  - The given `root` pointer must be unique and there are no other
    ///    pointers into the tree.
    ///  - The given `alloc` must have been used to allocate all of the nodes
    ///    referenced by the given `root` pointer.
    ///
    /// # Errors
    ///
    /// This function runs a series of checks to ensure that the returned tree
    /// is well-formed. See [`WellFormedChecker`] for details on the
    /// requirements.
    #[cfg_attr(
        any(feature = "nightly", feature = "allocator-api2"),
        doc = r##"
# Examples

Using the [`TreeMap::into_raw`] function to get the root node pointer:

```rust
use blart::{TreeMap, map::DEFAULT_PREFIX_LEN};
use std::alloc::System;

let mut map = TreeMap::<Box<[u8]>, char, DEFAULT_PREFIX_LEN, _>::new_in(System);

map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
assert_eq!(map.len(), 1);
assert!(matches!(map.allocator(), &System));

let root = TreeMap::into_raw(map);
assert!(root.is_some());

// SAFETY: The root pointer came directly from the `into_raw` result.
let _map = unsafe { TreeMap::from_raw_in(root, System) }.unwrap();
```

Using the [`TreeMap::into_raw_with_allocator`] function to get the root
node pointer and allocator:

```rust
use blart::TreeMap;

let mut map = TreeMap::<Box<[u8]>, char>::new();

map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
assert_eq!(map.len(), 1);

let (root, alloc) = TreeMap::into_raw_with_allocator(map);

assert!(root.is_some());

// SAFETY: The root pointer came directly from the `into_raw` result.
let _map = unsafe { TreeMap::from_raw_in(root, alloc) }.unwrap();
```
    "##
    )]
    pub unsafe fn from_raw_in(
        root: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>,
        alloc: A,
    ) -> Result<Self, MalformedTreeError<K, V, PREFIX_LEN>>
    where
        K: AsBytes,
    {
        match root {
            Some(root) => {
                // SAFETY: The safety doc of this function guarantees the uniqueness of the
                // `root` pointer, which means we won't have any other mutations
                let stats = unsafe { WellFormedChecker::check_tree(root)? };

                let (min_leaf, max_leaf) =
                    // SAFETY: The safety doc of this function guarantees the uniqueness of the
                // `root` pointer, which means we won't have any other mutations
                    unsafe { (minimum_unchecked(root), maximum_unchecked(root)) };

                Ok(Self {
                    state: Some(NonEmptyTree {
                        root,
                        min_leaf,
                        max_leaf,
                    }),
                    num_entries: stats.num_leaf,
                    alloc,
                })
            },
            None => Ok(Self::with_prefix_len_in(alloc)),
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
        if let Some(state) = &self.state {
            // SAFETY: Since we have an immutable reference to the `TreeMap` object, that
            // means there can only exist other immutable references aside from this one,
            // and no mutable references. That means that no mutating operations can occur
            // on the root node or any child of the root node.
            let search_result = unsafe { search_unchecked(state.root, key.as_bytes())? };

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
        if let Some(state) = &self.state {
            // SAFETY: Since we have a mutable reference to the `TreeMap` object, that
            // means there cannot exist any other reference (mutable or immutable) to the
            // same `TreeMap`. Which means that no other mutating operations could be
            // happening during the `search_unchecked` call.
            let search_result = unsafe { search_unchecked(state.root, key.as_bytes())? };

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

    /// Returns a reference to the value corresponding to the leaf that prefixes
    /// the given key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// assert_eq!(*map.prefix_get([1, 2, 3, 4, 5].as_ref()).unwrap(), 'a');
    /// ```
    pub fn prefix_get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        Some(self.prefix_get_key_value(key)?.1)
    }

    /// Returns the key-value pair corresponding to the value of the leaf that
    /// prefixes the given key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// assert_eq!(
    ///     map.prefix_get_key_value([1, 2, 3, 4, 5].as_ref()).map(|(k, v)| (k.as_ref(), v)),
    ///     Some(([1, 2, 3].as_ref(), &'a'))
    /// );
    /// ```
    pub fn prefix_get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        if let Some(state) = &self.state {
            // SAFETY: Since we have an immutable reference to the `TreeMap` object, that
            // means there can only exist other immutable references aside from this one,
            // and no mutable references. That means that no mutating operations can occur
            // on the root node or any child of the root node.
            let search_result = unsafe { prefix_search_unchecked(state.root, key.as_bytes())? };

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

    /// Returns the key-value pair, with the value as a mutable reference,
    /// corresponding to the value of the leaf that prefixes the given key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
    /// let value = map.prefix_get_key_value_mut([1, 2, 3, 4, 5].as_ref()).unwrap();
    /// if value.0.last() == Some(&3) {
    ///     *value.1 = 'b';
    /// }
    /// assert_eq!(map.get([1, 2, 3].as_ref()), Some(&'b'));
    /// ```
    pub fn prefix_get_key_value_mut<Q>(&mut self, key: &Q) -> Option<(&K, &mut V)>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        if let Some(state) = &self.state {
            // SAFETY: Since we have an immutable reference to the `TreeMap` object, that
            // means there can only exist other immutable references aside from this one,
            // and no mutable references. That means that no mutating operations can occur
            // on the root node or any child of the root node.
            let search_result = unsafe { prefix_search_unchecked(state.root, key.as_bytes())? };

            // SAFETY: The lifetime chosen the value reference is bounded by the lifetime of
            // the immutable reference to the `TreeMap`. The memory of the value will not be
            // mutated since it is only owned by the `TreeMap` and there can only be other
            // immutable references at this time (no mutable references to the `TreeMap`).
            let (key, value) = unsafe { search_result.as_key_ref_value_mut() };
            Some((key, value))
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value corresponding to the leaf that
    /// prefixes the given key.
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
    /// *map.prefix_get_mut([1, 2, 3, 4].as_ref()).unwrap() = 'b';
    /// assert_eq!(map[[1, 2, 3].as_ref()], 'b');
    /// ```
    pub fn prefix_get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        if let Some(state) = &self.state {
            // SAFETY: Since we have a mutable reference to the `TreeMap` object, that
            // means there cannot exist any other reference (mutable or immutable) to the
            // same `TreeMap`. Which means that no other mutating operations could be
            // happening during the `search_unchecked` call.
            let search_result = unsafe { prefix_search_unchecked(state.root, key.as_bytes())? };

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
    ) -> Fuzzy<'a, 'b, K, V, PREFIX_LEN, A>
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
    ) -> FuzzyMut<'a, 'b, K, V, PREFIX_LEN, A>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
    {
        FuzzyMut::new(self, key.as_bytes(), max_edit_dist)
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
        if let Some(state) = &self.state {
            // SAFETY: The lifetime chosen the value reference is bounded by the lifetime of
            // the immutable reference to the `TreeMap`. The memory of the value will not be
            // mutated since it is only owned by the `TreeMap` and there can only be other
            // immutable references at this time (no mutable references to the `TreeMap`).
            let leaf_node_ref = unsafe { state.min_leaf.as_ref() };

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
        if let Some(state) = &self.state {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let delete_point = unsafe { find_minimum_to_delete(state.root) };

            // SAFETY: There are no outstanding pointers (besides leaf min/max which are
            // already fixed by `apply_delete_pointer`).
            let delete_result = unsafe { self.apply_delete_point(delete_point) };
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
        if let Some(state) = &self.state {
            // SAFETY: The lifetime chosen the value reference is bounded by the lifetime of
            // the immutable reference to the `TreeMap`. The memory of the value will not be
            // mutated since it is only owned by the `TreeMap` and there can only be other
            // immutable references at this time (no mutable references to the `TreeMap`).
            let leaf_node_ref = unsafe { state.max_leaf.as_ref() };

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
        if let Some(state) = &self.state {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let delete_point = unsafe { find_maximum_to_delete(state.root) };
            // SAFETY: There are no outstanding pointers (besides leaf min/max which are
            // already fixed by `apply_delete_pointer`).
            let delete_result = unsafe { self.apply_delete_point(delete_point) };
            Some(delete_result.deleted_leaf.into_entry())
        } else {
            None
        }
    }

    fn init_tree(&mut self, key: K, value: V) -> NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>> {
        // Since this is a singleton tree, the single leaf node has no siblings
        let leaf = NodePtr::allocate_node_ptr(LeafNode::with_no_siblings(key, value), &self.alloc);
        let state = NonEmptyTree {
            root: leaf.to_opaque(),
            min_leaf: leaf,
            max_leaf: leaf,
        };
        self.state = Some(state);
        self.num_entries = 1;
        leaf
    }

    /// Add the given insert point to the tree, fixing up the other tree
    /// state afterwards.
    ///
    /// This function will update the min/max leaf pointers, the number of nodes
    /// in the tree, and the tree root.
    ///
    /// # Safety
    ///
    /// This function may invalidate existing pointers into the tree when inner
    /// nodes are grown and the old inner node is deleted.
    ///
    /// Callers must ensure that they delete invalidated pointers, the new
    /// pointers are returned in [`InsertResult`].
    unsafe fn apply_insert_point(
        &mut self,
        insert_point: InsertPoint<K, V, PREFIX_LEN>,
        key: K,
        value: V,
    ) -> InsertResult<'_, K, V, PREFIX_LEN>
    where
        K: AsBytes,
    {
        // SAFETY:
        //  - This call is safe because we have a mutable reference on the tree, so no
        //    other operation can be concurrent with this one.
        //  - The same allocator is used for all inserts and deletes
        let insert_result = unsafe { insert_point.apply(key, value, &self.alloc) };
        let insert_result = self.apply_insert_result(insert_result);

        insert_result
    }

    fn apply_prefix_insert_point(
        &mut self,
        insert_point: PrefixInsertPoint<K, V, PREFIX_LEN>,
        key: K,
        value: V,
    ) -> InsertResult<'_, K, V, PREFIX_LEN>
    where
        K: AsBytes,
    {
        // SAFETY:
        //  - This call is safe because we have a mutable reference on the tree, so no
        //    other operation can be concurrent with this one.
        //  - The same allocator is used for all inserts and deletes
        let insert_result = unsafe { insert_point.apply(key, value, &self.alloc) };
        let leafs_removed = insert_result.leafs_removed;
        let insert_result = self.apply_insert_result(insert_result.insert_result);

        self.num_entries -= leafs_removed;

        insert_result
    }

    fn apply_insert_result<'a>(
        &mut self,
        insert_result: InsertResult<'a, K, V, PREFIX_LEN>,
    ) -> InsertResult<'a, K, V, PREFIX_LEN>
    where
        K: AsBytes,
    {
        match &mut self.state {
            Some(state) => {
                state.root = insert_result.new_root;

                {
                    // SAFETY: This call is safe because we have a mutable reference on the tree and
                    // the returned reference is bounded to this block, not returned
                    let new_leaf = unsafe { insert_result.leaf_node_ptr.as_ref() };
                    if new_leaf.previous.is_none() {
                        state.min_leaf = insert_result.leaf_node_ptr;
                    }

                    if new_leaf.next.is_none() {
                        state.max_leaf = insert_result.leaf_node_ptr;
                    }
                }
            },
            None => {
                self.state = Some(NonEmptyTree {
                    root: insert_result.new_root,
                    min_leaf: insert_result.leaf_node_ptr,
                    max_leaf: insert_result.leaf_node_ptr,
                })
            },
        }

        if insert_result.existing_leaf.is_none() {
            // this was a strict add, not a replace. If there was an existing leaf we are
            // removing and adding a leaf, so the number of entries stays the same
            self.num_entries += 1;
        }

        insert_result
    }

    /// Remove the given delete point from the tree, fixing up the other tree
    /// state afterwards.
    ///
    /// This function will update the min/max leaf pointers, the number of nodes
    /// in the tree, and the tree root.
    ///
    /// # Safety
    ///
    /// This function may invalidate existing pointers into the trie when leaves
    /// are deleted and when inner nodes are deleted or shrunk.
    ///
    /// Callers must ensure that they delete invalidated pointers, the new
    /// pointers are returned in [`DeleteResult`].
    unsafe fn apply_delete_point(
        &mut self,
        delete_point: DeletePoint<K, V, PREFIX_LEN>,
    ) -> DeleteResult<K, V, PREFIX_LEN> {
        // SAFETY:
        // - The root is sure to not be `None`, since the we somehow got a
        //   `DeletePoint`. So the caller must have checked this. Also, since we have a
        //   mutable reference to the tree, no other read or write operation can be
        //   happening concurrently.
        // - `self.alloc` is the same allocator which is used for all inserts and
        //   deletes on this tree
        // - Invalidated pointers covered by this caller's functions requirements
        let delete_result =
            unsafe { delete_point.apply(self.state.as_ref().unwrap_unchecked().root, &self.alloc) };

        match &mut self.state {
            Some(state) => {
                if let Some(new_root) = delete_result.new_root {
                    state.root = new_root;

                    if delete_result.deleted_leaf.previous.is_none() {
                        state.min_leaf = delete_result.deleted_leaf.next.expect(
                            "this should be Some since this is the non-singleton delete case",
                        );
                    }

                    if delete_result.deleted_leaf.next.is_none() {
                        state.max_leaf = delete_result.deleted_leaf.previous.expect(
                            "this should be Some since this is the non-singleton delete case",
                        );
                    }
                } else {
                    self.state = None;
                }
            },
            None => unreachable!("a successful deletion requires a non-empty tree"),
        }

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
        if let Some(state) = &self.state {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let insert_point = unsafe { search_for_insert_point(state.root, key.as_bytes()) }?;
            // SAFETY: We're not holding any pointers into the tree that we intend to use
            let insert_result = unsafe { self.apply_insert_point(insert_point, key, value) };
            Ok(insert_result.existing_leaf.map(|leaf| leaf.into_entry().1))
        } else {
            self.init_tree(key, value);
            Ok(None)
        }
    }

    /// Force inserts a key-value pair into the map.
    ///
    /// If the given key is not a prefix of any keys in the tree, this function
    /// behaves just like [`Self::try_insert`]. If the given key is a prefix
    /// of some keys in the tree, or the other way around, all these key
    /// value pairs are removed and this key value pair is inserted in their
    /// place.
    ///
    /// See also: [`Self::prefix_get`] and friends.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map = TreeMap::<Box<[u8]>, char>::new();
    ///
    /// map.prefix_insert(Box::new([1, 2, 3]), 'a');
    /// map.prefix_insert(Box::new([2, 3, 4, 5]), 'b');
    /// map.prefix_insert(Box::new([2, 3, 4, 6]), 'b');
    /// // [2, 3, 4, 5] and [2, 3, 4, 6] are removed and ([2, 3, 4], 'c') is inserted.
    /// map.prefix_insert(Box::new([2, 3, 4]), 'c');
    /// assert!(map.get([2, 3, 4, 5].as_ref()).is_none());
    /// assert!(map.get([2, 3, 4, 6].as_ref()).is_none());
    /// // ([1, 2, 3], 'a') is replaced by ([1, 2], 'd')
    /// map.prefix_insert(Box::new([1, 2]), 'd');
    /// assert!(map.get([1, 2, 3].as_ref()).is_none());
    /// assert_eq!(map.get([1, 2].as_ref()), Some(&'d'));
    ///
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn prefix_insert(&mut self, key: K, value: V)
    where
        K: AsBytes,
    {
        if let Some(state) = &self.state {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            // The same allocator is used for all inserts and deletes
            let _ = unsafe {
                let insert_point = search_for_prefix_insert_point(state.root, key.as_bytes());
                self.apply_prefix_insert_point(insert_point, key, value)
            };
        } else {
            self.init_tree(key, value);
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
        if let Some(state) = &self.state {
            // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
            // that there are no other references (mutable or immutable) to this same
            // object. Meaning that our access to the root node is unique and there are no
            // other accesses to any node in the tree.
            let delete_point = unsafe { search_for_delete_point(state.root, key.as_bytes())? };
            // SAFETY: There are no outstanding pointers (besides leaf min/max which are
            // already fixed by `apply_delete_pointer`).
            let delete_result = unsafe { self.apply_delete_point(delete_point) };
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

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)`
    /// returns `false`. The elements are visited in ascending key order.
    ///
    /// # Examples
    ///
    /// ```
    /// use blart::TreeMap;
    ///
    /// let mut map: TreeMap<i32, i32> = (0..8).map(|x| (x, x*10)).collect();
    /// // Keep only the elements with even-numbered keys.
    /// map.retain(|&k, _| k % 2 == 0);
    /// assert!(map.into_iter().eq(vec![(0, 0), (2, 20), (4, 40), (6, 60)]));
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
        K: AsBytes,
    {
        self.extract_if(.., |k, v| !f(k, v)).for_each(drop);
    }

    /// Moves all elements from other into self, leaving other empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut a = TreeMap::<u128, _>::new();
    /// a.try_insert(1, "a").unwrap();
    /// a.try_insert(2, "b").unwrap();
    /// a.try_insert(3, "c").unwrap(); // Note: Key (3) also present in b.
    ///
    /// let mut b = TreeMap::<u128, _>::new();
    /// b.try_insert(3, "d").unwrap(); // Note: Key (3) also present in a.
    /// b.try_insert(4, "e").unwrap();
    /// b.try_insert(5, "f").unwrap();
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.len(), 5);
    /// assert_eq!(b.len(), 0);
    ///
    /// assert_eq!(a[&1], "a");
    /// assert_eq!(a[&2], "b");
    /// assert_eq!(a[&3], "d"); // Note: "c" has been overwritten.
    /// assert_eq!(a[&4], "e");
    /// assert_eq!(a[&5], "f");
    /// ```
    pub fn append(&mut self, other: &mut Self)
    where
        K: NoPrefixesBytes,
    {
        if other.is_empty() {
            return;
        }

        if self.is_empty() {
            mem::swap(self, other);
            return;
        }

        self.extend(other.extract_if(.., |_, _| true))
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the
    /// map.
    ///
    /// The simplest way is to use the range syntax `min..max`, thus
    /// `range(min..max)` will yield elements from min (inclusive) to max
    /// (exclusive). The range may also be entered as `(Bound<T>, Bound<T>)`, so
    /// for example `range((Excluded(4), Included(10)))` will yield a
    /// left-exclusive, right-inclusive range from 4 to 10.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    /// use std::ops::Bound::Included;
    ///
    /// let mut map = TreeMap::<u8, _>::new();
    /// map.try_insert(3, "a").unwrap();
    /// map.try_insert(5, "b").unwrap();
    /// map.try_insert(8, "c").unwrap();
    ///
    /// for (key, &value) in map.range((Included(&4), Included(&8))) {
    ///     println!("{key:?}: {value}");
    /// }
    /// assert_eq!(map.range(&4..).next(), Some((&5, &"b")));
    /// ```
    pub fn range<Q, R>(&self, range: R) -> iterators::Range<'_, K, V, PREFIX_LEN, A>
    where
        Q: AsBytes + ?Sized,
        K: Borrow<Q> + AsBytes,
        R: RangeBounds<Q>,
    {
        iterators::Range::new(
            self,
            range.start_bound().map(AsBytes::as_bytes),
            range.end_bound().map(AsBytes::as_bytes),
        )
    }

    /// Constructs a mutable double-ended iterator over a sub-range of elements
    /// in the map.
    ///
    /// The simplest way is to use the range syntax `min..max`, thus
    /// `range_mut(min..max)` will yield elements from min (inclusive) to max
    /// (exclusive). The range may also be entered as `(Bound<T>, Bound<T>)`, so
    /// for example `range_mut((Excluded(4), Included(10)))` will yield a
    /// left-exclusive, right-inclusive range from 4 to 10.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut map: TreeMap<_, i32> = TreeMap::new();
    ///
    /// for (key, value) in [("Alice", 0), ("Bob", 0), ("Carol", 0), ("Cheryl", 0)] {
    ///     let _ = map.try_insert(key, value).unwrap();
    /// }
    ///
    /// for (name, balance) in map.range_mut("B"..="Cheryl") {
    ///     *balance += 100;
    ///
    ///     if name.starts_with('C') {
    ///         *balance *= 2;
    ///     }
    /// }
    ///
    /// for (name, balance) in &map {
    ///     println!("{name} => {balance}");
    /// }
    ///
    /// assert_eq!(map["Alice"], 0);
    /// assert_eq!(map["Bob"], 100);
    /// assert_eq!(map["Carol"], 200);
    /// assert_eq!(map["Cheryl"], 200);
    /// ```
    pub fn range_mut<Q, R>(&mut self, range: R) -> iterators::RangeMut<'_, K, V, PREFIX_LEN, A>
    where
        Q: AsBytes + ?Sized,
        K: Borrow<Q> + AsBytes,
        R: RangeBounds<Q>,
    {
        iterators::RangeMut::new(
            self,
            range.start_bound().map(AsBytes::as_bytes),
            range.end_bound().map(AsBytes::as_bytes),
        )
    }

    /// Splits the collection into two at the given key. Returns everything
    /// after the given key, including the key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use blart::TreeMap;
    ///
    /// let mut a = TreeMap::new();
    /// a.try_insert(1, "a").unwrap();
    /// a.try_insert(2, "b").unwrap();
    /// a.try_insert(3, "c").unwrap();
    /// a.try_insert(17, "d").unwrap();
    /// a.try_insert(41, "e").unwrap();
    ///
    /// let b = a.split_off(&3);
    ///
    /// assert_eq!(a.len(), 2);
    /// assert_eq!(b.len(), 3);
    ///
    /// assert_eq!(a[&1], "a");
    /// assert_eq!(a[&2], "b");
    ///
    /// assert_eq!(b[&3], "c");
    /// assert_eq!(b[&17], "d");
    /// assert_eq!(b[&41], "e");
    /// ```
    pub fn split_off<Q>(&mut self, split_key: &Q) -> TreeMap<K, V, PREFIX_LEN, A>
    where
        K: Borrow<Q> + AsBytes,
        Q: AsBytes + ?Sized,
        A: Clone,
    {
        // TODO(opt): Optimize this by doing a tree search to find split point and then
        // cutting the tree. This should save time versus reconstructing a whole new
        // tree

        let mut new_tree = TreeMap::with_prefix_len_in(self.alloc.clone());

        for (key, value) in
            self.extract_if(.., |key, _| split_key.as_bytes() <= key.borrow().as_bytes())
        {
            // PANIC SAFETY: This will not panic because the property of any existing tree
            // containing no keys that are prefixes of any other key holds when the tree is
            // split into any portion.
            let _ = new_tree.try_insert(key, value).unwrap();
        }

        new_tree
    }

    /// Creates an iterator that visits elements (key-value pairs) in the
    /// specified range in ascending key order and uses a closure to
    /// determine if an element should be removed.
    ///
    /// If the closure returns `true`, the element is removed from the map and
    /// yielded. If the closure returns `false`, or panics, the element remains
    /// in the map and will not be yielded.
    ///
    /// The iterator also lets you mutate the value of each element in the
    /// closure, regardless of whether you choose to keep or remove it.
    ///
    /// If the returned `ExtractIf` is not exhausted, e.g. because it is dropped
    /// without iterating or the iteration short-circuits, then the
    /// remaining elements will be retained. Use [`retain`] with a negated
    /// predicate if you do not need the returned iterator.
    ///
    /// [`retain`]: TreeMap::retain
    ///
    /// # Examples
    ///
    /// ```
    /// use blart::TreeMap;
    ///
    /// // Splitting a map into even and odd keys, reusing the original map:
    /// let mut map: TreeMap<u8, u8> = (0..8).map(|x| (x, x)).collect();
    /// let evens: TreeMap<_, _> = map.extract_if(.., |k, _v| k % 2 == 0).collect();
    /// let odds = map;
    /// assert_eq!(evens.keys().copied().collect::<Vec<_>>(), [0, 2, 4, 6]);
    /// assert_eq!(odds.keys().copied().collect::<Vec<_>>(), [1, 3, 5, 7]);
    ///
    /// // Splitting a map into low and high halves, reusing the original map:
    /// let mut map: TreeMap<u8, u8> = (0..8).map(|x| (x, x)).collect();
    /// let low: TreeMap<_, _> = map.extract_if(0..4, |_k, _v| true).collect();
    /// let high = map;
    /// assert_eq!(low.keys().copied().collect::<Vec<_>>(), [0, 1, 2, 3]);
    /// assert_eq!(high.keys().copied().collect::<Vec<_>>(), [4, 5, 6, 7]);
    /// ```
    pub fn extract_if<R, F>(&mut self, range: R, pred: F) -> ExtractIf<'_, K, V, F, PREFIX_LEN, A>
    where
        K: AsBytes,
        R: RangeBounds<K>,
        F: FnMut(&K, &mut V) -> bool,
    {
        ExtractIf::new(
            self,
            range.start_bound().map(AsBytes::as_bytes),
            range.end_bound().map(AsBytes::as_bytes),
            pred,
        )
    }

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
    pub fn into_keys(self) -> iterators::IntoKeys<K, V, PREFIX_LEN, A> {
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
    pub fn into_values(self) -> iterators::IntoValues<K, V, PREFIX_LEN, A> {
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
    pub fn iter(&self) -> Iter<'_, K, V, PREFIX_LEN, A> {
        Iter::new(self)
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
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V, PREFIX_LEN, A> {
        IterMut::new(self)
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
    pub fn keys(&self) -> Keys<'_, K, V, PREFIX_LEN, A> {
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
    pub fn values(&self) -> Values<'_, K, V, PREFIX_LEN, A> {
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
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, PREFIX_LEN, A> {
        ValuesMut::new(self)
    }

    /// Gets an iterator over the entries of the map that start with `prefix`
    ///
    /// # Examples
    ///
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
    pub fn prefix(&self, prefix: &[u8]) -> Prefix<'_, K, V, PREFIX_LEN, A>
    where
        K: AsBytes,
    {
        Prefix::new(self, prefix)
    }

    /// Gets a mutable iterator over the entries of the map that start with
    /// `prefix`
    ///
    /// # Examples
    ///
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
    pub fn prefix_mut(&mut self, prefix: &[u8]) -> PrefixMut<'_, K, V, PREFIX_LEN, A>
    where
        K: AsBytes,
    {
        PrefixMut::new(self, prefix)
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

impl<K, V, const PREFIX_LEN: usize, A: Allocator> TreeMap<K, V, PREFIX_LEN, A> {
    /// Tries to get the given key’s corresponding entry in the map for in-place
    /// manipulation.
    pub fn try_entry(&mut self, key: K) -> Result<Entry<'_, K, V, PREFIX_LEN, A>, InsertPrefixError>
    where
        K: AsBytes,
    {
        let entry = match &self.state {
            Some(state) => {
                // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
                // that there are no other references (mutable or immutable) to this same
                // object. Meaning that our access to the root node is unique and there are no
                // other accesses to any node in the tree.
                let insert_point = unsafe { search_for_insert_point(state.root, key.as_bytes())? };
                match insert_point.insert_kind {
                    InsertKind::Exact { leaf_node_ptr } => Entry::Occupied(OccupiedEntry {
                        map: self,
                        delete_point: DeletePoint {
                            path: insert_point.path,
                            leaf_node_ptr,
                        },
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

    /// Tries to get the given key’s corresponding prefix entry in the map for
    /// in-place manipulation.
    ///
    /// This entry represents an unfinished [prefix_insert](Self::prefix_insert)
    /// operation. Compared to [Entry], it has one extra occupied state
    /// called [InnerOccupiedEntry]. This entry represents the
    /// `prefix_insert` case were the exact key was not found, but a prefix
    /// of the given key or vice versa was found.
    ///
    /// See also: [Self::try_entry].
    ///
    /// # Examples
    ///
    /// ```
    /// use blart::{TreeMap, map::{PrefixEntry, PrefixOccupied}};
    /// let mut tree = TreeMap::new();
    /// tree.try_insert("Hello from Germany", 1).unwrap();
    /// tree.try_insert("Hello from France", 1).unwrap();
    /// tree.try_insert("Hello from Belgium", 1).unwrap();
    /// tree.try_insert("Anyone on Mars?", 3).unwrap();
    /// let PrefixEntry::Occupied(PrefixOccupied::Inner(inner)) =
    ///     tree.prefix_entry("Hello from")
    /// else {
    ///     unreachable!()
    /// };
    /// // We can iterate over all keys that would be overwritten if we inserted into this entry.
    /// let mut inner_iter = inner.iter();
    /// assert_eq!(inner_iter.next(), Some((&"Hello from Belgium", &1)));
    /// assert_eq!(inner_iter.next(), Some((&"Hello from France", &1)));
    /// assert_eq!(inner_iter.next(), Some((&"Hello from Germany", &1)));
    /// assert_eq!(inner_iter.next(), None);
    /// inner.insert(2);
    /// assert_eq!(tree.len(), 2);
    /// ```
    pub fn prefix_entry(&mut self, key: K) -> PrefixEntry<'_, K, V, PREFIX_LEN, A>
    where
        K: AsBytes,
    {
        match &self.state {
            Some(state) => {
                // SAFETY: Since we have a mutable reference to the `TreeMap`, we are guaranteed
                // that there are no other references (mutable or immutable) to this same
                // object. Meaning that our access to the root node is unique and there are no
                // other accesses to any node in the tree.
                let insert_point =
                    unsafe { search_for_prefix_insert_point(state.root, key.as_bytes()) };
                match insert_point {
                    PrefixInsertPoint::OverwritePoint(overwrite_point) => {
                        PrefixEntry::Occupied(PrefixOccupied::Inner(InnerOccupiedEntry {
                            map: self,
                            key,
                            overwrite_point,
                        }))
                    },
                    PrefixInsertPoint::InsertPoint(insert_point) => {
                        match insert_point.insert_kind {
                            InsertKind::Exact { leaf_node_ptr } => {
                                PrefixEntry::Occupied(PrefixOccupied::Leaf(OccupiedEntry {
                                    map: self,
                                    delete_point: DeletePoint {
                                        path: insert_point.path,
                                        leaf_node_ptr,
                                    },
                                }))
                            },
                            _ => PrefixEntry::Vacant(VacantEntry {
                                key,
                                insert_point: Some(insert_point),
                                map: self,
                            }),
                        }
                    },
                }
            },
            None => PrefixEntry::Vacant(VacantEntry {
                key,
                insert_point: None,
                map: self,
            }),
        }
    }

    /// Gets the given key’s corresponding entry in the map for in-place
    /// manipulation.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, PREFIX_LEN, A>
    where
        K: NoPrefixesBytes,
    {
        // This will never fail because of the safety contract of `NoPrefixesBytes`
        unsafe { self.try_entry(key).unwrap_unchecked() }
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> Drop for TreeMap<K, V, PREFIX_LEN, A> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<K, V, A, const PREFIX_LEN: usize> Clone for TreeMap<K, V, PREFIX_LEN, A>
where
    K: Clone + AsBytes,
    V: Clone,
    A: Allocator + Clone,
{
    fn clone(&self) -> Self {
        match &self.state {
            Some(state) => {
                let CloneResult {
                    root,
                    min_leaf,
                    max_leaf,
                } = unsafe { clone_unchecked(state.root, &self.alloc) };

                TreeMap {
                    num_entries: self.num_entries,
                    state: Some(NonEmptyTree {
                        root,
                        min_leaf,
                        max_leaf,
                    }),
                    alloc: self.alloc.clone(),
                }
            },
            None => TreeMap {
                num_entries: 0,
                state: None,
                alloc: self.alloc.clone(),
            },
        }
    }
}

impl<K, V, A, const PREFIX_LEN: usize> Debug for TreeMap<K, V, PREFIX_LEN, A>
where
    K: Debug,
    V: Debug,
    A: Allocator,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, const PREFIX_LEN: usize> Default for TreeMap<K, V, PREFIX_LEN> {
    fn default() -> Self {
        Self::with_prefix_len()
    }
}

impl<'a, K, V, A, const PREFIX_LEN: usize> Extend<(&'a K, &'a V)> for TreeMap<K, V, PREFIX_LEN, A>
where
    K: Copy + NoPrefixesBytes,
    V: Copy,
    A: Allocator,
{
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            let _ = self.insert(*key, *value);
        }
    }
}

impl<K, V, A, const PREFIX_LEN: usize> Extend<(K, V)> for TreeMap<K, V, PREFIX_LEN, A>
where
    K: NoPrefixesBytes,
    A: Allocator,
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

impl<K, V, const PREFIX_LEN: usize> From<Vec<(K, V)>> for TreeMap<K, V, PREFIX_LEN>
where
    K: NoPrefixesBytes,
{
    fn from(arr: Vec<(K, V)>) -> Self {
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

impl<K, V, A, const PREFIX_LEN: usize> Hash for TreeMap<K, V, PREFIX_LEN, A>
where
    K: Hash,
    V: Hash,
    A: Allocator,
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        hasher_write_length_prefix(state, self.num_entries);
        for elt in self {
            elt.hash(state);
        }
    }
}

impl<Q, K, V, A, const PREFIX_LEN: usize> Index<&Q> for TreeMap<K, V, PREFIX_LEN, A>
where
    K: Borrow<Q> + AsBytes,
    Q: AsBytes + ?Sized,
    A: Allocator,
{
    type Output = V;

    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> IntoIterator
    for &'a TreeMap<K, V, PREFIX_LEN, A>
{
    type IntoIter = Iter<'a, K, V, PREFIX_LEN, A>;
    type Item = (&'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> IntoIterator
    for &'a mut TreeMap<K, V, PREFIX_LEN, A>
{
    type IntoIter = IterMut<'a, K, V, PREFIX_LEN, A>;
    type Item = (&'a K, &'a mut V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> IntoIterator for TreeMap<K, V, PREFIX_LEN, A> {
    type IntoIter = iterators::IntoIter<K, V, PREFIX_LEN, A>;
    type Item = (K, V);

    fn into_iter(self) -> Self::IntoIter {
        iterators::IntoIter::new(self)
    }
}

impl<K, V, A, const PREFIX_LEN: usize> Ord for TreeMap<K, V, PREFIX_LEN, A>
where
    K: Ord,
    V: Ord,
    A: Allocator,
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<K, V, A, const PREFIX_LEN: usize> PartialOrd for TreeMap<K, V, PREFIX_LEN, A>
where
    K: PartialOrd,
    V: PartialOrd,
    A: Allocator,
{
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K, V, A, const PREFIX_LEN: usize> Eq for TreeMap<K, V, PREFIX_LEN, A>
where
    K: Eq,
    V: Eq,
    A: Allocator,
{
}

impl<K, V, A, const PREFIX_LEN: usize> PartialEq for TreeMap<K, V, PREFIX_LEN, A>
where
    K: PartialEq,
    V: PartialEq,
    A: Allocator,
{
    fn eq(&self, other: &Self) -> bool {
        self.num_entries == other.num_entries && self.iter().eq(other.iter())
    }
}

// SAFETY: This is safe to implement if `K` and `V` are also `Send`.
// This container is safe to `Send` for the same reasons why other container
// are also safe
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for TreeMap<K, V, PREFIX_LEN, A>
where
    K: Send,
    V: Send,
    A: Send + Allocator,
{
}

// SAFETY: This is safe to implement if `K` and `V` are also `Sync`.
// This container is safe to `Sync` for the same reasons why other container
// are also safe
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for TreeMap<K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

#[cfg(test)]
mod tests {
    use crate::{
        tests_common::{
            generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, swap,
            PrefixExpansion,
        },
        TreeMap,
    };
    use alloc::{boxed::Box, string::String, vec::Vec};
    use core::cmp::Ordering;

    use super::*;

    #[test]
    fn tree_map_is_send_sync_unwind_safe() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}
        fn is_unwind_safe<T: UnwindSafe>() {}

        fn map_is_send<K: Send, V: Send>() {
            is_send::<TreeMap<K, V>>();
        }

        fn map_is_sync<K: Sync, V: Sync>() {
            is_sync::<TreeMap<K, V>>();
        }

        fn map_is_unwind_safe<K: UnwindSafe, V: UnwindSafe>() {
            is_unwind_safe::<TreeMap<K, V>>();
        }

        map_is_send::<[u8; 3], usize>();
        map_is_sync::<[u8; 3], usize>();
        map_is_unwind_safe::<[u8; 3], usize>();
    }

    #[test]
    fn tree_map_create_empty() {
        let map = TreeMap::<Box<[u8]>, ()>::new();

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn default_tree_map_is_empty() {
        let default = TreeMap::<(), usize, 16>::default();

        assert!(default.is_empty());
        assert_eq!(default.len(), 0);
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
        assert_eq!(map_a.partial_cmp(&map_a), Some(Ordering::Equal));
        assert_eq!(map_a.cmp(&map_b), Ordering::Less);
        assert_eq!(map_a.partial_cmp(&map_b), Some(Ordering::Less));
        assert_eq!(map_a.cmp(&map_c), Ordering::Greater);
        assert_eq!(map_a.partial_cmp(&map_c), Some(Ordering::Greater));
        assert_eq!(map_a.cmp(&map_d), Ordering::Less);
        assert_eq!(map_a.partial_cmp(&map_d), Some(Ordering::Less));

        assert_eq!(map_b.cmp(&map_a), Ordering::Greater);
        assert_eq!(map_b.partial_cmp(&map_a), Some(Ordering::Greater));
        assert_eq!(map_b.cmp(&map_b), Ordering::Equal);
        assert_eq!(map_b.partial_cmp(&map_b), Some(Ordering::Equal));
        assert_eq!(map_b.cmp(&map_c), Ordering::Greater);
        assert_eq!(map_b.partial_cmp(&map_c), Some(Ordering::Greater));
        assert_eq!(map_b.cmp(&map_d), Ordering::Equal);
        assert_eq!(map_b.partial_cmp(&map_d), Some(Ordering::Equal));

        assert_eq!(map_c.cmp(&map_a), Ordering::Less);
        assert_eq!(map_c.partial_cmp(&map_a), Some(Ordering::Less));
        assert_eq!(map_c.cmp(&map_b), Ordering::Less);
        assert_eq!(map_c.partial_cmp(&map_b), Some(Ordering::Less));
        assert_eq!(map_c.cmp(&map_c), Ordering::Equal);
        assert_eq!(map_c.partial_cmp(&map_c), Some(Ordering::Equal));
        assert_eq!(map_c.cmp(&map_d), Ordering::Less);
        assert_eq!(map_c.partial_cmp(&map_d), Some(Ordering::Less));

        assert_eq!(map_d.cmp(&map_a), Ordering::Greater);
        assert_eq!(map_d.partial_cmp(&map_a), Some(Ordering::Greater));
        assert_eq!(map_d.cmp(&map_b), Ordering::Equal);
        assert_eq!(map_d.partial_cmp(&map_b), Some(Ordering::Equal));
        assert_eq!(map_d.cmp(&map_c), Ordering::Greater);
        assert_eq!(map_d.partial_cmp(&map_c), Some(Ordering::Greater));
        assert_eq!(map_d.cmp(&map_d), Ordering::Equal);
        assert_eq!(map_d.partial_cmp(&map_d), Some(Ordering::Equal));
    }

    #[cfg(feature = "std")]
    #[test]
    fn tree_hash_equals() {
        use core::hash::BuildHasher;
        let mut tree_a = TreeMap::<[u8; 0], i32>::new();

        let _ = tree_a.try_insert([], 0);
        let _ = tree_a.pop_first();

        let tree_b = tree_a.clone();

        let hasher_builder = std::hash::RandomState::new();

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
        assert!(!tree.is_empty());

        // insert to existing leaf, should replace the key and value, and not change the
        // length
        assert_eq!(tree.try_insert(Box::new([1]), 1), Ok(Some(0)));

        assert_eq!(tree.len(), 1);
        assert!(!tree.is_empty());

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
    fn clone_tree_skewed() {
        let mut tree: TreeMap<Box<[u8]>, usize> = TreeMap::new();
        for (v, k) in
            generate_keys_skewed(if cfg!(miri) { 64 } else { u8::MAX as usize }).enumerate()
        {
            tree.try_insert(k, v).unwrap();
        }
        let new_tree = tree.clone();
        assert!(tree == new_tree);
    }

    #[test]
    fn clone_tree_fixed_length() {
        const KEY_DEPTH: usize = if cfg!(miri) { 4 } else { 8 };
        let mut tree: TreeMap<_, usize> = TreeMap::new();
        for (v, k) in generate_key_fixed_length([2; KEY_DEPTH]).enumerate() {
            tree.try_insert(k, v).unwrap();
        }
        let new_tree = tree.clone();
        assert!(tree == new_tree);
    }

    #[test]
    fn clone_tree_with_prefix() {
        const KEY_DEPTH: usize = if cfg!(miri) { 4 } else { 8 };
        let mut tree: TreeMap<Box<[u8]>, usize> = TreeMap::new();
        for (v, k) in generate_key_with_prefix(
            [2; KEY_DEPTH],
            [
                PrefixExpansion {
                    base_index: 1,
                    expanded_length: if cfg!(miri) { 3 } else { 12 },
                },
                PrefixExpansion {
                    base_index: 3,
                    expanded_length: if cfg!(miri) { 2 } else { 8 },
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

    #[test]
    fn tree_map_contains_key_false() {
        let mut map: TreeMap<Box<[u8]>, i32> = TreeMap::new();
        map.try_insert(Box::from(*b"foo"), 1).unwrap();
        assert!(!map.contains_key(b"bar" as &[u8]));
    }

    #[test]
    fn tree_map_extend_and_from() {
        let mut map = TreeMap::<[u8; 4], i32>::new();
        let data = vec![([0; 4], 1i32), ([1; 4], 2)];

        // Test extending from an iterator of references
        // The `.map(...)` call looks like identity, but its actually taking `&([u8; 4],
        // i32)` and turning it into `(&[u8; 4], &i32)`
        map.extend(data.iter().map(|(k, v)| (k, v)));
        assert_eq!(map.len(), 2);

        // Test `FromIterator`
        let map2 = TreeMap::<[u8; 4], i32>::from_iter(data.clone());
        assert_eq!(map, map2);

        // Test `From` an array
        let map3 = TreeMap::<[u8; 4], i32>::from([([0; 4], 1), ([1; 4], 2)]);
        assert_eq!(map, map3);

        // Test extending from an iterator of owned values
        let mut map4 = TreeMap::<[u8; 4], i32>::new();
        map4.extend(data);
        assert_eq!(map, map4);
    }

    #[cfg(feature = "std")]
    #[test]
    fn tree_map_hash_ne() {
        use std::collections::HashSet;

        let map1 = TreeMap::<[u8; 4], i32>::from_iter(vec![([0; 4], 1)]);
        let map2 = TreeMap::<[u8; 4], i32>::from_iter(vec![([1; 4], 2)]);

        let mut set = HashSet::new();
        set.insert(map1);
        set.insert(map2);

        assert_eq!(set.len(), 2);
    }

    #[test]
    fn tree_map_partial_eq_different_values() {
        let map1 = TreeMap::<[u8; 4], i32>::from_iter(vec![([0; 4], 1), ([1; 4], 2)]);
        let map2 = TreeMap::<[u8; 4], i32>::from_iter(vec![([0; 4], 3), ([1; 4], 4)]);
        assert_ne!(map1, map2);
    }

    #[test]
    fn test_get_prefix() {
        let mut map = TreeMap::<Box<[u8]>, char>::new();

        map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
        assert_eq!(*map.prefix_get([1, 2, 3, 4, 5].as_ref()).unwrap(), 'a');
    }

    #[test]
    fn test_get_prefix_key_value() {
        let mut map = TreeMap::<Box<[u8]>, char>::new();

        map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
        assert_eq!(
            map.prefix_get_key_value([1, 2, 3, 4, 5].as_ref())
                .map(|(k, v)| (k.as_ref(), v)),
            Some(([1, 2, 3].as_ref(), &'a'))
        );
    }

    #[test]
    fn test_get_prefix_mut() {
        let mut map = TreeMap::<Box<[u8]>, char>::new();

        map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();

        *map.prefix_get_mut([1, 2, 3, 4].as_ref()).unwrap() = 'b';
        assert_eq!(map[[1, 2, 3].as_ref()], 'b');
    }

    #[test]
    fn test_prefix_insert() {
        let mut map = TreeMap::<Box<[u8]>, char>::new();

        map.prefix_insert(Box::new([1, 2, 3]), 'a');
        map.prefix_insert(Box::new([2, 3, 4, 5]), 'b');
        map.prefix_insert(Box::new([2, 3, 4, 6]), 'b');
        map.prefix_insert(Box::new([2, 3, 4]), 'c');
        assert!(map.get([2, 3, 4, 5].as_ref()).is_none());
        assert!(map.get([2, 3, 4, 6].as_ref()).is_none());
        map.prefix_insert(Box::new([1, 2]), 'd');
        assert!(map.get([1, 2, 3].as_ref()).is_none());
        assert_eq!(map.get([1, 2].as_ref()), Some(&'d'));

        assert_eq!(map.len(), 2);
    }

    #[test]
    fn test_empty_key_get_prefix() {
        let mut map = TreeMap::<Box<[u8]>, char>::new();

        map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
        map.try_insert(Box::new([2, 3, 4, 5]), 'b').unwrap();
        map.try_insert(Box::new([2, 3, 4, 6]), 'b').unwrap();
        assert!(map.prefix_get([].as_ref()).is_none());
    }

    #[test]
    fn test_prefix_insert_resize_inner() {
        let mut map = TreeMap::<Box<[u8]>, char>::new();

        map.try_insert(Box::new([1, 2, 3]), 'a').unwrap();
        map.try_insert(Box::new([1, 2, 4]), 'b').unwrap();
        map.try_insert(Box::new([1, 2, 5]), 'b').unwrap();
        map.try_insert(Box::new([1, 2, 6]), 'b').unwrap();
        map.prefix_insert(Box::new([1, 2, 7]), 'b');
        assert!(map.len() == 5);
    }

    #[test]
    fn tree_map_retain_partial() {
        let mut map: TreeMap<_, _> = generate_key_fixed_length([15, 3])
            .enumerate()
            .map(swap)
            .collect();

        assert_eq!(map.len(), 64);
        map.retain(|k, _| k[1] % 3 == 1);
        assert_eq!(map.len(), 16);
    }

    #[cfg(feature = "std")]
    #[test]
    fn tree_map_retain_interrupted() {
        let map: TreeMap<_, _> = generate_key_fixed_length([15, 3])
            .enumerate()
            .map(swap)
            .collect();

        assert_eq!(map.len(), 64);
        let map = std::sync::Mutex::new(map);
        let res = std::panic::catch_unwind(|| {
            let mut map = map.lock().unwrap();
            map.retain(|_, v| if *v == 32 { panic!("stop") } else { false })
        });
        assert!(res.is_err());
        assert!(map.is_poisoned());
        // We know in this case that the map should be fine after the panic
        map.clear_poison();
        let map = map.into_inner().unwrap();
        assert!(map.into_values().eq(32..64));
    }

    #[cfg(feature = "std")]
    #[test]
    fn regression_e8d5a0b988d1f1e0b49f8d6e22354d49539bcf6a() {
        // [
        //     TryInsertMany(
        //         [],
        //         159,
        //     ),
        //     Retain(
        //         All,
        //     ),
        // ]

        let mut tree = TreeMap::new();

        for suffix in 0..=159 {
            tree.insert([suffix], suffix);
        }

        tree.retain(|_, _| true);

        assert_eq!(tree.len(), 160);

        let _ = crate::visitor::WellFormedChecker::check(&tree).unwrap();
    }

    #[test]
    fn tree_map_append_no_overlap() {
        let mut map1 = TreeMap::<[u8; 4], i32>::from_iter([([0; 4], 1), ([1; 4], 2)]);
        let mut map2 = TreeMap::<[u8; 4], i32>::from_iter([([2; 4], 3), ([3; 4], 4)]);

        map1.append(&mut map2);
        assert_eq!(
            map1.into_iter().collect::<Vec<_>>(),
            vec![([0; 4], 1), ([1; 4], 2), ([2; 4], 3), ([3; 4], 4)]
        );
        assert!(map2.is_empty());
    }

    #[test]
    fn tree_map_append_overlap() {
        let mut map1 = TreeMap::<[u8; 4], i32>::from_iter([([0; 4], 1), ([1; 4], 2)]);
        let mut map2 = TreeMap::<[u8; 4], i32>::from_iter([([1; 4], 20), ([2; 4], 3)]);

        map1.append(&mut map2);
        assert_eq!(
            map1.into_iter().collect::<Vec<_>>(),
            vec![([0; 4], 1), ([1; 4], 20), ([2; 4], 3)]
        );
        assert!(map2.is_empty());
    }

    #[test]
    fn tree_map_append_empty_cases() {
        let mut non_empty_map = TreeMap::<[u8; 4], i32>::from_iter([([0; 4], 1), ([1; 4], 2)]);
        let mut empty_map = TreeMap::new();

        assert!(empty_map.is_empty());
        assert_eq!(non_empty_map.len(), 2);

        non_empty_map.append(&mut empty_map);

        assert!(empty_map.is_empty());
        assert_eq!(non_empty_map.len(), 2);

        empty_map.append(&mut non_empty_map);

        assert_eq!(empty_map.len(), 2);
        assert!(non_empty_map.is_empty());
    }

    #[test]
    fn tree_map_split_off_existing_key() {
        let mut map: TreeMap<_, _> = generate_key_fixed_length([15, 3])
            .enumerate()
            .map(swap)
            .collect();

        let after = map.split_off(&[8, 0]);

        assert_eq!(map.len(), 32);
        assert_eq!(after.len(), 32);

        assert!(map.into_values().eq(0..32));
        assert!(after.into_values().eq(32..64));
    }

    #[test]
    fn tree_map_split_off_nonexisting_key() {
        let mut map: TreeMap<_, _> = generate_key_fixed_length([15, 3])
            .enumerate()
            .map(swap)
            .collect();
        assert_eq!(map.remove(&[8, 0]).unwrap(), 32);

        let after = map.split_off(&[8, 0]);

        assert_eq!(map.len(), 32);
        assert_eq!(after.len(), 31);

        assert!(map.into_values().eq(0..32));
        assert!(after.into_values().eq(33..64));
    }

    #[test]
    fn tree_map_split_off_edges() {
        let mut map: TreeMap<_, _> = generate_key_fixed_length([15, 3])
            .enumerate()
            .map(swap)
            .collect();

        // First key
        let mut split_all = map.split_off(&[0, 0]);

        assert!(map.is_empty());
        assert_eq!(split_all.len(), 64);
        assert!(split_all.values().copied().eq(0..64));

        // One after the last key
        let split_none = split_all.split_off(&[15, 4]);

        assert_eq!(split_all.len(), 64);
        assert!(split_none.is_empty());
        assert!(split_all.values().copied().eq(0..64));
    }

    #[test]
    fn tree_map_from_vec() {
        let entries: Vec<_> = [c"abc", c"hello", c"", c"my name is"]
            .into_iter()
            .enumerate()
            .map(swap)
            .collect();

        let map = TreeMap::<_, _, 16>::from(entries);

        assert_eq!(*map.get(c"abc").unwrap(), 0);
        assert_eq!(*map.get(c"hello").unwrap(), 1);
        assert_eq!(*map.get(c"").unwrap(), 2);
        assert_eq!(*map.get(c"my name is").unwrap(), 3);
    }
}

#[cfg(all(test, any(feature = "allocator-api2", feature = "nightly")))]
#[cfg_attr(test, mutants::skip)]
mod custom_allocator_tests {
    use super::*;

    use crate::{
        allocator::AllocError,
        rust_nightly_apis::ptr::{nonnull_addr, nonnull_with_addr},
    };
    use alloc::boxed::Box;

    use core::{
        alloc::Layout,
        cell::{Cell, UnsafeCell},
        marker::PhantomPinned,
        mem::MaybeUninit,
        num::NonZeroUsize,
        pin::Pin,
        ptr::{addr_of_mut, NonNull},
    };

    struct BumpAllocator<const N: usize> {
        block: UnsafeCell<MaybeUninit<[u8; N]>>,

        // Points to start of block
        start: Cell<NonNull<u8>>,
        // Points to end of block
        end: Cell<NonNull<u8>>,
        // Points somewhere between `start` and `end`, is
        // the end of the next allocation
        ptr: Cell<NonNull<u8>>,

        alloc_count: Cell<usize>,
        dealloc_count: Cell<usize>,

        // Prevent Unpin
        _marker: PhantomPinned,
    }

    impl<const N: usize> BumpAllocator<N> {
        fn new() -> Pin<Box<Self>> {
            let mut alloc = Box::new(Self {
                block: UnsafeCell::new(MaybeUninit::uninit()),

                // These three will be fixed up after allocating the allocator
                start: Cell::new(NonNull::dangling()),
                end: Cell::new(NonNull::dangling()),
                ptr: Cell::new(NonNull::dangling()),

                alloc_count: Cell::new(0),
                dealloc_count: Cell::new(0),

                _marker: PhantomPinned,
            });

            let alloc_start = NonNull::new(addr_of_mut!(alloc.block).cast::<u8>()).unwrap();
            alloc.start.set(alloc_start);
            alloc.end.set(
                NonNull::new(unsafe { alloc_start.as_ptr().offset(N.try_into().unwrap()) })
                    .unwrap(),
            );
            alloc.ptr.set(alloc.end.get());

            Box::into_pin(alloc)
        }
    }

    unsafe impl<const N: usize> Allocator for Pin<Box<BumpAllocator<N>>> {
        #[inline]
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            self.alloc_count.set(self.alloc_count.get() + 1);

            let size = layout.size();
            let align = layout.align();

            debug_assert!(align > 0);
            debug_assert!(align.is_power_of_two());

            let ptr = nonnull_addr(self.ptr.get());

            let new_ptr = ptr.get().checked_sub(size).unwrap();

            // Round down to the requested alignment.
            let new_ptr = NonZeroUsize::new(new_ptr & !(align - 1)).unwrap();

            let start = nonnull_addr(self.start.get());
            if new_ptr < start {
                // Didn't have enough capacity!
                return Err(AllocError);
            }

            self.ptr.set(nonnull_with_addr(self.ptr.get(), new_ptr));
            Ok(NonNull::slice_from_raw_parts(self.ptr.get(), size))
        }

        #[inline]
        unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
            self.dealloc_count.set(self.dealloc_count.get() + 1);
        }
    }

    // Just a simple test to make sure the allocator works as expected outside of
    // the tree
    #[test]
    fn non_tree_allocation() {
        let allocator = BumpAllocator::<64>::new();

        let ptr = allocator.allocate(Layout::new::<[u8; 32]>());
        assert!(ptr.is_ok());
        let ptr = allocator.allocate(Layout::new::<[u8; 32]>());
        assert!(ptr.is_ok());
        let ptr = allocator.allocate(Layout::new::<[u8; 1]>());
        assert!(ptr.is_err());
        let ptr = allocator.allocate(Layout::new::<[u8; 0]>());
        assert!(ptr.is_ok());

        assert_eq!(allocator.alloc_count.get(), 4);
        assert_eq!(allocator.dealloc_count.get(), 0);
    }

    #[test]
    fn small_tree() {
        let allocator = BumpAllocator::<
            {
                core::mem::size_of::<
                    crate::raw::InnerNode4<
                        &core::ffi::CStr,
                        i32,
                        { crate::map::DEFAULT_PREFIX_LEN },
                    >,
                >() + (2 * core::mem::size_of::<
                    crate::raw::LeafNode<&core::ffi::CStr, i32, { crate::map::DEFAULT_PREFIX_LEN }>,
                >())
            },
        >::new();

        let mut tree = TreeMap::new_in(allocator);
        tree.insert(c"abc", 0);
        tree.insert(c"xyz", 1);
        assert_eq!(tree.get(c"abc").unwrap(), &0);
        assert_eq!(tree.get(c"xyz").unwrap(), &1);

        let (root, allocator) = TreeMap::into_raw_with_allocator(tree);

        // 1 Node4, 2 LeafNodes
        // assert_eq!(allocator.alloc_count.get(), 3);
        // assert_eq!(allocator.dealloc_count.get(), 0);

        unsafe {
            deallocate_tree(root.unwrap(), &allocator);
        }

        // Each node alloc and dealloced
        // assert_eq!(allocator.alloc_count.get(), 3);
        // assert_eq!(allocator.dealloc_count.get(), 3);
    }

    struct EmptyAllocator;

    unsafe impl Allocator for EmptyAllocator {
        #[inline]
        fn allocate(&self, _layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            Err(AllocError)
        }

        #[inline]
        unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
    }

    #[test]
    #[should_panic(expected = "memory is infinite")]
    fn out_of_memory() {
        let mut tree = TreeMap::new_in(EmptyAllocator);
        tree.insert(c"abc", 0);
    }
}
