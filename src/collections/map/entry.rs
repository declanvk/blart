use std::mem::replace;

use crate::{
    alloc::{Allocator, Global},
    raw::{DeletePoint, InsertParentNodeChange, InsertPoint, InsertResult, TreePath},
    AsBytes, TreeMap,
};

use super::DEFAULT_PREFIX_LEN;

/// A view into an occupied entry in a [`TreeMap`]. It is part of the [`Entry`]
/// enum.
#[derive(Debug)]
pub struct OccupiedEntry<
    'a,
    K,
    V,
    const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN,
    A: Allocator = Global,
> {
    /// Used for the removal
    pub(crate) map: &'a mut TreeMap<K, V, PREFIX_LEN, A>,
    /// The point in the tree that would be removed if requested.
    pub(crate) delete_point: DeletePoint<K, V, PREFIX_LEN>,
}

// SAFETY: This struct contains a `&mut TreeMap<K, V>` which mean `K` and `V`
// must be `Send` for the struct to be `Send`.
unsafe impl<K: Send, V: Send, const PREFIX_LEN: usize, A: Send + Allocator> Send
    for OccupiedEntry<'_, K, V, PREFIX_LEN, A>
{
}

// SAFETY: This type has no interior mutability, and requires all internally
// referenced types to be `Sync` for the whole thing to be `Sync`.
unsafe impl<K: Sync, V: Sync, const PREFIX_LEN: usize, A: Sync + Allocator> Sync
    for OccupiedEntry<'_, K, V, PREFIX_LEN, A>
{
}

impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> OccupiedEntry<'a, K, V, PREFIX_LEN, A>
where
    K: AsBytes,
{
    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a shared reference from this mutable reference
        unsafe { self.delete_point.leaf_node_ptr.as_value_ref() }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the [`OccupiedEntry`] which may outlive the
    /// destruction of the Entry value, see [`OccupiedEntry::into_mut`].
    pub fn get_mut(&mut self) -> &mut V {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a mutable reference from this mutable reference
        unsafe { self.delete_point.leaf_node_ptr.as_value_mut() }
    }

    /// Sets the value of the entry, and returns the entry’s old value.
    pub fn insert(&mut self, value: V) -> V {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a mutable reference from this mutable reference
        let leaf_value = unsafe { self.delete_point.leaf_node_ptr.as_value_mut() };
        replace(leaf_value, value)
    }

    /// Converts the [`OccupiedEntry`] into a mutable reference to the value in
    /// the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the [`OccupiedEntry`], see
    /// [`OccupiedEntry::get_mut`].
    pub fn into_mut(self) -> &'a mut V {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a mutable reference from this mutable reference
        unsafe { self.delete_point.leaf_node_ptr.as_value_mut() }
    }

    /// Gets a reference to the key in the entry.
    pub fn key(&self) -> &K {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a shared reference from this mutable reference
        unsafe { self.delete_point.leaf_node_ptr.as_key_ref() }
    }

    /// Takes the entry out of the map and returns it.
    pub fn remove_entry(self) -> (K, V) {
        // SAFETY: This function call may invalidate the `leaf_node_ptr` and/or
        // `parent_ptr`, but since we take this by value there is no way to access those
        // values afterwards.
        let delete_result = unsafe { self.map.apply_delete_point(self.delete_point) };
        delete_result.deleted_leaf.into_entry()
    }

    /// Takes the value of the entry out of the map, and returns it.
    pub fn remove(self) -> V {
        self.remove_entry().1
    }
}

/// A view into a vacant entry in a [`TreeMap`]. It is part of the [`Entry`]
/// enum.
#[derive(Debug)]
pub struct VacantEntry<'a, K, V, const PREFIX_LEN: usize, A: Allocator> {
    pub(crate) map: &'a mut TreeMap<K, V, PREFIX_LEN, A>,
    pub(crate) key: K,
    pub(crate) insert_point: Option<InsertPoint<K, V, PREFIX_LEN>>,
}

// SAFETY: This struct contains a `&mut TreeMap<K, V>` which mean `K` and `V`
// must be `Send` for the struct to be `Send`.
unsafe impl<K: Send, V: Send, A: Send + Allocator, const PREFIX_LEN: usize> Send
    for VacantEntry<'_, K, V, PREFIX_LEN, A>
{
}

// SAFETY: This type has no interior mutability, and requires all internally
// referenced types to be `Sync` for the whole thing to be `Sync`.
unsafe impl<K: Sync, V: Sync, A: Sync + Allocator, const PREFIX_LEN: usize> Sync
    for VacantEntry<'_, K, V, PREFIX_LEN, A>
{
}

impl<'a, K: AsBytes, V, A: Allocator, const PREFIX_LEN: usize>
    VacantEntry<'a, K, V, PREFIX_LEN, A>
{
    /// Sets the value of the entry with the [`VacantEntry`]’s key, and returns
    /// a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a mutable reference from this mutable reference
        unsafe {
            self.insert_entry(value)
                .delete_point
                .leaf_node_ptr
                .as_value_mut()
        }
    }

    /// Sets the value of the entry with the [`VacantEntry`]’s key, and returns
    /// a [`OccupiedEntry`].
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A> {
        let delete_point = match self.insert_point {
            Some(insert_point) => {
                // SAFETY: We are holding pointers across this function that we intend to use,
                // specifically the pointers inside the [`TreePath`]. That is why we must fixup
                // those pointers after the call using the [`InsertResult`]
                // contents.
                let result = unsafe { self.map.apply_insert_point(insert_point, self.key, value) };

                // Fixup happens here, it is necessary for the safety of future mutations using
                // the entry API
                Self::fixup_after_insert(insert_point, result)
            },
            None => {
                let leaf_node_ptr: crate::raw::NodePtr<
                    PREFIX_LEN,
                    crate::raw::LeafNode<K, V, PREFIX_LEN>,
                > = self.map.init_tree(self.key, value);

                DeletePoint {
                    path: TreePath::Root,
                    leaf_node_ptr,
                }
            },
        };

        OccupiedEntry {
            map: self.map,
            delete_point,
        }
    }

    /// This function will adjust the parent pointers in the [`InsertPoint`] to
    /// reflect changes that were by the insert and reported in the given
    /// [`InsertResult`].
    fn fixup_after_insert(
        insert_point: InsertPoint<K, V, PREFIX_LEN>,
        result: InsertResult<K, V, PREFIX_LEN>,
    ) -> DeletePoint<K, V, PREFIX_LEN> {
        let path = match result.parent_node_change {
            InsertParentNodeChange::NoChange => insert_point.path,
            InsertParentNodeChange::NewParent {
                new_parent_node,
                leaf_node_key_byte,
            } => match insert_point.path {
                TreePath::Root => TreePath::ChildOfRoot {
                    parent: new_parent_node,
                    child_key_byte: leaf_node_key_byte,
                },
                TreePath::ChildOfRoot {
                    parent,
                    child_key_byte,
                } => TreePath::Normal {
                    grandparent: parent,
                    parent_key_byte: child_key_byte,
                    parent: new_parent_node,
                    child_key_byte: leaf_node_key_byte,
                },
                TreePath::Normal {
                    parent,
                    child_key_byte,
                    ..
                } => TreePath::Normal {
                    grandparent: parent,
                    parent_key_byte: child_key_byte,
                    parent: new_parent_node,
                    child_key_byte: leaf_node_key_byte,
                },
            },
        };

        DeletePoint {
            path,
            leaf_node_ptr: result.leaf_node_ptr,
        }
    }

    /// Take ownership of the key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Gets a reference to the key that would be used when inserting a value
    /// through the [`VacantEntry`].
    pub fn key(&self) -> &K {
        &self.key
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This enum is constructed from the [`TreeMap::entry`].
#[derive(Debug)]
pub enum Entry<'a, K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global> {
    /// A view into an occupied entry in a [`TreeMap`].
    Occupied(OccupiedEntry<'a, K, V, PREFIX_LEN, A>),
    /// A view into a vacant entry in a [`TreeMap`].
    Vacant(VacantEntry<'a, K, V, PREFIX_LEN, A>),
}

impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> Entry<'a, K, V, PREFIX_LEN, A>
where
    K: AsBytes,
{
    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(entry) => {
                // SAFETY: This is safe because `Self` has an mutable reference
                // so it's safe to generate a mutable reference from this mutable reference
                f(unsafe { entry.delete_point.leaf_node_ptr.as_value_mut() });
                Entry::Occupied(entry)
            },
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }

    /// Sets the value of the entry, and returns an [`OccupiedEntry`].
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A> {
        match self {
            Entry::Occupied(mut entry) => {
                entry.insert(value);
                entry
            },
            Entry::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Returns a reference to this entry’s key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(V::default()),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    pub fn or_insert(self, value: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(value),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the
    /// entry.
    pub fn or_insert_with<F>(self, f: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(f()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of
    /// the default function. This method allows for generating key-derived
    /// values for insertion by providing the default function a reference to
    /// the key that was moved during the .entry(key) method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying
    /// the key is unnecessary, unlike with .or_insert_with(|| ... ).
    pub fn or_insert_with_key<F>(self, f: F) -> &'a mut V
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let k = f(entry.key());
                entry.insert(k)
            },
        }
    }

    /// Similar to [`Entry::or_default`] but yields an [`OccupiedEntry`]
    pub fn or_default_entry(self) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A>
    where
        V: Default,
    {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert_entry(V::default()),
        }
    }

    /// Similar to [`Entry::or_insert`] but yields an [`OccupiedEntry`]
    pub fn or_insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Similar to [`Entry::or_insert_with`] but yields an [`OccupiedEntry`]
    pub fn or_insert_with_entry<F>(self, f: F) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A>
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert_entry(f()),
        }
    }

    /// Similar to [`Entry::or_insert_with_key`] but yields an [`OccupiedEntry`]
    pub fn or_insert_with_key_entry<F>(self, f: F) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A>
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => {
                let k = f(entry.key());
                entry.insert_entry(k)
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ffi::CString;

    use crate::TreeMap;

    use super::*;

    #[test]
    fn iterators_are_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        fn entry_is_send<'a, K: Send + 'a, V: Send + 'a, A: Send + Allocator + 'a>() {
            is_send::<Entry<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn entry_is_sync<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_sync::<Entry<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        entry_is_send::<[u8; 3], usize, Global>();
        entry_is_sync::<[u8; 3], usize, Global>();
    }

    #[test]
    fn and_modify() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        tree.insert(a.clone(), String::from("a"));
        tree.insert(b.clone(), String::from("b"));

        tree.entry(a.clone()).and_modify(|v| v.push('a'));
        tree.entry(b.clone()).and_modify(|v| v.push('a'));
        tree.entry(c.clone()).and_modify(|v| v.push('a'));

        assert_eq!(tree.get(&a).unwrap(), "aa");
        assert_eq!(tree.get(&b).unwrap(), "ba");
        assert_eq!(tree.get(&c), None);
    }

    #[test]
    fn key() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        tree.insert(a.clone(), String::from("a"));
        tree.insert(b.clone(), String::from("b"));

        assert_eq!(*tree.entry(a.clone()).key(), a);
        assert_eq!(*tree.entry(b.clone()).key(), b);
        assert_eq!(*tree.entry(c.clone()).key(), c);
    }

    #[test]
    fn or() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        let d = CString::new("d").unwrap();
        let e = CString::new("e").unwrap();
        let f = CString::new("f").unwrap();
        tree.insert(a.clone(), String::from("a"));
        tree.insert(b.clone(), String::from("b"));

        tree.entry(a.clone()).or_insert(String::from("aa"));
        tree.entry(b.clone()).or_insert(String::from("bb"));
        tree.entry(c.clone()).or_insert(String::from("cc"));
        tree.entry(d.clone()).or_default();
        tree.entry(e.clone()).or_insert_with(|| String::from("e"));
        tree.entry(f.clone())
            .or_insert_with_key(|k| String::from(k.to_str().unwrap()));

        assert_eq!(tree.get(&a).unwrap(), "a");
        assert_eq!(tree.get(&b).unwrap(), "b");
        assert_eq!(tree.get(&c).unwrap(), "cc");
        assert_eq!(tree.get(&d).unwrap(), &String::default());
        assert_eq!(tree.get(&e).unwrap(), "e");
        assert_eq!(tree.get(&f).unwrap(), "f");
    }

    #[test]
    fn insert_entry() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        tree.insert(a.clone(), String::from("a"));
        tree.insert(b.clone(), String::from("b"));

        tree.entry(a.clone()).insert_entry(String::from("aa"));
        tree.entry(b.clone()).insert_entry(String::from("bb"));
        tree.entry(c.clone()).insert_entry(String::from("cc"));

        assert_eq!(tree.get(&a).unwrap(), "aa");
        assert_eq!(tree.get(&b).unwrap(), "bb");
        assert_eq!(tree.get(&c).unwrap(), "cc");
    }

    #[test]
    fn remove_entry() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        let d = CString::new("d").unwrap();
        let e = CString::new("e").unwrap();
        tree.insert(a.clone(), String::from("aa"));
        tree.insert(b.clone(), String::from("bb"));
        tree.insert(c.clone(), String::from("cc"));
        tree.insert(d.clone(), String::from("dd"));
        tree.insert(e.clone(), String::from("ee"));

        match tree.entry(a.clone()) {
            Entry::Occupied(e) => {
                let (k, v) = e.remove_entry();
                assert_eq!(k, a);
                assert_eq!(v, "aa");
            },
            Entry::Vacant(_) => panic!(),
        }

        match tree.entry(a.clone()) {
            Entry::Occupied(_) => panic!(),
            Entry::Vacant(e) => {
                let e = e.insert_entry(String::from("aaa"));
                let v = e.get();
                assert_eq!(v, "aaa");
            },
        }
    }

    #[test]
    fn regression_01cf3c554fd1da17307a8451972a823db68d4c04() {
        // [
        //     Entry(
        //         OrInsertWith,
        //         [
        //             5,
        //         ],
        //     ),
        //     Entry(
        //         InsertEntry(
        //             Some(
        //                 Remove,
        //             ),
        //         ),
        //         [
        //             255,
        //         ],
        //     ),
        // ]
        let mut tree = TreeMap::<u8, _>::new();

        assert_eq!(*tree.try_entry(5).unwrap().or_insert_with(|| 1), 1);
        assert_eq!(tree.try_entry(255).unwrap().insert_entry(2).remove(), 2);
        let _ = crate::visitor::WellFormedChecker::check(&tree).unwrap();
    }

    #[test]
    fn regression_a1d834472bf0d652a9ad39eab5d6e173825c80dc() {
        // [
        //     Entry(
        //         OrInsertWith,
        //         [
        //             205,
        //             61,
        //             255,
        //         ],
        //     ),
        //     Entry(
        //         OrInsertWith,
        //         [
        //             0,
        //         ],
        //     ),
        //     Entry(
        //         InsertEntry(
        //             Some(
        //                 Remove,
        //             ),
        //         ),
        //         [
        //             205,
        //             1,
        //         ],
        //     ),
        // ]

        let mut tree = TreeMap::<Box<[u8]>, _>::new();

        assert_eq!(
            *tree
                .try_entry(Box::from([205, 61, 255]))
                .unwrap()
                .or_insert_with(|| 1),
            1
        );
        assert_eq!(
            *tree.try_entry(Box::from([0])).unwrap().or_insert_with(|| 2),
            2
        );
        assert_eq!(
            tree.try_entry(Box::from([205, 1]))
                .unwrap()
                .insert_entry(3)
                .remove(),
            3
        );
        let _ = crate::visitor::WellFormedChecker::check(&tree).unwrap();
    }

    #[test]
    fn regression_0a766df3f0e1c88c45e5ff54d247731a8efefe08() {
        // [
        //     Entry(
        //         OrInsertWith,
        //         [
        //             5,
        //             205,
        //             205,
        //             205,
        //             235,
        //             0,
        //             205,
        //         ],
        //     ),
        //     Entry(
        //         OrInsertWith,
        //         [
        //             205,
        //             210,
        //             205,
        //             205,
        //             205,
        //         ],
        //     ),
        //     Entry(
        //         OrInsertWith,
        //         [
        //             205,
        //             205,
        //             5,
        //         ],
        //     ),
        //     Entry(
        //         InsertEntry(
        //             Some(
        //                 Remove,
        //             ),
        //         ),
        //         [
        //             205,
        //             205,
        //             205,
        //             205,
        //             36,
        //             0,
        //         ],
        //     ),
        // ]

        let mut tree = TreeMap::<Box<[u8]>, _>::new();

        assert_eq!(
            *tree
                .try_entry(Box::from([5, 205, 205, 205, 235, 0, 20]))
                .unwrap()
                .or_insert_with(|| 1),
            1
        );
        assert_eq!(
            *tree
                .try_entry(Box::from([205, 210, 205, 205, 20]))
                .unwrap()
                .or_insert_with(|| 2),
            2
        );
        assert_eq!(
            *tree
                .try_entry(Box::from([205, 205, 5]))
                .unwrap()
                .or_insert_with(|| 3),
            3
        );
        assert_eq!(
            tree.try_entry(Box::from([205, 205, 205, 205, 36, 0]))
                .unwrap()
                .insert_entry(4)
                .remove(),
            4
        );

        let _ = crate::visitor::WellFormedChecker::check(&tree).unwrap();
    }

    #[test]
    fn empty_tree_insert_remove() {
        let mut tree = TreeMap::<[u8; 0], i32>::new();

        assert_eq!(tree.entry([]).insert_entry(0).remove(), 0);

        let _ = crate::visitor::WellFormedChecker::check(&tree).unwrap();
    }

    #[test]
    fn replace_existing_leaf() {
        let mut tree = TreeMap::<[u8; 2], i32>::new();

        tree.insert([0, 0], 0);
        tree.insert([1, 0], 1);
        tree.insert([3, 0], 3);

        assert_eq!(tree.entry([2, 0]).insert_entry(2).get(), &2);

        assert_eq!(tree.values().copied().collect::<Vec<_>>(), [0, 1, 2, 3]);
        let _ = crate::visitor::WellFormedChecker::check(&tree).unwrap();
    }
}
