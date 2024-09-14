use std::{borrow::Borrow, mem::replace};

use crate::{AsBytes, DeletePoint, InsertPoint, LeafNode, NodePtr, OpaqueNodePtr, TreeMap};

/// A view into an occupied entry in a [`TreeMap`]. It is part of the
/// [`EntryRef`] enum.
pub struct OccupiedEntryRef<'a, K, V, const PREFIX_LEN: usize> {
    pub(crate) leaf_node_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,

    /// Used for the removal
    pub(crate) map: &'a mut TreeMap<K, V, PREFIX_LEN>,
    /// Used for the removal
    pub(crate) grandparent_ptr_and_parent_key_byte: Option<(OpaqueNodePtr<K, V, PREFIX_LEN>, u8)>,
    /// Used for the removal
    pub(crate) parent_ptr_and_child_key_byte: Option<(OpaqueNodePtr<K, V, PREFIX_LEN>, u8)>,
}

impl<'a, K, V, const PREFIX_LEN: usize> OccupiedEntryRef<'a, K, V, PREFIX_LEN> {
    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a shared reference from this mutable reference
        unsafe { self.leaf_node_ptr.as_value_ref() }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the [`OccupiedEntryRef`] which may outlive
    /// the destruction of the Entry value, see
    /// [`OccupiedEntryRef::into_mut`].
    pub fn get_mut(&mut self) -> &mut V {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a mutable reference from this mutable reference
        unsafe { self.leaf_node_ptr.as_value_mut() }
    }

    /// Sets the value of the entry, and returns the entry’s old value.
    pub fn insert(&mut self, value: V) -> V {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a mutable reference from this mutable reference
        let leaf_value = unsafe { self.leaf_node_ptr.as_value_mut() };
        replace(leaf_value, value)
    }

    /// Converts the [`OccupiedEntryRef`] into a mutable reference to the value
    /// in the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the [`OccupiedEntryRef`], see
    /// [`OccupiedEntryRef::get_mut`].
    pub fn into_mut(self) -> &'a mut V {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a mutable reference from this mutable reference
        unsafe { self.leaf_node_ptr.as_value_mut() }
    }

    /// Gets a reference to the key in the entry.
    pub fn key(&self) -> &K {
        // SAFETY: This is safe because `Self` has an mutable reference
        // so it's safe to generate a shared reference from this mutable reference
        unsafe { self.leaf_node_ptr.as_key_ref() }
    }

    /// Take the ownership of the key and value from the map. Keeps the
    /// allocated memory for reuse.
    pub fn remove_entry(self) -> (K, V) {
        let delete_point = DeletePoint {
            grandparent_ptr_and_parent_key_byte: self.grandparent_ptr_and_parent_key_byte,
            parent_ptr_and_child_key_byte: self.parent_ptr_and_child_key_byte,
            leaf_node_ptr: self.leaf_node_ptr,
        };

        let delete_result = self.map.apply_delete_point(delete_point);
        delete_result.deleted_leaf.into_entry()
    }

    /// Takes the value out of the entry, and returns it. Keeps the allocated
    /// memory for reuse.
    pub fn remove(self) -> K {
        self.remove_entry().0
    }
}

/// A view into a vacant entry in a [`TreeMap`]. It is part of the [`EntryRef`]
/// enum.
pub struct VacantEntryRef<'a, 'b, K, V, Q, const PREFIX_LEN: usize>
where
    K: AsBytes + Borrow<Q> + From<&'b Q>,
    Q: AsBytes + ?Sized,
{
    pub(crate) map: &'a mut TreeMap<K, V, PREFIX_LEN>,
    pub(crate) key: &'b Q,
    pub(crate) insert_point: Option<InsertPoint<K, V, PREFIX_LEN>>,
}

impl<'a, 'b, K, V, Q, const PREFIX_LEN: usize> VacantEntryRef<'a, 'b, K, V, Q, PREFIX_LEN>
where
    K: AsBytes + Borrow<Q> + From<&'b Q>,
    Q: AsBytes + ?Sized,
{
    /// Sets the value of the entry with the [`VacantEntryRef`]’s key, and
    /// returns a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        // SAFETY: This is safe because `Self` has an shared reference
        // so it's safe to generate a mutable reference from this shared reference
        unsafe { self.insert_entry(value).leaf_node_ptr.as_value_mut() }
    }

    /// Sets the value of the entry with the [`VacantEntryRef`]’s key, and
    /// returns a [`OccupiedEntryRef`].
    pub fn insert_entry(self, value: V) -> OccupiedEntryRef<'a, K, V, PREFIX_LEN> {
        let (leaf_node_ptr, grandparent_ptr_and_parent_key_byte, parent_ptr_and_child_key_byte) =
            match self.insert_point {
                Some(insert_point) => {
                    let grandparent_ptr = insert_point.grandparent_ptr_and_parent_key_byte;
                    let parent_ptr = insert_point.parent_ptr_and_child_key_byte;
                    let result = self
                        .map
                        .apply_insert_point(insert_point, self.key.into(), value);
                    (result.leaf_node_ptr, grandparent_ptr, parent_ptr)
                },
                None => {
                    let leaf_node_ptr = self.map.init_tree(self.key.into(), value);
                    (leaf_node_ptr, None, None)
                },
            };

        OccupiedEntryRef {
            map: self.map,
            leaf_node_ptr,
            grandparent_ptr_and_parent_key_byte,
            parent_ptr_and_child_key_byte,
        }
    }

    /// Take ownership of the key.
    pub fn into_key(self) -> K {
        self.key.into()
    }

    /// Gets a reference to the key that would be used when inserting a value
    /// through the [`VacantEntryRef`].
    pub fn key(&self) -> &Q {
        self.key
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This enum is constructed from the entry method on [`TreeMap`].
pub enum EntryRef<'a, 'b, K, V, Q, const PREFIX_LEN: usize>
where
    K: AsBytes + Borrow<Q> + From<&'b Q>,
    Q: AsBytes + ?Sized,
{
    /// A view into an occupied entry in a [`TreeMap`].
    Occupied(OccupiedEntryRef<'a, K, V, PREFIX_LEN>),
    /// A view into a vacant entry in a [`TreeMap`].
    Vacant(VacantEntryRef<'a, 'b, K, V, Q, PREFIX_LEN>),
}

impl<'a, 'b, K, V, Q, const PREFIX_LEN: usize> EntryRef<'a, 'b, K, V, Q, PREFIX_LEN>
where
    K: AsBytes + Borrow<Q> + From<&'b Q>,
    Q: AsBytes + ?Sized,
{
    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            EntryRef::Occupied(entry) => {
                // SAFETY: This is safe because `Self` has an shared reference
                // so it's safe to generate a mutable reference from this shared reference
                f(unsafe { entry.leaf_node_ptr.as_value_mut() });
                EntryRef::Occupied(entry)
            },
            EntryRef::Vacant(entry) => EntryRef::Vacant(entry),
        }
    }

    /// Sets the value of the entry, and returns an [`OccupiedEntryRef`].
    pub fn insert_entry(self, value: V) -> OccupiedEntryRef<'a, K, V, PREFIX_LEN> {
        match self {
            EntryRef::Occupied(mut entry) => {
                entry.insert(value);
                entry
            },
            EntryRef::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Returns a reference to this entry’s key.
    pub fn key(&self) -> &Q {
        match self {
            EntryRef::Occupied(entry) => entry.key().borrow(),
            EntryRef::Vacant(entry) => entry.key(),
        }
    }

    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(V::default()),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    pub fn or_insert(self, value: V) -> &'a mut V {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(value),
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
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(f()),
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
        F: FnOnce(&Q) -> V,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => {
                let k = f(entry.key());
                entry.insert(k)
            },
        }
    }

    /// Similar to [`EntryRef::or_default`] but yields an [`OccupiedEntryRef`]
    pub fn or_default_entry(self) -> OccupiedEntryRef<'a, K, V, PREFIX_LEN>
    where
        V: Default,
    {
        match self {
            EntryRef::Occupied(entry) => entry,
            EntryRef::Vacant(entry) => entry.insert_entry(V::default()),
        }
    }

    /// Similar to [`EntryRef::or_insert`] but yields an [`OccupiedEntryRef`]
    pub fn or_insert_entry(self, value: V) -> OccupiedEntryRef<'a, K, V, PREFIX_LEN> {
        match self {
            EntryRef::Occupied(entry) => entry,
            EntryRef::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Similar to [`EntryRef::or_insert_with`] but yields an
    /// [`OccupiedEntryRef`]
    pub fn or_insert_with_entry<F>(self, f: F) -> OccupiedEntryRef<'a, K, V, PREFIX_LEN>
    where
        F: FnOnce() -> V,
    {
        match self {
            EntryRef::Occupied(entry) => entry,
            EntryRef::Vacant(entry) => entry.insert_entry(f()),
        }
    }

    /// Similar to [`EntryRef::or_insert_with_key`] but yields an
    /// [`OccupiedEntryRef`]
    pub fn or_insert_with_key_entry<F>(self, f: F) -> OccupiedEntryRef<'a, K, V, PREFIX_LEN>
    where
        F: FnOnce(&Q) -> V,
    {
        match self {
            EntryRef::Occupied(entry) => entry,
            EntryRef::Vacant(entry) => {
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
    fn and_modify() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        tree.insert(a.clone(), String::from("a"));
        tree.insert(b.clone(), String::from("b"));

        tree.entry_ref(&a).and_modify(|v| v.push('a'));
        tree.entry_ref(&b).and_modify(|v| v.push('a'));
        tree.entry_ref(&c).and_modify(|v| v.push('a'));

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

        assert_eq!(tree.entry_ref(&a).key(), a.borrow());
        assert_eq!(tree.entry_ref(&b).key(), b.borrow());
        assert_eq!(tree.entry_ref(&c).key(), c.borrow());
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

        tree.entry_ref(&a).or_insert(String::from("aa"));
        tree.entry_ref(&b).or_insert(String::from("bb"));
        tree.entry_ref(&c).or_insert(String::from("cc"));
        tree.entry_ref(&d).or_default();
        tree.entry_ref(&e).or_insert_with(|| String::from("e"));
        tree.entry_ref(&f)
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

        tree.entry_ref(&a).insert_entry(String::from("aa"));
        tree.entry_ref(&b).insert_entry(String::from("bb"));
        tree.entry_ref(&c).insert_entry(String::from("cc"));

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

        match tree.entry_ref(&a) {
            EntryRef::Occupied(e) => {
                let (k, v) = e.remove_entry();
                assert_eq!(k, a);
                assert_eq!(v, "aa");
            },
            EntryRef::Vacant(_) => panic!(),
        }

        match tree.entry_ref(&a) {
            EntryRef::Occupied(_) => panic!(),
            EntryRef::Vacant(e) => {
                let e = e.insert_entry(String::from("aaa"));
                let v = e.get();
                assert_eq!(v, "aaa");
            },
        }
    }
}
