use std::mem::replace;

use crate::{
    AsBytes, DeletePoint, InsertPoint, LeafNode, NodeHeader, NodePtr, OpaqueNodePtr, RawTreeMap,
};

/// A view into an occupied entry in a HashMap. It is part of the Entry enum.
pub struct OccupiedEntry<'a, K, V, const NUM_PREFIX_BYTES: usize, H>
where
    K: AsBytes,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    pub(crate) leaf_node_ptr: NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES, H>>,

    /// Used for the removal
    pub(crate) map: &'a mut RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    /// Used for the removal
    pub(crate) grandparent_ptr_and_parent_key_byte:
        Option<(OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>, u8)>,
    /// Used for the removal
    pub(crate) parent_ptr_and_child_key_byte:
        Option<(OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>, u8)>,
}

impl<'a, K, V, const NUM_PREFIX_BYTES: usize, H> OccupiedEntry<'a, K, V, NUM_PREFIX_BYTES, H>
where
    K: AsBytes,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        unsafe { self.leaf_node_ptr.as_value_ref() }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the [`OccupiedEntry`] which may outlive the
    /// destruction of the Entry value, see [`OccupiedEntry::into_mut`].
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { self.leaf_node_ptr.as_value_mut() }
    }

    /// Sets the value of the entry, and returns the entry’s old value.
    pub fn insert(&mut self, value: V) -> V {
        let leaf_value = unsafe { self.leaf_node_ptr.as_value_mut() };
        replace(leaf_value, value)
    }

    /// Converts the [`OccupiedEntry`] into a mutable reference to the value in
    /// the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the [`OccupiedEntry`], see
    /// [`OccupiedEntry::get_mut`].
    pub fn into_mut(self) -> &'a mut V {
        unsafe { self.leaf_node_ptr.as_value_mut() }
    }

    /// Gets a reference to the key in the entry.
    pub fn key(&self) -> &K {
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

/// A view into a vacant entry in a HashMap. It is part of the [`Entry`] enum.
pub struct VacantEntry<'a, K, V, const NUM_PREFIX_BYTES: usize, H>
where
    K: AsBytes,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    pub(crate) map: &'a mut RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    pub(crate) key: K,
    pub(crate) insert_point: Option<InsertPoint<K, V, NUM_PREFIX_BYTES, H>>,
}

impl<'a, K, V, const NUM_PREFIX_BYTES: usize, H> VacantEntry<'a, K, V, NUM_PREFIX_BYTES, H>
where
    K: AsBytes,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    /// Sets the value of the entry with the [`VacantEntry`]’s key, and returns
    /// a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        unsafe { self.insert_entry(value).leaf_node_ptr.as_value_mut() }
    }

    /// Sets the value of the entry with the [`VacantEntry`]’s key, and returns
    /// a [`OccupiedEntry`].
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, NUM_PREFIX_BYTES, H> {
        let (leaf_node_ptr, grandparent_ptr_and_parent_key_byte, parent_ptr_and_child_key_byte) =
            match self.insert_point {
                Some(insert_point) => {
                    let grandparent_ptr = insert_point.grandparent_ptr_and_parent_key_byte;
                    let parent_ptr = insert_point.parent_ptr_and_child_key_byte;
                    let result = self.map.apply_insert_point(insert_point, self.key, value);
                    (result.leaf_node_ptr, grandparent_ptr, parent_ptr)
                },
                None => {
                    let leaf_node_ptr = self.map.init_tree(self.key, value);
                    (leaf_node_ptr, None, None)
                },
            };

        OccupiedEntry {
            map: self.map,
            leaf_node_ptr,
            grandparent_ptr_and_parent_key_byte,
            parent_ptr_and_child_key_byte,
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

///A view into a single entry in a map, which may either be vacant or occupied.
//
//This enum is constructed from the entry method on HashMap.
pub enum Entry<'a, K, V, const NUM_PREFIX_BYTES: usize, H>
where
    K: AsBytes,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    /// A view into an occupied entry in a HashMap. It is part of the [`Entry`]
    /// enum.
    Occupied(OccupiedEntry<'a, K, V, NUM_PREFIX_BYTES, H>),
    /// A view into a vacant entry in a HashMap. It is part of the [`Entry`]
    /// enum.
    Vacant(VacantEntry<'a, K, V, NUM_PREFIX_BYTES, H>),
}

impl<'a, K, V, const NUM_PREFIX_BYTES: usize, H> Entry<'a, K, V, NUM_PREFIX_BYTES, H>
where
    K: AsBytes,
    H: NodeHeader<NUM_PREFIX_BYTES>,
{
    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(entry) => {
                f(unsafe { entry.leaf_node_ptr.as_value_mut() });
                Entry::Occupied(entry)
            },
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }

    /// Sets the value of the entry, and returns an [`OccupiedEntry`].
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, NUM_PREFIX_BYTES, H> {
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
    pub fn or_default_entry(self) -> OccupiedEntry<'a, K, V, NUM_PREFIX_BYTES, H>
    where
        V: Default,
    {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert_entry(V::default()),
        }
    }

    /// Similar to [`Entry::or_insert`] but yields an [`OccupiedEntry`]
    pub fn or_insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, NUM_PREFIX_BYTES, H> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Similar to [`Entry::or_insert_with`] but yields an [`OccupiedEntry`]
    pub fn or_insert_with_entry<F>(self, f: F) -> OccupiedEntry<'a, K, V, NUM_PREFIX_BYTES, H>
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert_entry(f()),
        }
    }

    /// Similar to [`Entry::or_insert_with_key`] but yields an [`OccupiedEntry`]
    pub fn or_insert_with_key_entry<F>(self, f: F) -> OccupiedEntry<'a, K, V, NUM_PREFIX_BYTES, H>
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
            Entry::Vacant(_) => unreachable!(),
        }

        match tree.entry(a.clone()) {
            Entry::Occupied(_) => unreachable!(),
            Entry::Vacant(e) => {
                let e = e.insert_entry(String::from("aaa"));
                let v = e.get();
                assert_eq!(v, "aaa");
            },
        }
    }
}