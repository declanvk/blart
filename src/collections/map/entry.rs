use std::{
    borrow::Borrow,
    default,
    marker::PhantomData,
    mem::{replace, swap},
};

use crate::{
    inner_delete_unchecked, AsBytes, DeletePoint, DeleteResult, InsertPoint, LeafNode,
    NoPrefixesBytes, NodePtr, OpaqueNodePtr, TreeMap,
};

pub struct OccupiedEntry<'a, K, V>
where
    K: AsBytes,
{
    pub leaf_node_ptr: NodePtr<LeafNode<K, V>>,

    /// Used for the removal
    pub map: &'a mut TreeMap<K, V>,
    /// Used for the removal
    pub grandparent_ptr_and_parent_key_byte: Option<(OpaqueNodePtr<K, V>, u8)>,
    /// Used for the removal
    pub parent_ptr_and_child_key_byte: Option<(OpaqueNodePtr<K, V>, u8)>,
}

impl<'a, K, V> OccupiedEntry<'a, K, V>
where
    K: AsBytes,
{
    pub fn get(&self) -> &V {
        unsafe { self.leaf_node_ptr.as_value_ref() }
    }

    pub fn get_mut(&mut self) -> &mut V {
        unsafe { self.leaf_node_ptr.as_value_mut() }
    }

    pub fn insert(&mut self, value: V) -> V {
        let leaf_value = unsafe { self.leaf_node_ptr.as_value_mut() };
        replace(leaf_value, value)
    }

    pub fn into_mut(self) -> &'a mut V {
        unsafe { self.leaf_node_ptr.as_value_mut() }
    }

    pub fn key(&self) -> &K {
        unsafe { self.leaf_node_ptr.as_key_ref() }
    }

    pub fn remove_entry(self) -> (K, V) {
        let delete_point = DeletePoint {
            grandparent_ptr_and_parent_key_byte: self.grandparent_ptr_and_parent_key_byte,
            parent_ptr_and_child_key_byte: self.parent_ptr_and_child_key_byte,
            leaf_node_ptr: self.leaf_node_ptr,
        };

        let DeleteResult {
            deleted_leaf,
            new_root,
        } = unsafe { inner_delete_unchecked(self.map.root.unwrap_unchecked(), delete_point) };

        self.map.num_entries -= 1;
        self.map.root = new_root;
        deleted_leaf.into_entry()
    }

    pub fn remove(self) -> K {
        self.remove_entry().0
    }
}

pub struct VacantEntry<'a, K, V>
where
    K: AsBytes,
{
    pub map: &'a mut TreeMap<K, V>,
    pub key: K,
    pub insert_point: Option<InsertPoint<K, V>>,
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: AsBytes,
{
    pub fn insert(self, value: V) -> &'a mut V {
        unsafe { self.insert_entry(value).leaf_node_ptr.as_value_mut() }
    }

    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
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

    pub fn into_key(self) -> K {
        self.key
    }

    pub fn key(&self) -> &K {
        &self.key
    }
}

pub enum Entry<'a, K, V>
where
    K: AsBytes,
{
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: AsBytes,
{
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

    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        match self {
            Entry::Occupied(mut entry) => {
                entry.insert(value);
                entry
            },
            Entry::Vacant(entry) => entry.insert_entry(value),
        }
    }

    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(V::default()),
        }
    }

    pub fn or_insert(self, value: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(value),
        }
    }

    pub fn or_insert_with<F>(self, f: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(f()),
        }
    }

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


    pub fn or_default_entry(self) -> OccupiedEntry<'a, K, V>
    where
        V: Default,
    {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert_entry(V::default()),
        }
    }

    pub fn or_insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert_entry(value),
        }
    }

    pub fn or_insert_with_entry<F>(self, f: F) -> OccupiedEntry<'a, K, V>
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert_entry(f()),
        }
    }

    pub fn or_insert_with_key_entry<F>(self, f: F) -> OccupiedEntry<'a, K, V>
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
    use std::{
        ffi::CString,
        mem::ManuallyDrop,
        ptr::{read, NonNull},
    };

    use super::*;

    #[test]
    fn and_modify() {
        let mut tree = TreeMap::new();
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
        let mut tree = TreeMap::new();
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
        let mut tree = TreeMap::new();
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
        let mut tree = TreeMap::new();
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
        let mut tree = TreeMap::new();
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
