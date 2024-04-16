use std::{
    borrow::Borrow,
    default,
    marker::PhantomData,
    mem::{replace, swap},
};

use crate::{AsBytes, InsertPoint, LeafNode, NoPrefixesBytes, NodePtr, TreeMap};

pub struct OccupiedEntry<'a, K, V> {
    pub entry_ref: (&'a K, &'a mut V),
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub fn get(&self) -> &V {
        self.entry_ref.1
    }

    pub fn get_mut(&mut self) -> &mut V {
        self.entry_ref.1
    }

    pub fn insert(&mut self, value: V) -> V {
        replace(self.entry_ref.1, value)
    }

    pub fn into_mut(self) -> &'a mut V {
        self.entry_ref.1
    }

    pub fn key(&self) -> &K {
        &self.entry_ref.0
    }

    // TODO: Remove, Replace
}

pub struct VacantEntry<'a, K: AsBytes, V> {
    pub map: &'a mut TreeMap<K, V>,
    pub key: K,
    pub insert_point: Option<InsertPoint<K, V>>,
}

impl<'a, K: AsBytes, V> VacantEntry<'a, K, V> {
    fn inner_insert(self, value: V) -> (&'a K, &'a mut V)
    where
        K: AsBytes,
    {
        match self.insert_point {
            Some(insert_point) => {
                let result = self.map.apply_insert_point(insert_point, self.key, value);
                result.entry_ref
            },
            None => {
                let leaf = self.map.init_tree(self.key, value);
                unsafe { leaf.as_key_ref_value_mut() }
            },
        }
    }

    pub fn insert(self, value: V) -> &'a mut V
    where
        K: AsBytes,
    {
        self.inner_insert(value).1
    }

    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V>
    where
        K: AsBytes,
    {
        OccupiedEntry {
            entry_ref: self.inner_insert(value),
        }
    }

    pub fn into_key(self) -> K {
        self.key
    }

    pub fn key(&self) -> &K {
        &self.key
    }
}

pub enum Entry<'a, K: AsBytes, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K: AsBytes, V> Entry<'a, K, V> {
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(entry) => {
                f(entry.entry_ref.1);
                Entry::Occupied(entry)
            },
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }

    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V>
    where
        K: AsBytes,
    {
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
        K: AsBytes,
        V: Default,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(V::default()),
        }
    }

    pub fn or_insert(self, value: V) -> &'a mut V
    where
        K: AsBytes,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(value),
        }
    }

    pub fn or_insert_with<F>(self, f: F) -> &'a mut V
    where
        K: AsBytes,
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(f()),
        }
    }

    pub fn or_insert_with_key<F>(self, f: F) -> &'a mut V
    where
        K: AsBytes,
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
}
