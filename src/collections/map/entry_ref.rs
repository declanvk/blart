use std::{
    borrow::Borrow,
    default,
    marker::PhantomData,
    mem::{replace, swap},
};

use crate::{AsBytes, InsertPoint, LeafNode, NoPrefixesBytes, NodePtr, TreeMap};

pub struct OccupiedEntryRef<'a, 'b, K, V, Q: ?Sized> {
    pub leaf: (&'a K, &'a mut V),
    pub key: &'b Q,
}

impl<'a, 'b, K, V, Q: ?Sized> OccupiedEntryRef<'a, 'b, K, V, Q> {
    pub fn get(&self) -> &V {
        self.leaf.1
    }

    pub fn get_mut(&mut self) -> &mut V {
        self.leaf.1
    }

    pub fn insert(&mut self, value: V) -> V {
        replace(self.leaf.1, value)
    }

    pub fn into_mut(self) -> &'a mut V {
        self.leaf.1
    }

    pub fn key(&self) -> &Q {
        self.key
    }

    // TODO: Remove, Replace
}

pub struct VacantEntryRef<'a, 'b, K, V, Q: ?Sized> {
    pub map: &'a mut TreeMap<K, V>,
    pub key: &'b Q,
    pub insert_point: Option<InsertPoint<K, V>>,
}

impl<'a, 'b, K, V, Q: ?Sized> VacantEntryRef<'a, 'b, K, V, Q> {
    pub fn insert(self, value: V) -> &'a mut V
    where
        K: AsBytes + From<&'b Q>,
    {
        match self.insert_point {
            Some(insert_point) => {
                let result = self
                    .map
                    .apply_insert_point(insert_point, self.key.into(), value);
                result.new_value_ref
            },
            None => {
                let leaf = self.map.init_tree(self.key.into(), value);
                unsafe { leaf.as_value_mut() }
            },
        }
    }

    // TODO: insert_entry

    pub fn into_key(self) -> K
    where
        K: From<&'b Q>,
    {
        self.key.into()
    }

    pub fn key(&self) -> &Q {
        self.key
    }
}

pub enum EntryRef<'a, 'b, K, V, Q: ?Sized> {
    Occupied(OccupiedEntryRef<'a, 'b, K, V, Q>),
    Vacant(VacantEntryRef<'a, 'b, K, V, Q>),
}

impl<'a, 'b, K, V, Q: ?Sized> EntryRef<'a, 'b, K, V, Q> {
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            EntryRef::Occupied(entry) => {
                f(entry.leaf.1);
                EntryRef::Occupied(entry)
            },
            EntryRef::Vacant(entry) => EntryRef::Vacant(entry),
        }
    }

    pub fn key(&self) -> &Q
    where
        K: AsBytes + Borrow<Q> + From<&'b Q>,
        Q: AsBytes,
    {
        match self {
            EntryRef::Occupied(entry) => entry.key(),
            EntryRef::Vacant(entry) => entry.key(),
        }
    }

    pub fn or_insert(self, value: V) -> &'a mut V
    where
        K: AsBytes + From<&'b Q>,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(value),
        }
    }

    pub fn or_default(self) -> &'a mut V
    where
        K: AsBytes + From<&'b Q>,
        V: Default,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(V::default()),
        }
    }

    pub fn or_insert_with<F>(self, f: F) -> &'a mut V
    where
        K: AsBytes + From<&'b Q>,
        F: FnOnce() -> V,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(f()),
        }
    }

    pub fn or_insert_with_key<F>(self, f: F) -> &'a mut V
    where
        K: AsBytes + From<&'b Q>,
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

        tree.entry_ref(&a).and_modify(|v| v.push('a'));
        tree.entry_ref(&b).and_modify(|v| v.push('a'));
        tree.entry_ref(&c).and_modify(|v| v.push('a'));

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

        let k = tree.entry_ref(&a).key();

        assert_eq!(tree.entry_ref(&a).key(), a.borrow());
        assert_eq!(tree.entry_ref(&b).key(), b.borrow());
        assert_eq!(tree.entry_ref(&c).key(), c.borrow());
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
    fn occupied_entry_insert() {
        let mut tree = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        tree.insert(a.clone(), String::from("a"));
        tree.insert(b.clone(), String::from("b"));

        match tree.entry_ref(&a) {
            EntryRef::Occupied(mut entry) => {
                let v = entry.insert(String::from("aa"));
                assert_eq!(v, "a");
                assert_eq!(tree.get(&a).unwrap(), "aa");
            },
            EntryRef::Vacant(_) => panic!(),
        }
    }
}
