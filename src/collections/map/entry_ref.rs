use std::{
    borrow::Borrow,
    default,
    marker::PhantomData,
    mem::{replace, swap},
};

use crate::{
    AsBytes, DeletePoint, DeleteResult, InsertPoint, LeafNode, NoPrefixesBytes, NodePtr,
    OpaqueNodePtr, TreeMap,
};

pub struct OccupiedEntryRef<'a, K, V>
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

impl<'a, K, V> OccupiedEntryRef<'a, K, V>
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

        let delete_result = self.map.apply_delete_point(delete_point);
        delete_result.deleted_leaf.into_entry()
    }

    pub fn remove(self) -> K {
        self.remove_entry().0
    }
}

pub struct VacantEntryRef<'a, 'b, K, V, Q>
where
    K: AsBytes + Borrow<Q> + From<&'b Q>,
    Q: AsBytes + ?Sized,
{
    pub map: &'a mut TreeMap<K, V>,
    pub key: &'b Q,
    pub insert_point: Option<InsertPoint<K, V>>,
}

impl<'a, 'b, K, V, Q> VacantEntryRef<'a, 'b, K, V, Q>
where
    K: AsBytes + Borrow<Q> + From<&'b Q>,
    Q: AsBytes + ?Sized,
{
    pub fn insert(self, value: V) -> &'a mut V {
        unsafe { self.insert_entry(value).leaf_node_ptr.as_value_mut() }
    }

    pub fn insert_entry(self, value: V) -> OccupiedEntryRef<'a, K, V> {
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

    pub fn into_key(self) -> K {
        self.key.into()
    }

    pub fn key(&self) -> &Q {
        &self.key
    }
}

pub enum EntryRef<'a, 'b, K, V, Q>
where
    K: AsBytes + Borrow<Q> + From<&'b Q>,
    Q: AsBytes + ?Sized,
{
    Occupied(OccupiedEntryRef<'a, K, V>),
    Vacant(VacantEntryRef<'a, 'b, K, V, Q>),
}

impl<'a, 'b, K, V, Q> EntryRef<'a, 'b, K, V, Q>
where
    K: AsBytes + Borrow<Q> + From<&'b Q>,
    Q: AsBytes + ?Sized,
{
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            EntryRef::Occupied(entry) => {
                f(unsafe { entry.leaf_node_ptr.as_value_mut() });
                EntryRef::Occupied(entry)
            },
            EntryRef::Vacant(entry) => EntryRef::Vacant(entry),
        }
    }

    pub fn insert_entry(self, value: V) -> OccupiedEntryRef<'a, K, V> {
        match self {
            EntryRef::Occupied(mut entry) => {
                entry.insert(value);
                entry
            },
            EntryRef::Vacant(entry) => entry.insert_entry(value),
        }
    }

    pub fn key(&self) -> &Q {
        match self {
            EntryRef::Occupied(entry) => entry.key().borrow(),
            EntryRef::Vacant(entry) => entry.key(),
        }
    }

    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(V::default()),
        }
    }

    pub fn or_insert(self, value: V) -> &'a mut V {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(value),
        }
    }

    pub fn or_insert_with<F>(self, f: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(f()),
        }
    }

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

    pub fn or_default_entry(self) -> OccupiedEntryRef<'a, K, V>
    where
        V: Default,
    {
        match self {
            EntryRef::Occupied(entry) => entry,
            EntryRef::Vacant(entry) => entry.insert_entry(V::default()),
        }
    }

    pub fn or_insert_entry(self, value: V) -> OccupiedEntryRef<'a, K, V> {
        match self {
            EntryRef::Occupied(entry) => entry,
            EntryRef::Vacant(entry) => entry.insert_entry(value),
        }
    }

    pub fn or_insert_with_entry<F>(self, f: F) -> OccupiedEntryRef<'a, K, V>
    where
        F: FnOnce() -> V,
    {
        match self {
            EntryRef::Occupied(entry) => entry,
            EntryRef::Vacant(entry) => entry.insert_entry(f()),
        }
    }

    pub fn or_insert_with_key_entry<F>(self, f: F) -> OccupiedEntryRef<'a, K, V>
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
    fn insert_entry() {
        let mut tree = TreeMap::new();
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

        match tree.entry_ref(&a) {
            EntryRef::Occupied(e) => {
                let (k, v) = e.remove_entry();
                assert_eq!(k, a);
                assert_eq!(v, "aa");
            },
            EntryRef::Vacant(_) => unreachable!(),
        }

        match tree.entry_ref(&a) {
            EntryRef::Occupied(_) => unreachable!(),
            EntryRef::Vacant(e) => {
                let e = e.insert_entry(String::from("aaa"));
                let v = e.get();
                assert_eq!(v, "aaa");
            },
        }
    }
}
