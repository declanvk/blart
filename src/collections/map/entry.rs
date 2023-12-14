use std::{default, marker::PhantomData};

use crate::{AsBytes, InsertPoint, LeafNode, NoPrefixesBytes, TreeMap, NodePtr};

pub struct OccupiedEntry<'a, K, V> {
    pub key: K,
    pub leaf: (&'a K, &'a mut V),
}

pub struct VacantEntry<'a, K, V> {
    pub key: K,
    pub insert_point: Option<InsertPoint<K, V>>,
    pub map: &'a mut TreeMap<K, V>,
}

pub enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(entry) => {
                f(entry.leaf.1);
                Entry::Occupied(entry)
            },
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }

    pub fn or_insert(self, default: V) -> &'a mut V
    where
        K: NoPrefixesBytes,
    {
        match self {
            Entry::Occupied(entry) => entry.leaf.1,
            Entry::Vacant(entry) => match entry.insert_point {
                Some(insert_point) => {
                    let result =
                        unsafe { insert_point.apply(entry.key, default).unwrap_unchecked() };
                    entry.map.apply_insert_result(&result);
                    result.new_value_ref
                },
                None => {
                    let leaf = NodePtr::allocate_node_ptr(LeafNode::new(entry.key, default));
                    let new_value_ref = unsafe { leaf.as_value_mut() };

                    entry.map.root = Some(leaf.to_opaque());
                    entry.map.num_entries = 1;
                    new_value_ref
                },
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
    fn or_insert() {
        let mut tree = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        tree.insert(a.clone(), 1u32);
        tree.insert(b.clone(), 2u32);
        let r = tree.entry(a.clone()).or_insert(10);
        *r += 1;
        println!("{tree:?}");
    }
}
