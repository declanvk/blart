#![feature(is_sorted)]
#![no_main]

use blart::FixedTreeMap;
use blart::map::Entry;
use blart::map::EntryRef;
use blart::Mapped;
use blart::ToUBE;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use std::{
    collections::hash_map::RandomState,
    hash::{BuildHasher, Hash, Hasher},
};

#[derive(Arbitrary, Debug)]
enum EntryAction {
    AndModify,
    InsertEntry,
    Key,
    OrDefault,
    OrInsert,
    OrInsertWith,
    OrInsertWithKey,
    RemoveEntry
}

#[derive(Arbitrary, Debug)]
enum Action {
    Clear,
    ContainsKey(usize),
    GetMinimum,
    PopMinimum,
    GetMaximum,
    PopMaximum,
    GetKey(usize),
    CheckLen,
    CheckIter,
    Remove(usize),
    Insert(usize),
    Extend(Vec<usize>),
    Clone,
    Hash,
    Entry(EntryAction, usize)
}

libfuzzer_sys::fuzz_target!(|actions: Vec<Action>| {
    let mut tree = FixedTreeMap::<Mapped::<ToUBE<usize>>, u32>::new();
    let mut next_key = 0;

    for action in actions {
        match action {
            Action::Clear => {
                tree.clear();
            },
            Action::ContainsKey(key) => {
                let key = Mapped::<ToUBE<usize>>::new(key);
                let _ = tree.contains_key(&key);
            },
            Action::GetMinimum => {
                let min = tree.first_key_value();
                if let Some((_, min_value)) = min {
                    assert!(*min_value < next_key);
                }
            },
            Action::PopMinimum => {
                let min = tree.pop_first();
                if let Some((_, min_value)) = min {
                    assert!(min_value < next_key);
                }
            },
            Action::GetMaximum => {
                let max = tree.last_key_value();
                if let Some((_, max_value)) = max {
                    assert!(*max_value < next_key);
                }
            },
            Action::PopMaximum => {
                let max = tree.pop_last();
                if let Some((_, max_value)) = max {
                    assert!(max_value < next_key);
                }
            },
            Action::GetKey(key) => {
                let key = Mapped::<ToUBE<usize>>::new(key);
                let entry = tree.get_mut(&key);
                if let Some(value) = entry {
                    *value = value.saturating_sub(1);
                }
            },
            Action::CheckLen => {
                assert!((tree.is_empty() && tree.len() == 0) || tree.len() > 0);
            },
            Action::CheckIter => {
                tree.iter_mut().for_each(|(_, value)| {
                    *value = value.saturating_add(1);
                });

                tree.iter_mut().rev().for_each(|(_, value)| {
                    *value = value.saturating_sub(1);
                });

                assert!(tree.keys().is_sorted());
                assert!(tree.keys().rev().is_sorted_by(|a, b| a >= b));
                assert!(tree.iter().count() == tree.len());
                assert!(tree.iter().rev().count() == tree.len());
            },
            Action::Remove(key) => {
                let key = Mapped::<ToUBE<usize>>::new(key);
                if let Some(value) = tree.remove(&key) {
                    assert!(value < next_key);
                }
            },
            Action::Insert(key) => {
                let key = Mapped::<ToUBE<usize>>::new(key);
                let value = next_key;
                next_key += 1;

                let _ = tree.insert(key, value);
            },
            Action::Extend(new_keys) => {
                for key in new_keys {
                    let key = Mapped::<ToUBE<usize>>::new(key);
                    let value = next_key;
                    next_key += 1;

                    let _ = tree.insert(key, value);
                }
            },
            Action::Clone => {
                tree = tree.clone();
            },
            Action::Hash => {
                let hash_builder = RandomState::new();
                let tree_copy = tree.clone();

                let original_hash = hash_one(&hash_builder, &tree);
                let copy_hash = hash_one(&hash_builder, &tree_copy);

                assert_eq!(original_hash, copy_hash, "{:?} != {:?}", tree, tree_copy);
            },
            Action::Entry(ea, key) => {
                let key = Mapped::<ToUBE<usize>>::new(key);
                let entry = tree.entry(key);
                let value = next_key;
                next_key += 1;
                match ea {
                    EntryAction::AndModify => {entry.and_modify(|v| *v = v.saturating_sub(1));},
                    EntryAction::InsertEntry => {entry.insert_entry(value);},
                    EntryAction::Key => {entry.key();},
                    EntryAction::OrDefault => {entry.or_default();},
                    EntryAction::OrInsert => {entry.or_insert(value);},
                    EntryAction::OrInsertWith => {entry.or_insert_with(|| value);},
                    EntryAction::OrInsertWithKey => {entry.or_insert_with_key(|_| value);},
                    EntryAction::RemoveEntry => {
                        match entry {
                            blart::map::Entry::Occupied(e) => {e.remove_entry();},
                            blart::map::Entry::Vacant(_) => {},
                        };
                    }
                };
            }
        }
    }
});

fn hash_one(hasher_builder: &impl BuildHasher, value: impl Hash) -> u64 {
    let mut hasher = hasher_builder.build_hasher();
    value.hash(&mut hasher);
    hasher.finish()
}
