#![no_main]

use blart::TreeMap;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use std::{
    collections::hash_map::RandomState,
    hash::{BuildHasher, Hash, Hasher},
    mem,
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
    RemoveEntry,
}

#[derive(Arbitrary, Debug)]
enum Action {
    Clear,
    ContainsKey(Box<[u8]>),
    GetMinimum,
    PopMinimum,
    GetMaximum,
    PopMaximum,
    GetKey(Box<[u8]>),
    CheckLen,
    CheckIter,
    Remove(Box<[u8]>),
    TryInsert(Box<[u8]>),
    Extend(Vec<Box<[u8]>>),
    Clone,
    Hash,
    Entry(EntryAction, Box<[u8]>),
    EntryRef(EntryAction, Box<[u8]>),
    Fuzzy(Box<[u8]>),
    Prefix(Box<[u8]>),
    IntoIter { take_front: usize, take_back: usize },
}

libfuzzer_sys::fuzz_target!(|actions: Vec<Action>| {
    let mut tree = TreeMap::<_, u32>::new();
    let mut next_value = 0;

    for action in actions {
        match action {
            Action::Clear => {
                tree.clear();
            },
            Action::ContainsKey(key) => {
                let _ = tree.contains_key(key.as_ref());
            },
            Action::GetMinimum => {
                let min = tree.first_key_value();
                if let Some((_, min_value)) = min {
                    assert!(*min_value < next_value);
                }
            },
            Action::PopMinimum => {
                let min = tree.pop_first();
                if let Some((_, min_value)) = min {
                    assert!(min_value < next_value);
                }
            },
            Action::GetMaximum => {
                let max = tree.last_key_value();
                if let Some((_, max_value)) = max {
                    assert!(*max_value < next_value);
                }
            },
            Action::PopMaximum => {
                let max = tree.pop_last();
                if let Some((_, max_value)) = max {
                    assert!(max_value < next_value);
                }
            },
            Action::GetKey(key) => {
                let entry = tree.get_mut(key.as_ref());
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
                if let Some(value) = tree.remove(key.as_ref()) {
                    assert!(value < next_value);
                }
            },
            Action::TryInsert(key) => {
                let value = next_value;
                next_value += 1;

                let _ = tree.try_insert(key, value);
            },
            Action::Extend(new_keys) => {
                for key in new_keys {
                    let value = next_value;
                    next_value += 1;

                    let _ = tree.try_insert(key, value);
                }
            },
            Action::Clone => {
                let tree_copy = tree.clone();
                assert!(tree_copy.iter().eq(tree.iter()));
                tree = tree_copy;
            },
            Action::Hash => {
                let hash_builder = RandomState::new();
                let tree_copy = tree.clone();

                let original_hash = hash_builder.hash_one(&tree);
                let copy_hash = hash_builder.hash_one(&tree_copy);

                assert_eq!(original_hash, copy_hash, "{:?} != {:?}", tree, tree_copy);
            },
            Action::Entry(ea, key) => {
                if let Ok(entry) = tree.try_entry(key) {
                    let value = next_value;
                    next_value += 1;
                    match ea {
                        EntryAction::AndModify => {
                            entry.and_modify(|v| *v = v.saturating_sub(1));
                        },
                        EntryAction::InsertEntry => {
                            entry.insert_entry(value);
                        },
                        EntryAction::Key => {
                            entry.key();
                        },
                        EntryAction::OrDefault => {
                            entry.or_default();
                        },
                        EntryAction::OrInsert => {
                            entry.or_insert(value);
                        },
                        EntryAction::OrInsertWith => {
                            entry.or_insert_with(|| value);
                        },
                        EntryAction::OrInsertWithKey => {
                            entry.or_insert_with_key(|_| value);
                        },
                        EntryAction::RemoveEntry => {
                            match entry {
                                blart::map::Entry::Occupied(e) => {
                                    e.remove_entry();
                                },
                                blart::map::Entry::Vacant(_) => {},
                            };
                        },
                    };
                }
            },
            Action::EntryRef(ea, key) => {
                if let Ok(entry) = tree.try_entry_ref(&key) {
                    let value = next_value;
                    next_value += 1;
                    match ea {
                        EntryAction::AndModify => {
                            entry.and_modify(|v| *v = v.saturating_sub(1));
                        },
                        EntryAction::InsertEntry => {
                            entry.insert_entry(value);
                        },
                        EntryAction::Key => {
                            entry.key();
                        },
                        EntryAction::OrDefault => {
                            entry.or_default();
                        },
                        EntryAction::OrInsert => {
                            entry.or_insert(value);
                        },
                        EntryAction::OrInsertWith => {
                            entry.or_insert_with(|| value);
                        },
                        EntryAction::OrInsertWithKey => {
                            entry.or_insert_with_key(|_| value);
                        },
                        EntryAction::RemoveEntry => {
                            match entry {
                                blart::map::EntryRef::Occupied(e) => {
                                    e.remove_entry();
                                },
                                blart::map::EntryRef::Vacant(_) => {},
                            };
                        },
                    };
                }
            },
            Action::Fuzzy(key) => {
                let v: Vec<_> = tree.fuzzy(&key, 3).collect();
                std::hint::black_box(v);
            },
            Action::Prefix(key) => {
                let v: Vec<_> = tree.prefix(&key).collect();
                std::hint::black_box(v);
            },
            Action::IntoIter {
                take_front,
                take_back,
            } => {
                let tree = mem::replace(&mut tree, TreeMap::<_, u32>::new());

                let original_size = tree.len();
                let mut it = tree.into_iter();
                let front_count = it.by_ref().take(take_front).count();
                let back_count = it.rev().take(take_back).count();

                assert_eq!(
                    front_count + back_count,
                    original_size.min(take_front.saturating_add(take_back))
                );
                assert!(front_count <= take_front);
                assert!(back_count <= take_back);
            },
        }
    }
});
