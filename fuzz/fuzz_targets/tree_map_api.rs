#![no_main]
#![feature(btree_entry_insert)]

use blart::{visitor::WellFormedChecker, TreeMap};
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use std::{
    collections::{hash_map::RandomState, BTreeMap},
    hash::BuildHasher,
    mem,
};

#[derive(Arbitrary, Debug)]
enum EntryAction {
    AndModify(Option<Box<EntryAction>>),
    InsertEntry(Option<OccupiedEntryAction>),
    OrDefault,
    OrInsert,
    OrInsertWith,
    OrInsertWithKey,
}

#[derive(Arbitrary, Debug)]
enum OccupiedEntryAction {
    Insert,
    Remove,
}

#[derive(Arbitrary, Debug)]
enum RetainKind {
    All,
    None,
    Half,
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
    GetPrefixKey(Box<[u8]>),
    CheckLen,
    CheckIter,
    Remove(Box<[u8]>),
    RemovePrefix(Box<[u8]>),
    TryInsert(Box<[u8]>),
    TryInsertMany(Box<[u8]>, u8),
    ForceInsert(Box<[u8]>),
    Clone,
    Hash,
    Entry(EntryAction, Box<[u8]>),
    Fuzzy(Box<[u8]>),
    Prefix(Box<[u8]>),
    IntoIter { take_front: usize, take_back: usize },
    Retain(RetainKind),
    SplitOff(Box<[u8]>),
}

libfuzzer_sys::fuzz_target!(|actions: Vec<Action>| {
    let mut tree = TreeMap::<_, u32>::new();
    let mut oracle = BTreeMap::<_, u32>::new();
    let mut next_value = 0;

    for action in actions {
        match action {
            Action::Clear => {
                tree.clear();
                oracle.clear();
            },
            Action::ContainsKey(key) => {
                assert_eq!(
                    tree.contains_key(key.as_ref()),
                    oracle.contains_key(key.as_ref())
                );
            },
            Action::GetMinimum => {
                let min = tree.first_key_value();
                assert_eq!(min, oracle.first_key_value());
                if let Some((_, min_value)) = min {
                    assert!(*min_value < next_value);
                }
            },
            Action::PopMinimum => {
                let min = tree.pop_first();
                assert_eq!(min, oracle.pop_first());
                if let Some((_, min_value)) = min {
                    assert!(min_value < next_value);
                }
            },
            Action::GetMaximum => {
                let max = tree.last_key_value();
                assert_eq!(max, oracle.last_key_value());
                if let Some((_, max_value)) = max {
                    assert!(*max_value < next_value);
                }
            },
            Action::PopMaximum => {
                let max = tree.pop_last();
                assert_eq!(max, oracle.pop_last());
                if let Some((_, max_value)) = max {
                    assert!(max_value < next_value);
                }
            },
            Action::GetKey(key) => {
                let entry = tree.get_mut(key.as_ref());
                let oracle_entry = oracle.get_mut(key.as_ref());
                assert_eq!(entry, oracle_entry);
                if let Some(value) = entry {
                    *value = value.saturating_sub(1);
                    let oracle_value = oracle_entry.unwrap();
                    *oracle_value = oracle_value.saturating_sub(1);
                    assert_eq!(value, oracle_value);
                }
            },
            Action::GetPrefixKey(key) => {
                // No easy way to replicate this using BTreeMap.
                let _ = tree.get_prefix_mut(key.as_ref());
            },
            Action::CheckLen => {
                assert!((tree.is_empty() && tree.len() == 0) || tree.len() > 0);
            },
            Action::CheckIter => {
                tree.iter_mut().for_each(|(_, value)| {
                    *value = value.saturating_add(1);
                });
                oracle.iter_mut().for_each(|(_, value)| {
                    *value = value.saturating_add(1);
                });

                tree.iter_mut().rev().for_each(|(_, value)| {
                    *value = value.saturating_sub(1);
                });
                oracle.iter_mut().rev().for_each(|(_, value)| {
                    *value = value.saturating_sub(1);
                });

                assert!(tree.keys().is_sorted());
                assert!(tree.keys().rev().is_sorted_by(|a, b| a >= b));
                assert!(tree.iter().count() == tree.len());
                assert!(tree.iter().rev().count() == tree.len());
            },
            Action::Remove(key) => {
                let value = tree.remove(key.as_ref());
                assert_eq!(value, oracle.remove(key.as_ref()));
                if let Some(value) = value {
                    assert!(value < next_value);
                }
            },
            Action::RemovePrefix(prefix) => {
                let to_remove: Vec<_> = tree
                    .prefix(prefix.as_ref())
                    .map(|(k, _)| k)
                    .cloned()
                    .collect();

                for key in to_remove {
                    let value = tree.remove(&key);
                    assert_eq!(value, oracle.remove(&key));
                }
            },
            Action::TryInsert(key) => {
                let value = next_value;
                next_value += 1;

                let result = tree.try_insert(key.clone(), value);
                if let Ok(prev) = result {
                    let oracle_prev = oracle.insert(key.clone(), value);
                    assert_eq!(prev, oracle_prev);
                }
            },
            Action::ForceInsert(key) => {
                let value = next_value;
                next_value += 1;

                let _ = tree.force_insert(key.clone(), value);
                oracle.retain(|f, _| !f.starts_with(&key) && !key.starts_with(f));
                oracle.insert(key, value);
            },
            Action::TryInsertMany(prefix, count) => {
                let mut key = Vec::from(prefix);
                key.push(0);
                for suffix in 0..=count {
                    let value = next_value;
                    next_value += 1;
                    *key.last_mut().unwrap() = suffix;
                    let key = Box::<[u8]>::from(key.clone());

                    let result = tree.try_insert(key.clone(), value);
                    if let Ok(prev) = result {
                        let oracle_prev = oracle.insert(key.clone(), value);
                        assert_eq!(prev, oracle_prev);
                    }
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
                if let Ok(entry) = tree.try_entry(key.clone()) {
                    let value = next_value;
                    next_value += 1;
                    let oracle_entry = oracle.entry(key.clone());
                    apply_entry_action(ea, entry, oracle_entry, value);
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
                let _oracle = mem::replace(&mut oracle, BTreeMap::<_, u32>::new());

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
            Action::Retain(kind) => match kind {
                RetainKind::All => {
                    tree.retain(|_, _| true);
                    oracle.retain(|_, _| true);
                },
                RetainKind::None => {
                    tree.retain(|_, _| false);
                    oracle.retain(|_, _| false);
                },
                RetainKind::Half => {
                    let mut i = 0;
                    tree.retain(|_, _| {
                        i += 1;
                        i % 2 == 0
                    });
                    i = 0;
                    oracle.retain(|_, _| {
                        i += 1;
                        i % 2 == 0
                    });
                },
            },
            Action::SplitOff(split_key) => {
                let tree_removed = tree.split_off(&split_key);
                let oracle_removed = oracle.split_off(&split_key);

                assert!(
                    tree_removed.iter().eq(oracle_removed.iter()),
                    "{:?} != {:?}",
                    tree,
                    oracle
                );
            },
        }

        assert!(tree.iter().eq(oracle.iter()), "{:?} != {:?}", tree, oracle);
        assert_eq!(tree.len(), oracle.len());
        let _ = WellFormedChecker::check(&tree).expect("tree should be well-formed");
    }
});

fn apply_entry_action(
    ea: EntryAction,
    tree_entry: blart::map::Entry<'_, Box<[u8]>, u32>,
    oracle_entry: std::collections::btree_map::Entry<'_, Box<[u8]>, u32>,
    value: u32,
) {
    match ea {
        EntryAction::AndModify(entry_action) => {
            let tree_entry = tree_entry.and_modify(|v| *v = v.saturating_sub(1));
            let oracle_entry = oracle_entry.and_modify(|v| *v = v.saturating_sub(1));

            if let Some(entry_action) = entry_action {
                apply_entry_action(*entry_action, tree_entry, oracle_entry, value);
            }
        },
        EntryAction::InsertEntry(entry_action) => {
            let tree_entry = tree_entry.insert_entry(value);
            let oracle_entry = oracle_entry.insert_entry(value);

            if let Some(occupied_action) = entry_action {
                apply_occupied_entry_action(occupied_action, tree_entry, oracle_entry, value);
            }
        },
        EntryAction::OrDefault => {
            assert_eq!(tree_entry.or_default(), oracle_entry.or_default());
        },
        EntryAction::OrInsert => {
            assert_eq!(tree_entry.or_insert(value), oracle_entry.or_insert(value));
        },
        EntryAction::OrInsertWith => {
            assert_eq!(
                tree_entry.or_insert_with(|| value),
                oracle_entry.or_insert_with(|| value)
            );
        },
        EntryAction::OrInsertWithKey => {
            assert_eq!(
                tree_entry.or_insert_with_key(|_| value),
                oracle_entry.or_insert_with_key(|_| value)
            );
        },
    };
}

fn apply_occupied_entry_action(
    occupied_action: OccupiedEntryAction,
    mut tree_entry: blart::map::OccupiedEntry<'_, Box<[u8]>, u32>,
    mut oracle_entry: std::collections::btree_map::OccupiedEntry<'_, Box<[u8]>, u32>,
    value: u32,
) {
    match occupied_action {
        OccupiedEntryAction::Insert => {
            assert_eq!(tree_entry.insert(value), oracle_entry.insert(value));
        },
        OccupiedEntryAction::Remove => {
            assert_eq!(tree_entry.remove(), oracle_entry.remove());
        },
    }
}
