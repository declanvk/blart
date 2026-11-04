//! Fuzz the `TreeMap` API with randomly generated keys.

#![no_main]
#![feature(btree_entry_insert)]

use std::{
    collections::{hash_map::RandomState, BTreeMap},
    hash::BuildHasher,
    mem,
    ops::Bound,
};

use blart::{
    map::{PrefixEntry, PrefixOccupied},
    visitor::WellFormedChecker,
    TreeMap,
};

mod common;

use common::{Action, EntryAction, OccupiedEntryAction, PrefixEntryAction, RangeBound};

/// Return true if the range would not cause a panic in `BTreeMap::range`.
fn range_is_valid<K: Ord>(start: &RangeBound<K>, end: &RangeBound<K>) -> bool {
    match (start, end) {
        (RangeBound::Included(s), RangeBound::Included(e)) => s <= e,
        (
            RangeBound::Included(s) | RangeBound::Excluded(s),
            RangeBound::Included(e) | RangeBound::Excluded(e),
        ) => s < e,
        _ => true,
    }
}

libfuzzer_sys::fuzz_target!(|actions: Vec<Action<Box<[u8]>>>| {
    let mut tree = TreeMap::<Box<[u8]>, u32>::new();
    let mut oracle = BTreeMap::<Box<[u8]>, u32>::new();
    // The second tree holds the result of `SplitOff`, and can be swapped with the first
    let mut other_tree = TreeMap::<Box<[u8]>, u32>::new();
    let mut other_oracle = BTreeMap::<Box<[u8]>, u32>::new();
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
                let entry = tree.prefix_get_mut(key.as_ref());
                let oracle_entry = oracle.iter_mut().find(|f| key.as_ref().starts_with(f.0));
                if let Some(value) = entry {
                    *value = value.saturating_sub(1);
                    let oracle_value = oracle_entry.unwrap().1;
                    *oracle_value = oracle_value.saturating_sub(1);
                    assert_eq!(value, oracle_value);
                }
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
            Action::PrefixInsert(key) => {
                let value = next_value;
                next_value += 1;

                let _ = tree.prefix_insert(key.clone(), value);
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
            Action::PrefixEntry(ea, key) => {
                let entry = tree.prefix_entry(key.clone());
                match &entry {
                    PrefixEntry::Occupied(PrefixOccupied::Inner(entry)) => {
                        let oracle_iter = oracle
                            .iter()
                            .filter(|f| f.0.starts_with(&key) || key.starts_with(f.0));
                        assert!(entry.iter().eq(oracle_iter));
                    },
                    _ => {},
                }
                let value = next_value;
                next_value += 1;
                let oracle_entry = oracle.entry(key.clone());
                apply_prefix_entry_action(ea, entry, oracle_entry, value);
                oracle.retain(|f, _| {
                    // Remove everything that prefixes or is prefixed except for what we just added
                    (!f.starts_with(&key) && !key.starts_with(f)) || f == &key
                });
            },
            Action::Fuzzy(key) => {
                // TODO: Provide an oracle implementation for fuzzy search (hard)
                let v: Vec<_> = tree.fuzzy(&key, 3).collect();
                std::hint::black_box(v);
            },
            Action::Prefix(key) => {
                let tree_result: Vec<_> = tree.prefix(&key).collect();
                let oracle_result: Vec<_> = oracle
                    .range::<[u8], _>((Bound::Included(key.as_ref()), Bound::Unbounded))
                    .take_while(|(k, _)| k.starts_with(&key))
                    .collect();

                assert_eq!(tree_result, oracle_result);
            },
            Action::Range(start, end) => {
                if range_is_valid(&start, &end) {
                    let bounds = (
                        start.as_bound().map(|key| key.as_ref()),
                        end.as_bound().map(|key| key.as_ref()),
                    );
                    let tree_result: Vec<_> = tree.range::<[u8], _>(bounds).collect();
                    let oracle_result: Vec<_> = oracle.range::<[u8], _>(bounds).collect();
                    assert_eq!(
                        tree_result.len(),
                        oracle_result.len(),
                        "range result lengths differ for bounds {bounds:?}"
                    );
                    for ((tk, tv), (ok, ov)) in tree_result.iter().zip(oracle_result.iter()) {
                        assert_eq!(tk.as_ref() as &[u8], ok.as_ref() as &[u8]);
                        assert_eq!(tv, ov);
                    }
                }
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
            Action::ExtractIf(start, end, kind) => {
                if range_is_valid(&start, &end) {
                    let bounds = (start.as_bound(), end.as_bound());
                    let tree_extracted: Vec<_> =
                        tree.extract_if(bounds, kind.predicate()).collect();
                    let oracle_extracted: Vec<_> =
                        oracle.extract_if(bounds, kind.predicate()).collect();
                    assert_eq!(tree_extracted, oracle_extracted);
                }
            },
            Action::Retain(kind) => {
                tree.retain(kind.predicate());
                oracle.retain(kind.predicate());
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
                assert_eq!(tree_removed.len(), oracle_removed.len());
                let _ = WellFormedChecker::check(&tree_removed)
                    .expect("split off tree should be well-formed");

                other_tree = tree_removed;
                other_oracle = oracle_removed;
            },
            Action::SwapTrees => {
                mem::swap(&mut tree, &mut other_tree);
                mem::swap(&mut oracle, &mut other_oracle);
            },
        }

        assert!(tree.iter().eq(oracle.iter()), "{:?} != {:?}", tree, oracle);
        assert_eq!(tree.len(), oracle.len());
        let _ = WellFormedChecker::check(&tree).expect("tree should be well-formed");
    }
});

fn apply_prefix_entry_action(
    ea: PrefixEntryAction,
    tree_entry: blart::map::PrefixEntry<'_, Box<[u8]>, u32>,
    oracle_entry: std::collections::btree_map::Entry<'_, Box<[u8]>, u32>,
    value: u32,
) {
    match ea {
        PrefixEntryAction::InsertEntry(entry_action) => {
            let tree_entry = tree_entry.insert_entry(value);
            let oracle_entry = oracle_entry.insert_entry(value);

            if let Some(occupied_action) = entry_action {
                apply_occupied_entry_action(occupied_action, tree_entry, oracle_entry, value);
            }
        },
        PrefixEntryAction::OrDefault => {
            assert_eq!(tree_entry.or_default(), oracle_entry.or_default());
        },
        PrefixEntryAction::OrInsert => {
            assert_eq!(tree_entry.or_insert(value), oracle_entry.or_insert(value));
        },
        PrefixEntryAction::OrInsertWith => {
            assert_eq!(
                tree_entry.or_insert_with(|| value),
                oracle_entry.or_insert_with(|| value)
            );
        },
        PrefixEntryAction::OrInsertWithKey => {
            assert_eq!(
                tree_entry.or_insert_with_key(|_| value),
                oracle_entry.or_insert_with_key(|_| value)
            );
        },
    };
}

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
