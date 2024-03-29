#![no_main]

use blart::map::TreeMap;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use std::{
    collections::hash_map::RandomState,
    hash::{BuildHasher, Hash, Hasher},
};

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
    Clone,
    Extend(Vec<Box<[u8]>>),
    Hash,
}

libfuzzer_sys::fuzz_target!(|actions: Vec<Action>| {
    let mut tree = TreeMap::<_, u32>::new();
    let mut next_key = 0;

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
                let entry = tree.get_mut(key.as_ref());
                if let Some(value) = entry {
                    *value = value.saturating_sub(1);
                }
            },
            Action::CheckLen => {
                assert!((tree.is_empty() && tree.len() == 0) || tree.len() > 0);
            },
            Action::CheckIter => {
                let zipped_key_value = tree.keys().zip(tree.values());
                let regular_iter = tree.iter();

                assert!(zipped_key_value
                    .zip(regular_iter)
                    .all(|(elt_zipped, elt_regular)| { elt_zipped == elt_regular }));

                tree.iter_mut().for_each(|(_, value)| {
                    *value = value.saturating_sub(1);
                });
            },
            Action::Remove(key) => {
                if let Some(value) = tree.remove(key.as_ref()) {
                    assert!(value < next_key);
                }
            },
            Action::TryInsert(key) => {
                let value = next_key;
                next_key += 1;

                let _ = tree.try_insert(key, value);
            },
            Action::Clone => {
                tree = tree.clone();
            },
            Action::Extend(new_keys) => {
                for key in new_keys {
                    let value = next_key;
                    next_key += 1;

                    let _ = tree.try_insert(key, value);
                }
            },
            Action::Hash => {
                let hash_builder = RandomState::new();
                let tree_copy = tree.clone();

                let original_hash = hash_one(&hash_builder, &tree);
                let copy_hash = hash_one(&hash_builder, &tree_copy);

                assert_eq!(original_hash, copy_hash, "{:?} != {:?}", tree, tree_copy);
            },
        }
    }
});

fn hash_one(hasher_builder: &impl BuildHasher, value: impl Hash) -> u64 {
    let mut hasher = hasher_builder.build_hasher();
    value.hash(&mut hasher);
    hasher.finish()
}
