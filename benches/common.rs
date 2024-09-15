use std::{ffi::CString, sync::OnceLock};

use blart::{
    tests_common::{
        generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, PrefixExpansion,
    },
    AsBytes, TreeMap,
};
use rand::{prelude::Distribution, SeedableRng};

static DICTIONARY: &str = include_str!("data/medium-dict.txt");

fn tree_from_keys<K: AsBytes>(keys: impl IntoIterator<Item = K>) -> TreeMap<K, usize> {
    let mut tree = TreeMap::new();
    for (v, k) in keys.into_iter().enumerate() {
        tree.try_insert(k, v).unwrap();
    }

    tree
}

#[allow(dead_code)]
pub fn get_first_key<K: AsBytes + Clone, V, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
) -> &K {
    tree.first_key_value().unwrap().0
}

#[allow(dead_code)]
pub fn get_middle_key<K: AsBytes + Clone, V, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    forward_step_size: usize,
    backward_step_size: usize,
) -> &K {
    let mut last_key = None;
    let mut iter = tree.keys();
    assert!(!tree.is_empty());

    'outer: loop {
        for _ in 0..forward_step_size {
            let current = iter.next();
            if current.is_none() {
                break 'outer;
            }
            last_key = current;
        }

        for _ in 0..backward_step_size {
            let current = iter.next_back();
            if current.is_none() {
                break 'outer;
            }
            last_key = current;
        }
    }

    last_key.expect("tree is non-empty")
}

#[allow(dead_code)]
pub fn get_last_key<K: AsBytes + Clone, V, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
) -> &K {
    tree.last_key_value().unwrap().0
}

#[allow(dead_code)]
pub fn select_zipfian_keys<K: AsBytes + Clone, V, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    num_elements: usize,
) -> Vec<&K> {
    let keys = tree.keys().collect::<Vec<_>>();
    let distr = zipf::ZipfDistribution::new(tree.len(), 1.78).unwrap();
    let mut rng = rand::rngs::StdRng::from_seed([128; 32]);

    distr
        .map(move |idx| keys[idx])
        .sample_iter(&mut rng)
        .take(num_elements)
        .collect()
}

#[allow(dead_code)]
pub fn remove_keys<K: AsBytes + Clone, V, const PREFIX_LEN: usize>(
    tree: &mut TreeMap<K, V, PREFIX_LEN>,
    keys: Vec<&K>,
) -> Vec<(K, V)> {
    let output = Vec::with_capacity(keys.len());

    for key in keys {
        let _ = tree.remove(key);
    }

    output
}

#[allow(dead_code)]
pub fn skewed_tree() -> &'static TreeMap<Box<[u8]>, usize> {
    static TREE: OnceLock<TreeMap<Box<[u8]>, usize>> = OnceLock::new();

    TREE.get_or_init(|| tree_from_keys(generate_keys_skewed(256 * 128)))
}

#[allow(dead_code)]
pub fn dense_fixed_length_key_tree() -> &'static TreeMap<[u8; 2], usize> {
    static TREE: OnceLock<TreeMap<[u8; 2], usize>> = OnceLock::new();

    TREE.get_or_init(|| tree_from_keys(generate_key_fixed_length([u8::MAX, 127])))
}

// pub fn medium_sparse_fixed_length_key_tree() -> TreeMap<[u8; 3], usize> {
//     tree_from_keys(generate_key_fixed_length([63; 3]))
// }

// pub fn sparse_fixed_length_key_tree() -> TreeMap<[u8; 16], usize> {
//     tree_from_keys(generate_key_fixed_length([1; 16]))
// }

pub fn with_prefixes_tree() -> &'static TreeMap<Box<[u8]>, usize> {
    static TREE: OnceLock<TreeMap<Box<[u8]>, usize>> = OnceLock::new();

    &TREE.get_or_init(|| {
        tree_from_keys(generate_key_with_prefix(
            [7; 5],
            [
                PrefixExpansion {
                    base_index: 1,
                    expanded_length: 12,
                },
                PrefixExpansion {
                    base_index: 4,
                    expanded_length: 8,
                },
            ],
        ))
    })
}

pub fn dictionary_tree() -> &'static TreeMap<CString, usize> {
    fn swap<A, B>((a, b): (A, B)) -> (B, A) {
        (b, a)
    }

    static TREE: OnceLock<TreeMap<CString, usize>> = OnceLock::new();

    TREE.get_or_init(|| {
        DICTIONARY
            .split('\n')
            .filter(|s| !s.is_empty())
            .map(|s| CString::new(s).unwrap())
            .enumerate()
            .map(swap)
            .collect()
    })
}
