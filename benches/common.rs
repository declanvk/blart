use std::{ffi::CString, sync::OnceLock};

use blart::{
    testing::{
        generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, swap,
        PrefixExpansion,
    },
    AsBytes, TreeMap,
};
use rand::{
    rngs::StdRng,
    seq::{IndexedRandom, SliceRandom},
    Rng, SeedableRng,
};

static DICTIONARY: &str = include_str!("data/medium-dict.txt");

fn tree_from_keys<K: AsBytes>(keys: impl IntoIterator<Item = K>) -> TreeMap<K, usize> {
    let mut tree = TreeMap::new();
    for (v, k) in keys.into_iter().enumerate() {
        tree.try_insert(k, v).unwrap();
    }

    tree
}

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

/// Seed for every random choice the benchmarks make, so that runs are
/// comparable.
#[cfg_attr(not(test), expect(dead_code))]
pub const SAMPLE_SEED: u64 = 0x5EED_B1A7;

/// Choose `num_elements` randomly-selected distinct keys from `tree`.
#[cfg_attr(not(test), expect(dead_code))]
pub fn sample_keys<K: AsBytes, V, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    num_elements: usize,
) -> Vec<&K> {
    let keys = tree.keys().collect::<Vec<_>>();
    assert!(num_elements <= keys.len());
    let mut rng = StdRng::seed_from_u64(SAMPLE_SEED);
    let mut sample: Vec<_> = keys
        .choose_multiple(&mut rng, num_elements)
        .copied()
        .collect();
    sample.shuffle(&mut rng);
    sample
}

/// Choose `num_ranges` ranges of `range_len` consecutive keys from `tree`,
/// returned as `(start, end)` pairs for a half-open `start..end` range.
#[cfg_attr(not(test), expect(dead_code))]
pub fn sample_ranges<K: AsBytes, V, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    num_ranges: usize,
    range_len: usize,
) -> Vec<(&K, &K)> {
    let keys = tree.keys().collect::<Vec<_>>();
    assert!(range_len < keys.len());
    let mut rng = StdRng::seed_from_u64(SAMPLE_SEED);
    (0..num_ranges)
        .map(|_| {
            let start = rng.random_range(0..keys.len() - range_len);
            (keys[start], keys[start + range_len])
        })
        .collect()
}

#[cfg_attr(not(test), expect(dead_code))]
pub fn skewed_tree() -> &'static TreeMap<Box<[u8]>, usize> {
    static TREE: OnceLock<TreeMap<Box<[u8]>, usize>> = OnceLock::new();

    TREE.get_or_init(|| tree_from_keys(generate_keys_skewed(256 * 32)))
}

#[cfg_attr(not(test), expect(dead_code))]
pub fn dense_fixed_length_key_tree() -> &'static TreeMap<[u8; 2], usize> {
    static TREE: OnceLock<TreeMap<[u8; 2], usize>> = OnceLock::new();

    TREE.get_or_init(|| tree_from_keys(generate_key_fixed_length([u8::MAX, 127])))
}

// pub fn medium_sparse_fixed_length_key_tree() -> TreeMap<[u8; 3], usize> {
//     tree_from_keys(generate_key_fixed_length([63; 3]))
// }

#[cfg_attr(not(test), expect(dead_code))]
pub fn sparse_fixed_length_key_tree() -> &'static TreeMap<[u8; 16], usize> {
    static TREE: OnceLock<TreeMap<[u8; 16], usize>> = OnceLock::new();

    TREE.get_or_init(|| tree_from_keys(generate_key_fixed_length([1; 16])))
}

pub fn with_prefixes_tree() -> &'static TreeMap<Box<[u8]>, usize> {
    static TREE: OnceLock<TreeMap<Box<[u8]>, usize>> = OnceLock::new();

    TREE.get_or_init(|| {
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
