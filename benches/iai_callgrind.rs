use std::borrow::Borrow;

use crate::common::{
    dictionary_tree, get_first_key, get_last_key, get_middle_key, select_zipfian_keys,
    with_prefixes_tree,
};
use blart::{AsBytes, TreeMap};
use iai_callgrind::{library_benchmark, library_benchmark_group, main, LibraryBenchmarkConfig};

#[macro_use]
mod common;

// CLONE

#[library_benchmark]
#[bench::with_prefixes(with_prefixes_tree())]
#[bench::dictionary(dictionary_tree())]
fn bench_clone<K: AsBytes + Clone, V: Clone, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
) -> TreeMap<K, V, PREFIX_LEN> {
    tree.clone()
}

library_benchmark_group!(name = bench_clone_group; benchmarks = bench_clone);

// LOOKUP

#[library_benchmark]
#[bench::first_key(dictionary_tree(), get_first_key(dictionary_tree()))]
#[bench::last_key(dictionary_tree(), get_last_key(dictionary_tree()))]
fn bench_lookup_single<'a, K: AsBytes, V, const PREFIX_LEN: usize>(
    tree: &'a TreeMap<K, V, PREFIX_LEN>,
    key: &K,
) -> &'a V {
    tree.get(key).unwrap()
}

#[library_benchmark]
#[bench::dictionary(dictionary_tree(), select_zipfian_keys(dictionary_tree(), 2048))]
fn bench_lookup_multiple<K: AsBytes, V, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    keys: Vec<&K>,
) {
    for key in keys {
        let _ = std::hint::black_box(tree.get(key).unwrap());
    }
}

library_benchmark_group!(name = bench_lookup_group; benchmarks = bench_lookup_single, bench_lookup_multiple);

// REMOVE

#[library_benchmark]
#[bench::first_key(dictionary_tree().clone(), get_first_key(dictionary_tree()))]
#[bench::last_key(dictionary_tree().clone(), get_last_key(dictionary_tree()))]
fn bench_remove_single<K: AsBytes, V, const PREFIX_LEN: usize>(
    mut tree: TreeMap<K, V, PREFIX_LEN>,
    key: &K,
) -> Option<V> {
    tree.remove(key)
}

#[library_benchmark]
#[bench::dictionary(dictionary_tree().clone(), select_zipfian_keys(dictionary_tree(), 2048))]
fn bench_remove_multiple<K: AsBytes, V, const PREFIX_LEN: usize>(
    mut tree: TreeMap<K, V, PREFIX_LEN>,
    keys: Vec<&K>,
) {
    for key in keys {
        let _ = std::hint::black_box(tree.remove(key));
    }
}

library_benchmark_group!(name = bench_remove_group; benchmarks = bench_remove_single, bench_remove_multiple);

// INSERT

#[allow(dead_code)]
fn insert_single_setup<K: AsBytes + Clone, V: Clone, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    key: &K,
) -> (TreeMap<K, V, PREFIX_LEN>, K) {
    let mut tree = tree.clone();
    let _ = tree.remove(key);
    (tree, key.clone())
}

#[library_benchmark]
#[bench::first_key(insert_single_setup(dictionary_tree(), get_first_key(dictionary_tree())))]
#[bench::last_key(insert_single_setup(dictionary_tree(), get_last_key(dictionary_tree())))]
fn bench_insert_single<K: AsBytes, V: Default, const PREFIX_LEN: usize>(
    (mut tree, key): (TreeMap<K, V, PREFIX_LEN>, K),
) -> Option<V> {
    tree.try_insert(key, V::default()).ok().flatten()
}

#[allow(dead_code)]
fn insert_multiple_setup<K: AsBytes + Clone, V: Clone, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    keys: Vec<&K>,
) -> (TreeMap<K, V, PREFIX_LEN>, Vec<K>) {
    let mut tree = tree.clone();
    let mut output = Vec::with_capacity(keys.len());
    for key in keys {
        let _ = tree.remove(key);
        output.push(key.clone());
    }
    (tree, output)
}

#[library_benchmark]
#[bench::dictionary(insert_multiple_setup(
    dictionary_tree(),
    select_zipfian_keys(dictionary_tree(), 2048)
))]
fn bench_insert_multiple<K: AsBytes, V: Default, const PREFIX_LEN: usize>(
    (mut tree, keys): (TreeMap<K, V, PREFIX_LEN>, Vec<K>),
) {
    for key in keys {
        let _ = std::hint::black_box(tree.try_insert(key, V::default()).ok().flatten());
    }
}

library_benchmark_group!(name = bench_insert_group; benchmarks = bench_insert_single, bench_insert_multiple);

// ITERATORS

#[library_benchmark]
#[bench::dictionary(dictionary_tree())]
fn bench_full_iterator<K: AsBytes, V, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
) -> bool {
    tree.iter().count() == tree.len()
}

fn truncate_half_slice<T>(b: &[T]) -> &[T] {
    &b[..b.len() / 2]
}

#[library_benchmark]
#[bench::empty(dictionary_tree(), &[])]
#[bench::specific_key(dictionary_tree(), get_last_key(dictionary_tree()).as_bytes())]
#[bench::random_partial(dictionary_tree(), truncate_half_slice(get_middle_key(dictionary_tree(), 1, 1).as_bytes()))]
fn bench_prefix_iterator<K: AsBytes, V, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    prefix: &[u8],
) -> bool {
    tree.prefix(prefix).count() <= tree.len()
}

#[library_benchmark]
#[bench::zero(dictionary_tree(), c"", 0)]
#[bench::specific_key(dictionary_tree(), get_last_key(dictionary_tree()), 100)]
fn bench_fuzzy_iterator<K: AsBytes + Borrow<Q>, V, Q: AsBytes + ?Sized, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    key: &Q,
    edit_distance: usize,
) -> bool {
    tree.fuzzy(key, edit_distance).count() <= tree.len()
}

library_benchmark_group!(name = bench_iterator_group; benchmarks = bench_full_iterator, bench_prefix_iterator, bench_fuzzy_iterator);

// END

fn config() -> LibraryBenchmarkConfig {
    let mut c = LibraryBenchmarkConfig::default();
    c.truncate_description(Some(0));
    c
}

main!(
    config = config();
    library_benchmark_groups = bench_clone_group,
    bench_lookup_group,
    bench_remove_group,
    bench_insert_group,
    bench_iterator_group
);
