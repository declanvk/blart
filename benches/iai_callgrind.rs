use std::{borrow::Borrow, ops::RangeBounds};

use crate::common::{
    dictionary_tree, get_first_key, get_last_key, get_middle_key, select_zipfian_keys,
    with_prefixes_tree,
};
use blart::{AsBytes, TreeMap};
use iai_callgrind::{
    library_benchmark, library_benchmark_group, main, Callgrind, FlamegraphConfig,
    LibraryBenchmarkConfig, OutputFormat,
};

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

#[library_benchmark]
#[bench::full(dictionary_tree(), ..)]
#[bench::specific_key(dictionary_tree(), get_middle_key(dictionary_tree(), 1, 1)..=get_middle_key(dictionary_tree(), 1, 1))]
#[bench::middle_third(dictionary_tree(), get_middle_key(dictionary_tree(), 1, 2)..get_middle_key(dictionary_tree(), 2, 1))]
fn bench_range_iterator<K: AsBytes, V, R: RangeBounds<K>, const PREFIX_LEN: usize>(
    tree: &TreeMap<K, V, PREFIX_LEN>,
    range: R,
) -> bool {
    tree.range(range).count() <= tree.len()
}

library_benchmark_group!(name = bench_iterator_group; benchmarks = bench_full_iterator, bench_prefix_iterator, bench_fuzzy_iterator, bench_range_iterator);

// MODIFYING

#[library_benchmark]
#[bench::all(dictionary_tree().clone(), "all")]
#[bench::half(dictionary_tree().clone(), "half")]
#[bench::none(dictionary_tree().clone(), "none")]
fn bench_retain<K: AsBytes, V, const PREFIX_LEN: usize>(
    mut tree: TreeMap<K, V, PREFIX_LEN>,
    mode: &str,
) {
    match mode {
        "all" => tree.retain(|_, _| true),
        "half" => {
            let mut i = 0;
            tree.retain(|_, _| {
                i += 1;
                i % 2 == 0
            })
        },
        "none" => tree.retain(|_, _| false),
        _ => unreachable!(),
    }
    std::hint::black_box(tree);
}

fn u128_tree(range: std::ops::Range<u128>) -> TreeMap<u128, usize> {
    range.map(|i| (i, i as usize)).collect()
}

#[library_benchmark]
#[bench::no_overlap(u128_tree(0..1024), u128_tree(1024..2048))]
#[bench::overlap(u128_tree(0..1024), u128_tree(512..1536))]
fn bench_append(mut tree1: TreeMap<u128, usize>, mut tree2: TreeMap<u128, usize>) {
    tree1.append(&mut tree2);
    std::hint::black_box(tree1);
}

#[library_benchmark]
#[bench::dictionary(dictionary_tree().clone(), get_middle_key(dictionary_tree(), 1, 1))]
fn bench_split_off<K, V, const PREFIX_LEN: usize>(
    mut tree: TreeMap<K, V, PREFIX_LEN>,
    key: &K,
) -> TreeMap<K, V, PREFIX_LEN>
where
    K: AsBytes + Borrow<K> + Clone,
    V: Clone,
{
    tree.split_off(key)
}

#[library_benchmark]
#[bench::all(dictionary_tree().clone(), "all")]
#[bench::half(dictionary_tree().clone(), "half")]
#[bench::none(dictionary_tree().clone(), "none")]
fn bench_extract_if<K: AsBytes, V, const PREFIX_LEN: usize>(
    mut tree: TreeMap<K, V, PREFIX_LEN>,
    mode: &str,
) {
    let extracted: Vec<_> = match mode {
        "all" => tree.extract_if(.., |_, _| true).collect(),
        "half" => {
            let mut i = 0;
            tree.extract_if(.., |_, _| {
                i += 1;
                i % 2 == 0
            })
            .collect()
        },
        "none" => tree.extract_if(.., |_, _| false).collect(),
        _ => unreachable!(),
    };
    std::hint::black_box(extracted);
    std::hint::black_box(tree);
}

library_benchmark_group!(
    name = bench_modifying_group;
    benchmarks = bench_retain, bench_append, bench_split_off, bench_extract_if
);

// END

fn config() -> LibraryBenchmarkConfig {
    let mut output = OutputFormat::default();
    output.truncate_description(Some(0));
    let mut tool = Callgrind::default();
    tool.flamegraph(FlamegraphConfig::default());
    let mut c = LibraryBenchmarkConfig::default();
    c.output_format(output);
    c.tool(tool);
    c
}

main!(
    config = config();
    library_benchmark_groups = bench_clone_group,
    bench_lookup_group,
    bench_remove_group,
    bench_insert_group,
    bench_iterator_group,
    bench_modifying_group
);
