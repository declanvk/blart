//! Instruction count benchmarks, run under callgrind with `gungraun`.

use std::{ffi::CStr, hint::black_box, ops::RangeBounds};

use blart::{AsBytes, NoPrefixesBytes, TreeMap};
use gungraun::{
    client_requests::callgrind, library_benchmark, library_benchmark_group, main, Callgrind,
    EntryPoint, LibraryBenchmarkConfig, OutputFormat,
};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};

use crate::common::{
    dense_fixed_length_key_tree, dictionary_tree, get_middle_key, sample_keys, sample_ranges,
    skewed_tree, sparse_fixed_length_key_tree, with_prefixes_tree, SAMPLE_SEED,
};

#[macro_use]
mod common;

/// The number of keys that the point operation benchmarks (get, insert, remove)
/// work on.
const NUM_KEYS: usize = 2048;

/// The number of iterators that the prefix and range benchmarks create.
const NUM_ITERATORS: usize = 256;

/// Run `f` with callgrind instrumentation and event collection turned on.
///
/// Both are off at the start of the benchmark (see `config`), and these client
/// requests turn them on and off around the measured code.
macro_rules! measure {
    ($e:expr) => {{
        callgrind::start_instrumentation();
        callgrind::toggle_collect();
        let result = black_box($e);
        callgrind::toggle_collect();
        callgrind::stop_instrumentation();
        result
    }};
}

/// Clone `tree` and remove a random sample of `num_keys` keys from the clone.
///
/// Returns the smaller tree and the removed keys, so that a benchmark can
/// insert them again or look them up and miss.
fn remove_sample<K: AsBytes + Clone, V: Clone>(
    tree: &TreeMap<K, V>,
    num_keys: usize,
) -> (TreeMap<K, V>, Vec<K>) {
    let keys: Vec<K> = sample_keys(tree, num_keys).into_iter().cloned().collect();
    let mut tree = tree.clone();
    for key in &keys {
        tree.remove(key).unwrap();
    }
    (tree, keys)
}

/// A random sample of `num_keys` keys of `tree`, cloned.
fn owned_sample<K: AsBytes + Clone, V>(tree: &TreeMap<K, V>, num_keys: usize) -> Vec<K> {
    sample_keys(tree, num_keys).into_iter().cloned().collect()
}

// CLONE

#[library_benchmark]
#[bench::dictionary(dictionary_tree())]
#[bench::dense_fixed_length(dense_fixed_length_key_tree())]
#[bench::sparse_fixed_length(sparse_fixed_length_key_tree())]
#[bench::skewed(skewed_tree())]
#[bench::with_prefixes(with_prefixes_tree())]
fn bench_clone<K: AsBytes + Clone, V: Clone>(tree: &TreeMap<K, V>) -> TreeMap<K, V> {
    measure!(tree.clone())
}

library_benchmark_group!(name = bench_clone_group; benchmarks = bench_clone);

// LOOKUP

#[library_benchmark]
#[bench::dictionary(dictionary_tree(), sample_keys(dictionary_tree(), NUM_KEYS))]
#[bench::dense_fixed_length(
    dense_fixed_length_key_tree(),
    sample_keys(dense_fixed_length_key_tree(), NUM_KEYS)
)]
#[bench::sparse_fixed_length(
    sparse_fixed_length_key_tree(),
    sample_keys(sparse_fixed_length_key_tree(), NUM_KEYS)
)]
#[bench::skewed(skewed_tree(), sample_keys(skewed_tree(), NUM_KEYS))]
#[bench::with_prefixes(with_prefixes_tree(), sample_keys(with_prefixes_tree(), NUM_KEYS))]
fn bench_get_hit<K: AsBytes, V>(tree: &TreeMap<K, V>, keys: Vec<&K>) {
    measure!({
        for key in &keys {
            black_box(tree.get(*key).unwrap());
        }
    })
}

#[library_benchmark]
#[bench::dictionary(remove_sample(dictionary_tree(), NUM_KEYS))]
#[bench::dense_fixed_length(remove_sample(dense_fixed_length_key_tree(), NUM_KEYS))]
#[bench::sparse_fixed_length(remove_sample(sparse_fixed_length_key_tree(), NUM_KEYS))]
#[bench::skewed(remove_sample(skewed_tree(), NUM_KEYS))]
#[bench::with_prefixes(remove_sample(with_prefixes_tree(), NUM_KEYS))]
fn bench_get_miss<K: AsBytes, V>((tree, keys): (TreeMap<K, V>, Vec<K>)) {
    measure!({
        for key in &keys {
            assert!(black_box(tree.get(key)).is_none());
        }
    })
}

library_benchmark_group!(name = bench_lookup_group; benchmarks = bench_get_hit, bench_get_miss);

// REMOVE

#[library_benchmark]
#[bench::dictionary(dictionary_tree().clone(), sample_keys(dictionary_tree(), NUM_KEYS))]
#[bench::dense_fixed_length(
    dense_fixed_length_key_tree().clone(),
    sample_keys(dense_fixed_length_key_tree(), NUM_KEYS)
)]
#[bench::sparse_fixed_length(
    sparse_fixed_length_key_tree().clone(),
    sample_keys(sparse_fixed_length_key_tree(), NUM_KEYS)
)]
#[bench::skewed(skewed_tree().clone(), sample_keys(skewed_tree(), NUM_KEYS))]
#[bench::with_prefixes(with_prefixes_tree().clone(), sample_keys(with_prefixes_tree(), NUM_KEYS))]
fn bench_remove<K: AsBytes, V>(mut tree: TreeMap<K, V>, keys: Vec<&K>) -> TreeMap<K, V> {
    measure!({
        for key in &keys {
            black_box(tree.remove(*key).unwrap());
        }
    });
    tree
}

library_benchmark_group!(name = bench_remove_group; benchmarks = bench_remove);

// INSERT

// Insert keys that are not in the tree.
#[library_benchmark]
#[bench::dictionary(remove_sample(dictionary_tree(), NUM_KEYS))]
#[bench::dense_fixed_length(remove_sample(dense_fixed_length_key_tree(), NUM_KEYS))]
#[bench::sparse_fixed_length(remove_sample(sparse_fixed_length_key_tree(), NUM_KEYS))]
#[bench::skewed(remove_sample(skewed_tree(), NUM_KEYS))]
#[bench::with_prefixes(remove_sample(with_prefixes_tree(), NUM_KEYS))]
fn bench_insert_new<K: AsBytes, V: Default>(
    (mut tree, keys): (TreeMap<K, V>, Vec<K>),
) -> TreeMap<K, V> {
    measure!({
        for key in keys {
            assert!(black_box(tree.try_insert(key, V::default()).unwrap()).is_none());
        }
    });
    tree
}

// Insert keys that are already in the tree, replacing the values.
#[library_benchmark]
#[bench::dictionary(dictionary_tree().clone(), owned_sample(dictionary_tree(), NUM_KEYS))]
#[bench::dense_fixed_length(
    dense_fixed_length_key_tree().clone(),
    owned_sample(dense_fixed_length_key_tree(), NUM_KEYS)
)]
#[bench::sparse_fixed_length(
    sparse_fixed_length_key_tree().clone(),
    owned_sample(sparse_fixed_length_key_tree(), NUM_KEYS)
)]
#[bench::skewed(skewed_tree().clone(), owned_sample(skewed_tree(), NUM_KEYS))]
#[bench::with_prefixes(with_prefixes_tree().clone(), owned_sample(with_prefixes_tree(), NUM_KEYS))]
fn bench_insert_existing<K: AsBytes, V: Default>(
    mut tree: TreeMap<K, V>,
    keys: Vec<K>,
) -> TreeMap<K, V> {
    measure!({
        for key in keys {
            assert!(black_box(tree.try_insert(key, V::default()).unwrap()).is_some());
        }
    });
    tree
}

// This seems like a tricky and possibly unsafe thing to do. We can statically
// guarantee that there are no prefixes amongst the keys that are currently in
// `tree`, since they all succeeded their insert operations.
//
// However, we can only guarantee that `TreeMap<TransparentNoPrefixesBytes<K>,
// V>` is safe so long as no other code can construct a
// `TransparentNoPrefixesBytes<K>` outside the set of keys we returned from this
// function.
//
// The reason we want this is so we can benchmark bulk insert for types that are
// not directly implementing `NoPrefixesBytes`.
fn bulk_insert_setup<K: AsBytes + Clone, V: Clone>(
    tree: &TreeMap<K, V>,
    shuffle: bool,
) -> Vec<(impl NoPrefixesBytes, V)> {
    #[repr(transparent)]
    struct TransparentNoPrefixesBytes<T>(T);

    impl<T> AsBytes for TransparentNoPrefixesBytes<T>
    where
        T: AsBytes,
    {
        fn as_bytes(&self) -> &[u8] {
            self.0.as_bytes()
        }
    }
    unsafe impl<T> NoPrefixesBytes for TransparentNoPrefixesBytes<T> where T: AsBytes {}

    let mut entries: Vec<(K, V)> = tree.clone().into_iter().collect();

    for (a, b) in entries.iter().zip(entries.iter().skip(1)) {
        if a.0.as_bytes().starts_with(b.0.as_bytes()) {
            panic!("found prefix {:?} {:?}", a.0.as_bytes(), b.0.as_bytes());
        }
    }

    if shuffle {
        entries.shuffle(&mut StdRng::seed_from_u64(SAMPLE_SEED));
    }

    unsafe { core::mem::transmute::<_, Vec<(TransparentNoPrefixesBytes<K>, V)>>(entries) }
}

#[library_benchmark]
#[bench::dictionary_sorted(bulk_insert_setup(dictionary_tree(), false))]
#[bench::dictionary_shuffled(bulk_insert_setup(dictionary_tree(), true))]
#[bench::dense_fixed_length_sorted(bulk_insert_setup(dense_fixed_length_key_tree(), false))]
#[bench::dense_fixed_length_shuffled(bulk_insert_setup(dense_fixed_length_key_tree(), true))]
#[bench::sparse_fixed_length_sorted(bulk_insert_setup(sparse_fixed_length_key_tree(), false))]
#[bench::sparse_fixed_length_shuffled(bulk_insert_setup(sparse_fixed_length_key_tree(), true))]
#[bench::skewed_sorted(bulk_insert_setup(skewed_tree(), false))]
#[bench::skewed_shuffled(bulk_insert_setup(skewed_tree(), true))]
#[bench::with_prefixes_sorted(bulk_insert_setup(with_prefixes_tree(), false))]
#[bench::with_prefixes_shuffled(bulk_insert_setup(with_prefixes_tree(), true))]
fn bench_from_iter<K: NoPrefixesBytes, V>(entries: Vec<(K, V)>) -> TreeMap<K, V> {
    measure!(TreeMap::from_iter(entries))
}

#[library_benchmark]
#[bench::dictionary_sorted(bulk_insert_setup(dictionary_tree(), false))]
#[bench::dictionary_shuffled(bulk_insert_setup(dictionary_tree(), true))]
#[bench::dense_fixed_length_sorted(bulk_insert_setup(dense_fixed_length_key_tree(), false))]
#[bench::dense_fixed_length_shuffled(bulk_insert_setup(dense_fixed_length_key_tree(), true))]
#[bench::sparse_fixed_length_sorted(bulk_insert_setup(sparse_fixed_length_key_tree(), false))]
#[bench::sparse_fixed_length_shuffled(bulk_insert_setup(sparse_fixed_length_key_tree(), true))]
#[bench::skewed_sorted(bulk_insert_setup(skewed_tree(), false))]
#[bench::skewed_shuffled(bulk_insert_setup(skewed_tree(), true))]
#[bench::with_prefixes_sorted(bulk_insert_setup(with_prefixes_tree(), false))]
#[bench::with_prefixes_shuffled(bulk_insert_setup(with_prefixes_tree(), true))]
fn bench_from_vec<K: NoPrefixesBytes, V>(entries: Vec<(K, V)>) -> TreeMap<K, V> {
    measure!(TreeMap::from(entries))
}

library_benchmark_group!(
    name = bench_insert_group;
    benchmarks = bench_insert_new, bench_insert_existing, bench_from_vec, bench_from_iter
);

// ITERATORS

#[library_benchmark]
#[bench::dictionary(dictionary_tree())]
#[bench::dense_fixed_length(dense_fixed_length_key_tree())]
#[bench::sparse_fixed_length(sparse_fixed_length_key_tree())]
#[bench::skewed(skewed_tree())]
#[bench::with_prefixes(with_prefixes_tree())]
fn bench_iter<K: AsBytes, V>(tree: &TreeMap<K, V>) {
    measure!(assert_eq!(tree.iter().map(black_box).count(), tree.len()))
}

#[library_benchmark]
#[bench::dictionary(dictionary_tree())]
fn bench_iter_rev<K: AsBytes, V>(tree: &TreeMap<K, V>) {
    measure!(assert_eq!(
        tree.iter().rev().map(black_box).count(),
        tree.len()
    ))
}

/// For a sample of keys, take the first `numerator / denominator` of the key
/// bytes.
fn key_prefixes<K: AsBytes, V>(
    tree: &TreeMap<K, V>,
    numerator: usize,
    denominator: usize,
) -> Vec<&[u8]> {
    sample_keys(tree, NUM_ITERATORS)
        .into_iter()
        .map(|key| {
            let bytes = key.as_bytes();
            &bytes[..bytes.len() * numerator / denominator]
        })
        .collect()
}

// Run a prefix iterator for each of `prefixes`.
//
// The `full_key` cases use whole keys as prefixes, so each iterator finds
// exactly one entry and the cost is mostly finding the start. The
// `half_key` cases each find a group of entries.
#[library_benchmark]
#[bench::dictionary_full_key(dictionary_tree(), key_prefixes(dictionary_tree(), 1, 1))]
#[bench::dictionary_half_key(dictionary_tree(), key_prefixes(dictionary_tree(), 1, 2))]
#[bench::dense_fixed_length_half_key(
    dense_fixed_length_key_tree(),
    key_prefixes(dense_fixed_length_key_tree(), 1, 2)
)]
#[bench::sparse_fixed_length_full_key(
    sparse_fixed_length_key_tree(),
    key_prefixes(sparse_fixed_length_key_tree(), 1, 1)
)]
#[bench::sparse_fixed_length_half_key(
    sparse_fixed_length_key_tree(),
    key_prefixes(sparse_fixed_length_key_tree(), 1, 2)
)]
#[bench::with_prefixes_full_key(with_prefixes_tree(), key_prefixes(with_prefixes_tree(), 1, 1))]
#[bench::with_prefixes_half_key(with_prefixes_tree(), key_prefixes(with_prefixes_tree(), 1, 2))]
fn bench_prefix_iter<K: AsBytes, V>(tree: &TreeMap<K, V>, prefixes: Vec<&[u8]>) -> usize {
    measure!({
        let mut total = 0;
        for prefix in &prefixes {
            total += tree.prefix(prefix).map(black_box).count();
        }
        assert!(total >= prefixes.len());
        total
    })
}

/// Words to search for in the dictionary, with and without spelling mistakes.
const FUZZY_SEARCHES: &[&CStr] = &[
    c"house",
    c"houze",
    c"headphones",
    c"headpones",
    c"unavoided",
    c"unavoid",
    c"tree",
    c"tre",
    c"benchmark",
    c"bencmark",
];

#[library_benchmark]
#[bench::distance_1(dictionary_tree(), 1)]
#[bench::distance_2(dictionary_tree(), 2)]
#[bench::distance_3(dictionary_tree(), 3)]
fn bench_fuzzy_iter<K: AsBytes + std::borrow::Borrow<CStr>, V>(
    tree: &TreeMap<K, V>,
    edit_distance: usize,
) -> usize {
    measure!({
        let mut total = 0;
        for search in FUZZY_SEARCHES {
            total += tree.fuzzy(*search, edit_distance).map(black_box).count();
        }
        total
    })
}

#[library_benchmark]
#[bench::full(dictionary_tree(), ..)]
#[bench::middle_third(dictionary_tree(), get_middle_key(dictionary_tree(), 1, 2)..get_middle_key(dictionary_tree(), 2, 1))]
fn bench_range_iter<K: AsBytes, V, R: RangeBounds<K>>(tree: &TreeMap<K, V>, range: R) -> usize {
    measure!(tree.range(range).map(black_box).count())
}

// Run many short range iterators, each over 16 entries.
//
// The cost is split between finding the ends of the range and walking the
// entries in it.
#[library_benchmark]
#[bench::dictionary(dictionary_tree(), sample_ranges(dictionary_tree(), NUM_ITERATORS, 16))]
#[bench::dense_fixed_length(
    dense_fixed_length_key_tree(),
    sample_ranges(dense_fixed_length_key_tree(), NUM_ITERATORS, 16)
)]
#[bench::sparse_fixed_length(
    sparse_fixed_length_key_tree(),
    sample_ranges(sparse_fixed_length_key_tree(), NUM_ITERATORS, 16)
)]
#[bench::skewed(skewed_tree(), sample_ranges(skewed_tree(), NUM_ITERATORS, 16))]
#[bench::with_prefixes(
    with_prefixes_tree(),
    sample_ranges(with_prefixes_tree(), NUM_ITERATORS, 16)
)]
fn bench_short_range_iter<K: AsBytes, V>(tree: &TreeMap<K, V>, ranges: Vec<(&K, &K)>) -> usize {
    measure!({
        let mut total = 0;
        for (start, end) in &ranges {
            total += tree.range::<K, _>(*start..*end).map(black_box).count();
        }
        assert_eq!(total, ranges.len() * 16);
        total
    })
}

library_benchmark_group!(
    name = bench_iterator_group;
    benchmarks = bench_iter, bench_iter_rev, bench_prefix_iter, bench_fuzzy_iter, bench_range_iter,
        bench_short_range_iter
);

// MODIFYING

#[library_benchmark]
#[bench::all(dictionary_tree().clone(), "all")]
#[bench::half(dictionary_tree().clone(), "half")]
#[bench::none(dictionary_tree().clone(), "none")]
fn bench_retain<K: AsBytes, V>(mut tree: TreeMap<K, V>, mode: &str) -> TreeMap<K, V> {
    measure!({
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
        tree
    })
}

fn u128_tree(range: std::ops::Range<u128>) -> TreeMap<u128, usize> {
    range.map(|i| (i, i as usize)).collect()
}

#[library_benchmark]
#[bench::no_overlap(u128_tree(0..1024), u128_tree(1024..2048))]
#[bench::overlap(u128_tree(0..1024), u128_tree(512..1536))]
fn bench_append(
    mut tree1: TreeMap<u128, usize>,
    mut tree2: TreeMap<u128, usize>,
) -> (TreeMap<u128, usize>, TreeMap<u128, usize>) {
    measure!({
        tree1.append(&mut tree2);
        (tree1, tree2)
    })
}

/// The number of pieces that `bench_split_off` cuts each tree into.
const NUM_SPLIT_PIECES: usize = 16;

/// Keys that cut `tree` into `NUM_SPLIT_PIECES` pieces of equal size, in
/// descending order.
fn split_points<K: AsBytes + Clone, V>(tree: &TreeMap<K, V>) -> Vec<K> {
    let keys: Vec<&K> = tree.keys().collect();
    (1..NUM_SPLIT_PIECES)
        .rev()
        .map(|i| keys[i * keys.len() / NUM_SPLIT_PIECES].clone())
        .collect()
}

// Cut a tree into pieces by calling `split_off` at several points, from the
// last to the first.
//
// Splitting at several points means the result does not depend on the shape
// of the tree around one split key.
#[library_benchmark]
#[bench::dictionary(dictionary_tree().clone(), split_points(dictionary_tree()))]
#[bench::dense_fixed_length(
    dense_fixed_length_key_tree().clone(),
    split_points(dense_fixed_length_key_tree())
)]
#[bench::sparse_fixed_length(
    sparse_fixed_length_key_tree().clone(),
    split_points(sparse_fixed_length_key_tree())
)]
#[bench::skewed(skewed_tree().clone(), split_points(skewed_tree()))]
#[bench::with_prefixes(with_prefixes_tree().clone(), split_points(with_prefixes_tree()))]
fn bench_split_off<K, V>(mut tree: TreeMap<K, V>, split_points: Vec<K>) -> Vec<TreeMap<K, V>>
where
    K: AsBytes + Clone,
    V: Clone,
{
    let mut pieces = Vec::with_capacity(split_points.len() + 1);
    measure!({
        for key in &split_points {
            pieces.push(tree.split_off(key));
        }
    });
    pieces.push(tree);
    pieces
}

#[library_benchmark]
#[bench::all(dictionary_tree().clone(), "all")]
#[bench::half(dictionary_tree().clone(), "half")]
#[bench::none(dictionary_tree().clone(), "none")]
fn bench_extract_if<K: AsBytes, V>(
    mut tree: TreeMap<K, V>,
    mode: &str,
) -> (Vec<(K, V)>, TreeMap<K, V>) {
    measure!({
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
        (extracted, tree)
    })
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
    // We're disabling the entry point because we want to have precise control over when
    // *collection* and *instrumentation* start. Callgrind separates collection (whether events are
    // counted) from instrumentation (whether code runs under the simulator at all). Collection
    // requires instrumentation to work, otherwise we would use the default `EntryPoint` and just
    // append the `--instr-atstart=no`.
    //
    // One effect of this is that the simulated cache doesn't see setup any more, so each
    // `measure!` starts with a cold cache, which affects the L1/LL/RAM benchmark numbers.
    //
    // Reference:
    // <https://gungraun.github.io/gungraun/latest/html/benchmarks/library_benchmarks/custom_entry_point.html>
    tool.entry_point(EntryPoint::None)
        .args(["--collect-atstart=no", "--instr-atstart=no"]);
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
