use std::time::Duration;

use blart::{
    testing::{
        generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, PrefixExpansion,
    },
    TreeMap,
};
use criterion::{criterion_group, measurement::Measurement, BenchmarkGroup, Criterion, Throughput};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};

fn run_benchmarks<M: Measurement>(
    group: &mut BenchmarkGroup<M>,
    key_vec: &[Box<[u8]>],
    map: &TreeMap<Box<[u8]>, usize>,
) {
    // Look up every key, in a random order, so the result does not depend on
    // the path to one particular key.
    let mut search_keys: Vec<&[u8]> = key_vec.iter().map(AsRef::as_ref).collect();
    search_keys.shuffle(&mut StdRng::seed_from_u64(69420));
    group.throughput(Throughput::Elements(search_keys.len() as u64));
    group.bench_function("search/all_keys", |b| {
        b.iter(|| {
            for key in &search_keys {
                std::hint::black_box(map.get(*key).unwrap());
            }
        })
    });
    group.throughput(Throughput::Elements(1));
    group.bench_function("minimum", |b| b.iter(|| map.first_key_value().unwrap()));
    group.bench_function("maximum", |b| b.iter(|| map.last_key_value().unwrap()));

    // TODO(#3): Add more benchmarks for:
    //   - insert new keys into:
    //     - an empty tree
    //     - a tree tree that already contains the given key
    //     - a tree node that is full and will need to grow
}

fn setup_tree_run_benches_cleanup(
    c: &mut Criterion,
    keys: impl Iterator<Item = Box<[u8]>>,
    group_name: &str,
) {
    let keys: Vec<_> = keys.collect();

    let mut tree = TreeMap::new();

    for (idx, key) in keys.iter().enumerate() {
        let _ = tree.try_insert(key.clone(), idx).unwrap();
    }

    {
        let mut group = c.benchmark_group(group_name);
        group.warm_up_time(Duration::from_secs(5));
        group.measurement_time(Duration::from_secs(15));
        run_benchmarks(&mut group, keys.as_ref(), &tree);
    }
}

fn bench(c: &mut Criterion) {
    // number of keys = 255
    setup_tree_run_benches_cleanup(
        c,
        generate_keys_skewed(u8::MAX as usize),
        "generated_get/skewed",
    );
    // number of keys = 6561 (3^8)
    setup_tree_run_benches_cleanup(
        c,
        generate_key_fixed_length([2; 8]).map(Box::from),
        "generated_get/fixed_length",
    );
    // number of keys = 6561 (3^8), with two prefixes expanded
    setup_tree_run_benches_cleanup(
        c,
        generate_key_with_prefix(
            [2; 8],
            [
                PrefixExpansion {
                    base_index: 1,
                    expanded_length: 12,
                },
                PrefixExpansion {
                    base_index: 5,
                    expanded_length: 8,
                },
            ],
        ),
        "generated_get/large_prefixes",
    );
}

criterion_group!(bench_generated_get_group, bench);
