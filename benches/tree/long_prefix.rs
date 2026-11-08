use std::ffi::CString;

use blart::TreeMap;
use criterion::{BatchSize, BenchmarkGroup, Criterion, criterion_group, measurement::Measurement};
use rand::{SeedableRng, rngs::SmallRng, seq::IndexedRandom};

use crate::common::{dictionary_words, prefix_queries, range_queries, url_keys};

const NUM_SEARCHES: usize = 5_000;

fn bench_keys<M: Measurement, const PREFIX_LEN: usize>(
    group: &mut BenchmarkGroup<M>,
    keys: Vec<CString>,
) {
    let mut rng = SmallRng::seed_from_u64(69420);
    let searches: Vec<CString> = keys
        .choose_multiple(&mut rng, NUM_SEARCHES)
        .cloned()
        .collect();

    let mut tree = TreeMap::<CString, usize, PREFIX_LEN>::with_prefix_len();
    for (idx, key) in keys.iter().enumerate() {
        let _ = tree.try_insert(key.clone(), idx);
    }

    group.bench_function("insert", |b| {
        b.iter_batched(
            || keys.clone(),
            |keys| {
                let mut tree = TreeMap::<CString, usize, PREFIX_LEN>::with_prefix_len();
                for (idx, key) in keys.into_iter().enumerate() {
                    let _ = tree.try_insert(key, idx);
                }
                tree
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("prefix_insert", |b| {
        b.iter_batched(
            || keys.clone(),
            |keys| {
                let mut tree = TreeMap::<CString, usize, PREFIX_LEN>::with_prefix_len();
                for (idx, key) in keys.into_iter().enumerate() {
                    tree.prefix_insert(key, idx);
                }
                tree
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("insert_existing", |b| {
        b.iter_batched(
            || (tree.clone(), searches.clone()),
            |(mut tree, searches)| {
                for key in searches {
                    let _ = std::hint::black_box(tree.try_insert(key, 0));
                }
                tree
            },
            BatchSize::LargeInput,
        )
    });

    let ranges = range_queries(&keys, NUM_SEARCHES);
    group.bench_function("range_short", |b| {
        b.iter(|| {
            for key in &ranges {
                for entry in tree.range::<CString, _>(key..).take(4) {
                    std::hint::black_box(entry);
                }
            }
        })
    });

    let prefixes = prefix_queries(&keys, NUM_SEARCHES);
    group.bench_function("prefix_short", |b| {
        b.iter(|| {
            for prefix in &prefixes {
                for entry in tree.prefix(prefix).take(4) {
                    std::hint::black_box(entry);
                }
            }
        })
    });

    group.bench_function("get", |b| {
        b.iter(|| {
            for key in &searches {
                std::hint::black_box(tree.get(key));
            }
        })
    });
}

fn bench(c: &mut Criterion) {
    {
        let mut group = c.benchmark_group("long_prefix/urls");
        bench_keys::<_, 16>(&mut group, url_keys(20_000));
    }
    {
        let mut group = c.benchmark_group("long_prefix/dict_prefix_len_4");
        bench_keys::<_, 4>(&mut group, dictionary_words());
    }
}

criterion_group!(bench_long_prefix_group, bench);
