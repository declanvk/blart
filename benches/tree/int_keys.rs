use std::collections::BTreeMap;

use blart::TreeMap;
use criterion::{BatchSize, Criterion, criterion_group};
use rand::{Rng, SeedableRng, rngs::StdRng, seq::IndexedRandom};

const NUM_KEYS: u64 = 100_000;
const NUM_SEARCHES: usize = 5_000;

fn bench_keys(c: &mut Criterion, group_name: &str, keys: Vec<u64>, rng: &mut StdRng) {
    let searches: Vec<u64> = keys.choose_multiple(rng, NUM_SEARCHES).copied().collect();

    let art: TreeMap<u64, u64> = keys.iter().map(|k| (*k, *k)).collect();
    let btree: BTreeMap<u64, u64> = keys.iter().map(|k| (*k, *k)).collect();

    let mut group = c.benchmark_group(group_name);

    group.bench_function("blart/insert", |b| {
        b.iter_batched(
            || keys.clone(),
            |keys| {
                let mut tree = TreeMap::new();
                for k in keys {
                    tree.insert(k, k);
                }
                tree
            },
            BatchSize::SmallInput,
        )
    });
    group.bench_function("btree/insert", |b| {
        b.iter_batched(
            || keys.clone(),
            |keys| {
                let mut tree = BTreeMap::new();
                for k in keys {
                    tree.insert(k, k);
                }
                tree
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("blart/get", |b| {
        b.iter(|| {
            for k in &searches {
                std::hint::black_box(art.get(k));
            }
        })
    });
    group.bench_function("btree/get", |b| {
        b.iter(|| {
            for k in &searches {
                std::hint::black_box(btree.get(k));
            }
        })
    });

    group.bench_function("blart/remove", |b| {
        b.iter_batched(
            || art.clone(),
            |mut tree| {
                for k in &searches {
                    std::hint::black_box(tree.remove(k));
                }
                tree
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("btree/remove", |b| {
        b.iter_batched(
            || btree.clone(),
            |mut tree| {
                for k in &searches {
                    std::hint::black_box(tree.remove(k));
                }
                tree
            },
            BatchSize::LargeInput,
        )
    });
}

fn bench(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(69420);

    let sequential: Vec<u64> = (0..NUM_KEYS).collect();
    bench_keys(c, "int_keys/sequential", sequential, &mut rng);

    let mut random: Vec<u64> = (0..NUM_KEYS).map(|_| rng.random()).collect();
    random.sort_unstable();
    random.dedup();
    // Insert in random order, not sorted order
    rand::seq::SliceRandom::shuffle(random.as_mut_slice(), &mut rng);
    bench_keys(c, "int_keys/random", random, &mut rng);
}

criterion_group!(bench_int_keys_group, bench);
