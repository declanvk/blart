use std::ffi::CString;

use blart::TreeMap;
use criterion::{criterion_group, BatchSize, Criterion};
use rand::{rngs::StdRng, seq::IndexedRandom, SeedableRng};

fn bench(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(69420);
    let words = include_str!("../data/medium-dict.txt");
    let mut words: Vec<_> = words.lines().map(|s| CString::new(s).unwrap()).collect();
    words.dedup();
    words.sort();

    let mut removals: Vec<_> = words.choose_multiple(&mut rng, 5_000).cloned().collect();
    removals.sort();

    let tree: TreeMap<_, _> = words.into_iter().map(|s| (s, 0usize)).collect();

    let mut group = c.benchmark_group("dict");
    group.bench_function("remove", |b| {
        b.iter_batched(
            || tree.clone(),
            |mut tree| {
                for word in &removals {
                    std::hint::black_box(tree.remove(word));
                }
                tree
            },
            BatchSize::LargeInput,
        );
    });
}

criterion_group!(bench_dict_remove_group, bench);
