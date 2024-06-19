use std::{ffi::CString, time::Duration};

use blart::TreeMap;
use criterion::{measurement::Measurement, Criterion};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};

#[macro_use]
mod common;

fn bench<M: Measurement>(c: &mut Criterion<M>, prefix: &str) {
    let mut rng = StdRng::seed_from_u64(69420);
    let words = include_str!("dict.txt");
    let mut bytes = 0;
    let mut words: Vec<_> = words
        .lines()
        .map(|s| {
            let s = CString::new(s).unwrap();
            bytes += s.as_bytes_with_nul().len();
            s
        })
        .collect();
    words.dedup();
    words.sort();

    let mut searches: Vec<_> = words.choose_multiple(&mut rng, 5_000).cloned().collect();
    searches.sort();

    let mut tree: TreeMap<_, _> = words.into_iter().map(|s| (s, 0usize)).collect();

    let mut group = c.benchmark_group(format!("{prefix}"));
    group.throughput(criterion::Throughput::Bytes(bytes as u64));
    group.warm_up_time(Duration::from_secs(10));
    group.measurement_time(Duration::from_secs(30));
    group.bench_function("get", |b| {
        b.iter(|| {
            for search in &searches {
                std::hint::black_box(tree.get(search));
            }
        });
    });
}

gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
