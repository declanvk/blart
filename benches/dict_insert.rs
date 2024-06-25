use std::{ffi::CString, time::Duration};

use blart::TreeMap;
use criterion::{measurement::Measurement, Criterion};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};

#[macro_use]
mod common;

fn insert(words: Vec<CString>) -> TreeMap<CString, usize> {
    let mut art = TreeMap::new();
    for (idx, word) in words.into_iter().enumerate() {
        art.insert(word, idx);
    }
    art
}

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

    let mut rev_words = words.clone();
    rev_words.reverse();

    let mut rand_words = words.clone();
    rand_words.shuffle(&mut rng);

    let mut part_words: Vec<_> = words.choose_multiple(&mut rng, 50_000).cloned().collect();
    part_words.sort();

    let mut rev_part_words = part_words.clone();
    rev_part_words.reverse();

    let mut rand_part_words = part_words.clone();
    rand_part_words.shuffle(&mut rng);

    let part_bytes: usize = part_words.iter().map(|w| w.as_bytes_with_nul().len()).sum();

    {
        let mut group = c.benchmark_group(format!("{prefix}/words/full"));
        group.throughput(criterion::Throughput::Bytes(bytes as u64));
        group.warm_up_time(Duration::from_secs(10));
        group.measurement_time(Duration::from_secs(30));
        group.bench_function("insert/asc", |b| {
            b.iter_batched(|| words.clone(), insert, criterion::BatchSize::SmallInput)
        });
        group.bench_function("insert/desc", |b| {
            b.iter_batched(
                || rev_words.clone(),
                insert,
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_function("insert/rand", |b| {
            b.iter_batched(
                || rand_words.clone(),
                insert,
                criterion::BatchSize::SmallInput,
            )
        });
    }
    {
        let mut group = c.benchmark_group(format!("{prefix}/words/part"));
        group.throughput(criterion::Throughput::Bytes(part_bytes as u64));
        group.warm_up_time(Duration::from_secs(10));
        group.measurement_time(Duration::from_secs(30));
        group.bench_function("insert/asc", |b| {
            b.iter_batched(
                || part_words.clone(),
                insert,
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_function("insert/desc", |b| {
            b.iter_batched(
                || rev_part_words.clone(),
                insert,
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_function("insert/rand", |b| {
            b.iter_batched(
                || rand_part_words.clone(),
                insert,
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
