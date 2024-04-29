use std::ffi::CString;

use blart::{
    tests_common::{
        generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, PrefixExpansion,
    },
    AsBytes, TreeMap,
};
use criterion::{measurement::Measurement, Criterion, Throughput};

fn gen_group<M: Measurement, K: AsBytes + Clone>(c: &mut Criterion<M>, group: String, mut keys: Vec<K>) {
    let bytes = keys.iter().map(|k| k.as_bytes().len() as u64).sum();
    let mut entries: Vec<_> = keys.into_iter().map(|k| (k, 0usize)).collect();

    let mut group = c.benchmark_group(group);
    group.warm_up_time(std::time::Duration::from_secs(5));
    group.measurement_time(std::time::Duration::from_secs(20));
    group.throughput(Throughput::Bytes(bytes));

    group.bench_function("bulk", |b| {
        b.iter_batched(
            || entries.clone(),
            |entries| TreeMap::bulk_insert(entries),
            criterion::BatchSize::SmallInput,
        )
    });

    entries.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    group.bench_function("bulk_unchecked", |b| {
        b.iter_batched(
            || entries.clone(),
            |entries| TreeMap::bulk_insert_unchecked(entries),
            criterion::BatchSize::SmallInput,
        )
    });
}

#[inline(always)]
fn bench<M: Measurement>(c: &mut Criterion<M>, prefix: &str) {
    let skewed: Vec<_> = generate_keys_skewed(u8::MAX as usize).collect();
    let fixed_length: Vec<_> = generate_key_fixed_length([2; 8]).collect();
    let large_prefixes: Vec<_> = generate_key_with_prefix(
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
    )
    .collect();

    let words = include_str!("dict.txt");
    let mut dict: Vec<_> = words.lines().map(|s| CString::new(s).unwrap()).collect();

    gen_group(c, format!("{prefix}/skewed"), skewed.clone());
    gen_group(c, format!("{prefix}/fixed_length"), fixed_length.clone());
    gen_group(c, format!("{prefix}/large_prefixes"), large_prefixes.clone());
    gen_group(c, format!("{prefix}/dict"), dict.clone());
}

blart::gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
