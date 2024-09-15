use blart::{
    tests_common::{
        generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, PrefixExpansion,
    },
    TreeMap,
};
use criterion::{criterion_group, Criterion, Throughput};

fn gen_group(c: &mut Criterion, group: &str, keys: Vec<Box<[u8]>>) {
    let mut group = c.benchmark_group(group);
    group.warm_up_time(std::time::Duration::from_secs(5));
    group.measurement_time(std::time::Duration::from_secs(15));
    group.throughput(Throughput::Bytes(keys.iter().map(|k| k.len() as u64).sum()));
    group.bench_function("insert", |b| {
        b.iter_batched(
            || keys.clone(),
            |keys| {
                let mut tree = TreeMap::new();
                for (idx, key) in keys.into_iter().enumerate() {
                    tree.try_insert(key, idx).unwrap();
                }
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });
}

#[inline(always)]
fn bench(c: &mut Criterion) {
    let skewed: Vec<_> = generate_keys_skewed(u8::MAX as usize).collect();
    let fixed_length: Vec<_> = generate_key_fixed_length([2; 8]).map(Box::from).collect();
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

    gen_group(c, "generated_insert/skewed", skewed);
    gen_group(c, "generated_insert/fixed_length", fixed_length);
    gen_group(c, "generated_insert/large_prefixes", large_prefixes);
}

criterion_group!(bench_generated_insert_group, bench);
