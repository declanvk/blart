use blart::{
    BytesMapping, FixedKeyHeader, Mapped, NoPrefixesBytes, NodeHeader, RawTreeMap, ToUBE,
    VariableKeyHeader,
};
use criterion::{measurement::Measurement, Criterion};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};

#[macro_use]
mod common;

fn gen_group<M, K, const NUM_PREFIX_BYTES: usize, H>(
    c: &mut Criterion<M>,
    group: String,
    keys: Vec<Mapped<ToUBE<K>>>,
) where
    M: Measurement,
    H: NodeHeader<NUM_PREFIX_BYTES>,
    ToUBE<K>: BytesMapping,
    Mapped<ToUBE<K>>: Copy + Clone + NoPrefixesBytes,
{
    let mut rng = StdRng::seed_from_u64(69420);

    let mut rand_keys: Vec<_> = keys
        .choose_multiple(&mut rng, keys.len() / 4)
        .cloned()
        .collect();
    rand_keys.shuffle(&mut rng);

    let mut group = c.benchmark_group(group);
    group.warm_up_time(std::time::Duration::from_secs(5));
    group.measurement_time(std::time::Duration::from_secs(15));

    group.bench_function("insert/asc", |b| {
        b.iter_batched(
            || keys.clone(),
            |keys| {
                let mut tree = RawTreeMap::<_, _, NUM_PREFIX_BYTES, H>::new();
                for k in keys.into_iter() {
                    tree.insert(k, k);
                }
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });
    group.bench_function("insert/desc", |b| {
        b.iter_batched(
            || keys.clone(),
            |keys| {
                let mut tree = RawTreeMap::<_, _, NUM_PREFIX_BYTES, H>::new();
                for k in keys.into_iter().rev() {
                    tree.insert(k, k);
                }
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });
    group.bench_function("insert/rand", |b| {
        b.iter_batched(
            || rand_keys.clone(),
            |rand_keys| {
                let mut tree = RawTreeMap::<_, _, NUM_PREFIX_BYTES, H>::new();
                for k in rand_keys.into_iter() {
                    tree.insert(k, k);
                }
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });

    let mut tree = RawTreeMap::<_, _, NUM_PREFIX_BYTES, H>::new();
    for k in keys.iter().copied() {
        tree.insert(k, k);
    }

    let mut rand_tree = RawTreeMap::<_, _, NUM_PREFIX_BYTES, H>::new();
    for k in rand_keys.iter().copied() {
        rand_tree.insert(k, k);
    }

    group.bench_function("get/hit", |b| {
        b.iter(|| {
            for k in keys.iter() {
                std::hint::black_box(tree.get(k));
            }
        })
    });

    group.bench_function("get/miss", |b| {
        b.iter(|| {
            for k in keys.iter() {
                std::hint::black_box(rand_tree.get(k));
            }
        })
    });
}

#[inline(always)]
fn bench<M: Measurement>(c: &mut Criterion<M>, prefix: &str) {
    gen_group::<_, _, 8, FixedKeyHeader<8, u64>>(
        c,
        format!("{prefix}/FixedKeyHeader/u64"),
        (0..4_194_304u64)
            .map(|k| Mapped::<ToUBE<u64>>::new(k))
            .collect(),
    );
    gen_group::<_, _, 8, VariableKeyHeader<8>>(
        c,
        format!("{prefix}/VariableKeyHeader/u64"),
        (0..4_194_304u64)
            .map(|k| Mapped::<ToUBE<u64>>::new(k))
            .collect(),
    );

    gen_group::<_, _, 4, FixedKeyHeader<4, u32>>(
        c,
        format!("{prefix}/FixedKeyHeader/u32"),
        (0..4_194_304u32)
            .map(|k| Mapped::<ToUBE<u32>>::new(k))
            .collect(),
    );
    gen_group::<_, _, 4, VariableKeyHeader<4>>(
        c,
        format!("{prefix}/VariableKeyHeader/u32"),
        (0..4_194_304u32)
            .map(|k| Mapped::<ToUBE<u32>>::new(k))
            .collect(),
    );

    gen_group::<_, _, 2, FixedKeyHeader<2, u16>>(
        c,
        format!("{prefix}/FixedKeyHeader/u16"),
        (0..32_768u16)
            .map(|k| Mapped::<ToUBE<u16>>::new(k))
            .collect(),
    );
    gen_group::<_, _, 2, VariableKeyHeader<2>>(
        c,
        format!("{prefix}/VariableKeyHeader/u16"),
        (0..32_768u16)
            .map(|k| Mapped::<ToUBE<u16>>::new(k))
            .collect(),
    );
}

gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
