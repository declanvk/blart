use blart::{
    tests_common::{
        generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, PrefixExpansion,
    },
    TreeMap,
};
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use paste::paste;

type Measurement = criterion_perf_events::Perf;

fn gen_group(c: &mut Criterion<Measurement>, group: String, keys: Vec<Box<[u8]>>) {
    let mut group = c.benchmark_group(group);
    group.warm_up_time(std::time::Duration::from_secs(5));
    group.measurement_time(std::time::Duration::from_secs(10));
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
fn bench(c: &mut Criterion<Measurement>, prefix: &str) {
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

    gen_group(c, format!("{prefix}/skewed"), skewed);
    gen_group(c, format!("{prefix}/fixed_length"), fixed_length);
    gen_group(c, format!("{prefix}/large_prefixes"), large_prefixes);
}

macro_rules! benches {
    ($bench:ident, $(($target:ident, $event:path)),+) => {
        paste! {
            $(
                pub fn $target(c: &mut Criterion<Measurement>) {
                    $bench(c, stringify!($target));
                }

                criterion_group! {
                    name = [<group_ $target>];
                    config = Criterion::default()
                    .with_measurement(
                        criterion_perf_events::Perf::new(
                            perfcnt::linux::PerfCounterBuilderLinux::from_hardware_event($event),
                        )
                    );
                    targets = $target
                }
            )+
        }

        paste! {
            criterion_main!($([<group_ $target>]),+);
        }
    };
}

benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    ) /* (cache_references, perfcnt::linux::HardwareEventType::CacheReferences),
       * (cache_misses, perfcnt::linux::HardwareEventType::CacheMisses),
       * (branch_instructions, perfcnt::linux::HardwareEventType::BranchInstructions),
       * (branch_misses, perfcnt::linux::HardwareEventType::BranchMisses) */
);
