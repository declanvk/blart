use blart::{
    tests_common::{
        generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, PrefixExpansion,
    },
    TreeMap,
};
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion};

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
type Measurement = criterion_perf_events::Perf;
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
type Measurement = criterion::measurement::WallTime;

fn run_benchmarks(
    group: &mut BenchmarkGroup<Measurement>,
    key_vec: &[Box<[u8]>],
    map: &TreeMap<usize>,
) {
    let (first_key, middle_key, last_key) = (
        key_vec[0].as_ref(),
        key_vec[key_vec.len() / 2].as_ref(),
        key_vec[key_vec.len() - 1].as_ref(),
    );
    group.bench_function("search/first_key", |b| {
        b.iter(|| map.get(first_key).unwrap())
    });
    group.bench_function("search/middle_key", |b| {
        b.iter(|| map.get(middle_key).unwrap())
    });
    group.bench_function("search/last_key", |b| b.iter(|| map.get(last_key).unwrap()));
    group.bench_function("minimum", |b| b.iter(|| map.first_key_value().unwrap()));
    group.bench_function("maximum", |b| b.iter(|| map.last_key_value().unwrap()));

    // TODO(#3): Add more benchmarks for:
    //   - insert new keys into:
    //     - an empty tree
    //     - a tree tree that already contains the given key
    //     - a tree node that is full and will need to grow
}

fn setup_tree_run_benches_cleanup(
    c: &mut Criterion<Measurement>,
    keys: impl Iterator<Item = Box<[u8]>>,
    group_name: &str,
) {
    let keys: Vec<_> = keys.collect();

    let tree: TreeMap<usize> = keys
        .iter()
        .enumerate()
        .map(|(idx, key)| (key.clone(), idx))
        .collect();

    {
        let mut group = c.benchmark_group(group_name);
        run_benchmarks(&mut group, keys.as_ref(), &tree);
    }
}

pub fn raw_api_benches(c: &mut Criterion<Measurement>) {
    // number of keys = 256
    setup_tree_run_benches_cleanup(c, generate_keys_skewed(u8::MAX as usize), "skewed");
    // number of keys = 256
    setup_tree_run_benches_cleanup(c, generate_key_fixed_length([2; 8]), "fixed_length");
    // number of keys = 256
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
        "large_prefixes",
    )
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn create_criterion_configuration() -> Criterion<Measurement> {
    use perfcnt::linux::{HardwareEventType, PerfCounterBuilderLinux};

    Criterion::default().with_measurement(criterion_perf_events::Perf::new(
        PerfCounterBuilderLinux::from_hardware_event(
            // I switched to using retired instruction counts because the variability of the
            // wall time measurement was too high. I was regularly seeing
            // +/-3-5% differences in the measured time, even with up to 5000
            // samples and duration around 30 seconds. I also tried measuring
            // CPU cycles, which had a similar issue. This level of variability was
            // too much to still be able to measure small differences in optimization outcomes.
            //
            // However, this library is likely to have major optimization issues with regards
            // to it memory usage/layout/etc, and only using the retired
            // instruction count will miss parts of this.
            //
            // Should consider making simple benchmarking tool using
            // https://docs.rs/perf-event/latest/perf_event/events/index.html
            //
            // Also note, using this `Measurement` writes output in "cycles" even though it
            // actually is counting retired instructions. The formatter is just
            // hardcoded to use "cycles".
            // https://github.com/jbreitbart/criterion-perf-events/blob/bcde187ccc5ca183a433d71525efb1e2b5ae9a83/src/lib.rs#L127
            HardwareEventType::Instructions,
        ),
    ))
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn create_criterion_configuration() -> Criterion<Measurement> {
    Criterion::default()
}

criterion_group! {
    name = benches;
    config = create_criterion_configuration();
    targets = raw_api_benches
}
criterion_main!(benches);
