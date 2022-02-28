use blart::{
    deallocate_tree, insert_unchecked, maximum_unchecked, minimum_unchecked, search_unchecked,
    tests_common::{generate_key_fixed_length, generate_keys_skewed},
    LeafNode, NodePtr, OpaqueNodePtr,
};
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion};
use criterion_perf_events::Perf;
use perfcnt::linux::{HardwareEventType, PerfCounterBuilderLinux};
use std::time::Duration;

fn run_benchmarks(
    group: &mut BenchmarkGroup<Perf>,
    key_vec: &[Box<[u8]>],
    tree_root: OpaqueNodePtr<usize>,
) {
    let (first_key, middle_key, last_key) = (
        key_vec[0].as_ref(),
        key_vec[key_vec.len() / 2].as_ref(),
        key_vec[key_vec.len() - 1].as_ref(),
    );
    group.bench_function("search/first_key", |b| {
        b.iter(|| unsafe { search_unchecked(tree_root, first_key).unwrap() })
    });
    group.bench_function("search/middle_key", |b| {
        b.iter(|| unsafe { search_unchecked(tree_root, middle_key).unwrap() })
    });
    group.bench_function("search/last_key", |b| {
        b.iter(|| unsafe { search_unchecked(tree_root, last_key).unwrap() })
    });
    group.bench_function("minimum", |b| {
        b.iter(|| unsafe { minimum_unchecked(tree_root).unwrap() })
    });
    group.bench_function("maximum", |b| {
        b.iter(|| unsafe { maximum_unchecked(tree_root).unwrap() })
    });
}

pub fn raw_api_benches(c: &mut Criterion<Perf>) {
    let skewed_keys: Vec<_> = generate_keys_skewed(u8::MAX as usize).collect();
    let fixed_length_keys: Vec<_> = generate_key_fixed_length(25, 10).collect();

    // size - skewed_keys = 256, fixed_length_keys = 251

    let mut skewed_root =
        NodePtr::allocate_node(LeafNode::new(skewed_keys[0].clone(), 0)).to_opaque();
    let mut fixed_length_root =
        NodePtr::allocate_node(LeafNode::new(fixed_length_keys[0].clone(), 0)).to_opaque();

    for (idx, key) in skewed_keys.iter().skip(1).cloned().enumerate() {
        skewed_root = unsafe { insert_unchecked(skewed_root, key, idx + 1).unwrap() };
    }
    for (idx, key) in fixed_length_keys.iter().skip(1).cloned().enumerate() {
        fixed_length_root = unsafe { insert_unchecked(fixed_length_root, key, idx + 1).unwrap() };
    }

    {
        let mut skewed_group = c.benchmark_group("skewed");
        run_benchmarks(&mut skewed_group, skewed_keys.as_ref(), skewed_root);
    }

    {
        let mut fixed_length_group = c.benchmark_group("fixed_length");
        run_benchmarks(
            &mut fixed_length_group,
            fixed_length_keys.as_ref(),
            fixed_length_root,
        );
    }

    unsafe { deallocate_tree(fixed_length_root) };
    unsafe { deallocate_tree(skewed_root) };
}

fn create_criterion_configuration() -> Criterion<Perf> {
    Criterion::default()
        .with_measurement(Perf::new(PerfCounterBuilderLinux::from_hardware_event(
            // I switched to using retired instruction counts because the variability of the wall
            // time measurement was too high. I was regularly seeing +/-3-5% differences in the
            // measured time, even with up to 5000 samples and duration around 30 seconds. I also
            // tried measuring CPU cycles, which had a similar issue. This level of variability was
            // too much to still be able to measure small differences in optimization outcomes.
            //
            // However, this library is likely to have major optimization issues with regards to it
            // memory usage/layout/etc, and only using the retired instruction count will miss
            // parts of this.
            //
            // Should consider making simple benchmarking tool using
            // https://docs.rs/perf-event/latest/perf_event/events/index.html
            HardwareEventType::Instructions,
        )))
        .sample_size(1000)
        .measurement_time(Duration::new(10, 0))
}

criterion_group! {
    name = benches;
    config = create_criterion_configuration();
    targets = raw_api_benches
}
criterion_main!(benches);
