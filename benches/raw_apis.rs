use blart::{
    deallocate_tree, insert_unchecked, maximum_unchecked, minimum_unchecked, search_unchecked,
    tests_common::{
        generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed, PrefixExpansion,
    },
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

    // TODO: Add more benchmarks for:
    //   - insert new keys into:
    //     - an empty tree
    //     - a tree tree that already contains the given key
    //     - a tree node that is full and will need to grow
}

fn setup_tree_run_benches_cleanup(
    c: &mut Criterion<Perf>,
    keys: impl Iterator<Item = Box<[u8]>>,
    group_name: &str,
) {
    let keys: Vec<_> = keys.collect();

    let mut root = NodePtr::allocate_node(LeafNode::new(keys[0].clone(), 0)).to_opaque();

    for (idx, key) in keys.iter().skip(1).cloned().enumerate() {
        root = unsafe { insert_unchecked(root, key, idx + 1).unwrap() };
    }

    {
        let mut group = c.benchmark_group(group_name);
        run_benchmarks(&mut group, keys.as_ref(), root);
    }

    unsafe { deallocate_tree(root) };
}

pub fn raw_api_benches(c: &mut Criterion<Perf>) {
    // number of keys = 256
    setup_tree_run_benches_cleanup(c, generate_keys_skewed(u8::MAX as usize), "skewed");
    // number of keys = 256
    setup_tree_run_benches_cleanup(c, generate_key_fixed_length(8, 2), "fixed_length");
    // number of keys = 256
    setup_tree_run_benches_cleanup(
        c,
        generate_key_with_prefix(
            8,
            2,
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
