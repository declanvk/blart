use std::{ffi::CString, ptr::NonNull, time::Duration};

use blart::{InnerNode, InnerNode16, InnerNode256, InnerNode4, InnerNode48, NodePtr, TreeMap, VariableKeyHeader};
use criterion::{measurement::Measurement, Criterion};

fn bench<M: Measurement>(c: &mut Criterion<M>, prefix: &str) {
    let dangling_ptr =
        unsafe { NodePtr::new(NonNull::<InnerNode48<CString, usize, 16, VariableKeyHeader<16>>>::dangling().as_ptr()) };
    let dangling_opaque = dangling_ptr.to_opaque();
    let count = 8u8;
    let skip = (256u32 / count as u32) as u8;
    let nodes48: Vec<_> = (0..count)
        .map(|i| {
            let idx = i * skip;
            let mut node = InnerNode48::<CString, usize, 16, VariableKeyHeader<16>>::empty();
            node.write_child(idx, dangling_opaque);
            (idx, node)
        })
        .collect();
    let nodes256: Vec<_> = (0..count)
        .map(|i| {
            let idx = i * skip;
            let mut node = InnerNode256::<CString, usize, 16, VariableKeyHeader<16>>::empty();
            node.write_child(idx, dangling_opaque);
            (idx, node)
        })
        .collect();

    for (idx, node) in nodes48.clone() {
        let mut group = c.benchmark_group(format!("{prefix}/min/n48"));
        group.warm_up_time(Duration::from_secs(3));
        group.measurement_time(Duration::from_secs(5));
        group.bench_function(format!("{idx}").as_str(), |b| {
            b.iter(|| std::hint::black_box(node.min()));
        });
    }

    for (idx, node) in nodes48.clone() {
        let mut group = c.benchmark_group(format!("{prefix}/max/n48"));
        group.warm_up_time(Duration::from_secs(3));
        group.measurement_time(Duration::from_secs(5));
        group.bench_function(format!("{idx}").as_str(), |b| {
            b.iter(|| std::hint::black_box(node.max()));
        });
    }

    for (idx, node) in nodes256.clone() {
        let mut group = c.benchmark_group(format!("{prefix}/min/n256"));
        group.warm_up_time(Duration::from_secs(3));
        group.measurement_time(Duration::from_secs(5));
        group.bench_function(format!("{idx}").as_str(), |b| {
            b.iter(|| std::hint::black_box(node.min()));
        });
    }

    for (idx, node) in nodes256.clone() {
        let mut group = c.benchmark_group(format!("{prefix}/max/n256"));
        group.warm_up_time(Duration::from_secs(3));
        group.measurement_time(Duration::from_secs(5));
        group.bench_function(format!("{idx}").as_str(), |b| {
            b.iter(|| std::hint::black_box(node.max()));
        });
    }
}

blart::gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
