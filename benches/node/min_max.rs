use std::{ffi::CString, ptr::NonNull};

use blart::{InnerNode, InnerNode256, InnerNode48, NodePtr};
use criterion::{criterion_group, Criterion};

fn bench(c: &mut Criterion) {
    let dangling_ptr =
        unsafe { NodePtr::new(NonNull::<InnerNode48<CString, usize, 16>>::dangling().as_ptr()) };
    let dangling_opaque = dangling_ptr.to_opaque();
    let count = 3u8;
    let skip = (256u32 / count as u32) as u8;
    let nodes48: Vec<_> = (0..count)
        .map(|i| {
            let idx = i * skip;
            let mut node = InnerNode48::<CString, usize, 16>::empty();
            node.write_child(idx, dangling_opaque);
            (idx, node)
        })
        .collect();
    let nodes256: Vec<_> = (0..count)
        .map(|i| {
            let idx = i * skip;
            let mut node = InnerNode256::<CString, usize, 16>::empty();
            node.write_child(idx, dangling_opaque);
            (idx, node)
        })
        .collect();

    for (idx, node) in nodes48.clone() {
        let mut group = c.benchmark_group("min/n48");
        group.bench_function(idx.to_string(), |b| {
            b.iter(|| std::hint::black_box(node.min()));
        });
    }

    for (idx, node) in nodes48.clone() {
        let mut group = c.benchmark_group("max/n48");
        group.bench_function(idx.to_string(), |b| {
            b.iter(|| std::hint::black_box(node.max()));
        });
    }

    for (idx, node) in nodes256.clone() {
        let mut group = c.benchmark_group("min/n256");
        group.bench_function(idx.to_string(), |b| {
            b.iter(|| std::hint::black_box(node.min()));
        });
    }

    for (idx, node) in nodes256.clone() {
        let mut group = c.benchmark_group("max/n256");
        group.bench_function(idx.to_string(), |b| {
            b.iter(|| std::hint::black_box(node.max()));
        });
    }
}

criterion_group!(bench_min_max_group, bench);
