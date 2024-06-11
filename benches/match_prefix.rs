use std::{ffi::CString, ptr::NonNull, time::Duration};

use blart::{
    InnerNode, InnerNode16, InnerNode256, InnerNode4, InnerNode48, LeafNode, NodePtr, TreeMap,
};
use criterion::{measurement::Measurement, Criterion};

fn bench<M: Measurement>(c: &mut Criterion<M>, prefix: &str) {
    let leaf = LeafNode::new(
        vec![
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ]
        .into_boxed_slice(),
        0usize,
    );
    let leaf_ptr = Box::into_raw(Box::new(leaf));
    let leaf_node_ptr = unsafe { NodePtr::new(leaf_ptr) };
    let leaf_opaque = leaf_node_ptr.to_opaque();

    let key_small_match = &[0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let key_small_match_padded = &[
        0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0,
    ];
    let key_small_mismatch = &[0u8, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    let key_small_mismatch_padded = &[
        0u8, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0,
    ];

    let key_large_match = &[
        0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0,
    ];
    let key_large_match_padded = &[
        0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    let key_large_mismatch = &[
        0u8, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0,
    ];
    let key_large_mismatch_padded = &[
        0u8, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];

    let p0 = &[0, 0, 0, 0, 0, 0, 0, 0];
    let mut node48_small = InnerNode48::<Box<[u8]>, usize>::from_prefix(p0, p0.len());
    let mut node256_small = InnerNode256::<Box<[u8]>, usize>::from_prefix(p0, p0.len());
    node48_small.write_child(99, leaf_opaque);
    node256_small.write_child(99, leaf_opaque);

    let p1 = &[
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    let mut node48_large = InnerNode48::<Box<[u8]>, usize>::from_prefix(p1, p1.len());
    let mut node256_large = InnerNode256::<Box<[u8]>, usize>::from_prefix(p1, p1.len());
    node48_large.write_child(99, leaf_opaque);
    node256_large.write_child(99, leaf_opaque);

    {
        let mut old_group = c.benchmark_group(format!("{prefix}/old"));
        old_group.warm_up_time(Duration::from_secs(5));
        old_group.measurement_time(Duration::from_secs(10));
        old_group.bench_function("node48/small/match", |b| {
            b.iter(|| std::hint::black_box(node48_small.match_prefix(key_small_match, 0)));
        });
        old_group.bench_function("node48/small/mismatch", |b| {
            b.iter(|| std::hint::black_box(node48_small.match_prefix(key_small_mismatch, 0)));
        });
        old_group.bench_function("node48/large/match", |b| {
            b.iter(|| std::hint::black_box(node48_large.match_prefix(key_large_match, 0)));
        });
        old_group.bench_function("node48/large/mismatch", |b| {
            b.iter(|| std::hint::black_box(node48_large.match_prefix(key_large_mismatch, 0)));
        });

        old_group.bench_function("node256/small/match", |b| {
            b.iter(|| std::hint::black_box(node256_small.match_prefix(key_small_match, 0)));
        });
        old_group.bench_function("node256/small/mismatch", |b| {
            b.iter(|| std::hint::black_box(node256_small.match_prefix(key_small_mismatch, 0)));
        });
        old_group.bench_function("node256/large/match", |b| {
            b.iter(|| std::hint::black_box(node256_large.match_prefix(key_large_match, 0)));
        });
        old_group.bench_function("node256/large/mismatch", |b| {
            b.iter(|| std::hint::black_box(node256_large.match_prefix(key_large_mismatch, 0)));
        });
    }

    drop(unsafe { Box::from_raw(leaf_ptr) });
}

blart::gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
