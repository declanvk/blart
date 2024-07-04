use std::{ffi::CString, ptr::NonNull};

use blart::{InnerNode, InnerNode16, InnerNode256, InnerNode4, InnerNode48, NodePtr, TreeMap};
use criterion::{measurement::Measurement, Criterion};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};

#[macro_use]
mod common;

fn iter_node<const PREFIX_LEN: usize, M: Measurement, N: InnerNode<PREFIX_LEN>>(
    c: &mut Criterion<M>,
    prefix: &str,
    ty: &str,
    sizes: &[u16],
) {
    let mut rng = StdRng::seed_from_u64(69420);
    let bytes: Vec<_> = (0..=255u8).collect();

    let dangling_ptr =
        unsafe { NodePtr::new(NonNull::<InnerNode48<_, _, PREFIX_LEN>>::dangling().as_ptr()) };
    let dangling_opaque = dangling_ptr.to_opaque();

    let mut group = c.benchmark_group(format!("{prefix}/{ty}"));
    for size in sizes {
        let mut node = N::empty();
        for key in bytes.choose_multiple(&mut rng, *size as usize) {
            node.write_child(*key, dangling_opaque)
        }

        group.bench_function(format!("{size}").as_str(), |b| {
            b.iter(|| {
                node.iter().for_each(|(k, n)| {
                    std::hint::black_box((k, n));
                });
            });
        });
    }
}

fn bench<M: Measurement>(c: &mut Criterion<M>, prefix: &str) {
    iter_node::<16, _, InnerNode4<CString, usize, 16>>(c, prefix, "n4", &[1, 4]);
    iter_node::<16, _, InnerNode16<CString, usize, 16>>(c, prefix, "n16", &[5, 12, 16]);
    iter_node::<16, _, InnerNode48<CString, usize, 16>>(c, prefix, "n48", &[17, 32, 48]);
    iter_node::<16, _, InnerNode256<CString, usize, 16>>(
        c,
        prefix,
        "n256",
        &[49, 100, 152, 204, 256],
    );

    let words = include_str!("dict.txt");
    let tree: TreeMap<_, _> = words
        .lines()
        .map(|s| (CString::new(s).unwrap(), 0usize))
        .collect();

    let mut group = c.benchmark_group(format!("{prefix}/tree"));
    group.warm_up_time(std::time::Duration::from_secs(5));
    group.measurement_time(std::time::Duration::from_secs(15));

    group.bench_function("dict/foward", |b| {
        b.iter(|| {
            tree.iter().for_each(|(k, v)| {
                std::hint::black_box((k, v));
            });
        });
    });

    group.bench_function("dict/rev", |b| {
        b.iter(|| {
            tree.iter().rev().for_each(|(k, v)| {
                std::hint::black_box((k, v));
            });
        });
    });
}

gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
