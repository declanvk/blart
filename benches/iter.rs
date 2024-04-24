use std::{ffi::CString, ptr::NonNull, time::Duration};

use blart::{
    InnerNode, InnerNode16, InnerNode256, InnerNode4, InnerNode48, Node, NodePtr, TreeMap,
};
use criterion::{measurement::Measurement, Criterion};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};

fn iter_node<M: Measurement, N: InnerNode>(
    c: &mut Criterion<M>,
    prefix: &str,
    ty: &str,
    sizes: &[u16],
) {
    let mut rng = StdRng::seed_from_u64(69420);
    let bytes: Vec<_> = (0..=255u8).collect();

    let dangling_ptr = unsafe { NodePtr::new(NonNull::<InnerNode48<_, _>>::dangling().as_ptr()) };
    let dangling_opaque = dangling_ptr.to_opaque();

    let mut group = c.benchmark_group(format!("{prefix}/{ty}"));
    for size in sizes {
        let mut node = N::empty();
        for key in bytes.choose_multiple(&mut rng, *size as usize) {
            node.write_child(*key, dangling_opaque)
        }

        group.bench_function(format!("{size}").as_str(), |b| {
            b.iter(|| unsafe {
                node.iter().for_each(|(k, n)| {
                    std::hint::black_box((k, n));
                });
            });
        });
    }
}

fn bench<M: Measurement>(c: &mut Criterion<M>, prefix: &str) {
    // iter_node::<_, InnerNode4<CString, usize>>(c, prefix, "n4", &[1, 4]);
    // iter_node::<_, InnerNode16<CString, usize>>(c, prefix, "n16", &[5, 12, 16]);
    // iter_node::<_, InnerNode48<CString, usize>>(c, prefix, "n48", &[17, 32, 48]);
    // iter_node::<_, InnerNode256<CString, usize>>(c, prefix, "n256", &[49, 100, 152, 204, 256]);

    let words = include_str!("dict.txt");
    let mut tree: TreeMap<_, _> = words
        .lines()
        .map(|s| (CString::new(s).unwrap(), 0usize))
        .collect();

    let mut group = c.benchmark_group(format!("{prefix}/tree"));
    group.warm_up_time(std::time::Duration::from_secs(60));
    group.measurement_time(std::time::Duration::from_secs(240));

    group.bench_function("dict", |b| {
        b.iter(|| {
            tree.iter().for_each(|(k, v)| {
                std::hint::black_box((k, v));
            });
        });
    });

    group.bench_function("dict1", |b| {
        b.iter(|| {
            tree.iter_1().for_each(|(k, v)| {
                std::hint::black_box((k, v));
            });
        });
    });
}

blart::gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
