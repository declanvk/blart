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
        let mut node = N::from_prefix(&[], 0);
        for key in bytes.choose_multiple(&mut rng, *size as usize) {
            node.write_child(*key, dangling_opaque)
        }

        group.bench_function(format!("{size}").as_str(), |b| {
            b.iter(|| {
                unsafe { node.iter().map(|(k, _)| k as u32).sum::<u32>() };
            });
        });
    }
}

fn bench<M: Measurement>(c: &mut Criterion<M>, prefix: &str) {
    iter_node::<_, InnerNode4<CString, usize>>(c, prefix, "n4", &[1, 4]);
    iter_node::<_, InnerNode16<CString, usize>>(c, prefix, "n16", &[5, 12, 16]);
    iter_node::<_, InnerNode48<CString, usize>>(c, prefix, "n48", &[17, 32, 48]);
    iter_node::<_, InnerNode256<CString, usize>>(c, prefix, "n256", &[49, 100, 152, 204, 256]);
}

blart::gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
