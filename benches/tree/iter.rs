use std::{ffi::CString, ptr::NonNull};

use blart::raw::{InnerNode, InnerNode16, InnerNode256, InnerNode4, InnerNode48, NodePtr};
use criterion::{criterion_group, measurement::Measurement, Criterion};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};

use crate::common::{dictionary_tree, get_middle_key};

fn iter_node<const PREFIX_LEN: usize, M: Measurement, N: InnerNode<PREFIX_LEN>>(
    c: &mut Criterion<M>,
    ty: &str,
    sizes: &[u16],
) {
    let mut rng = StdRng::seed_from_u64(69420);
    let bytes: Vec<_> = (0..=255u8).collect();

    let dangling_ptr =
        unsafe { NodePtr::new(NonNull::<InnerNode48<_, _, PREFIX_LEN>>::dangling().as_ptr()) };
    let dangling_opaque = dangling_ptr.to_opaque();

    let mut group = c.benchmark_group(format!("iter_node/{ty}"));
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

fn bench(c: &mut Criterion) {
    iter_node::<16, _, InnerNode4<CString, usize, 16>>(c, "n4", &[1, 4]);
    iter_node::<16, _, InnerNode16<CString, usize, 16>>(c, "n16", &[5, 12, 16]);
    iter_node::<16, _, InnerNode48<CString, usize, 16>>(c, "n48", &[17, 32, 48]);
    iter_node::<16, _, InnerNode256<CString, usize, 16>>(c, "n256", &[49, 100, 152, 204, 256]);

    let tree = dictionary_tree();

    let mut group = c.benchmark_group("iter/tree");

    group.bench_function("dict/forward", |b| {
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

    group.bench_function("dict/range", |b| {
        let range = get_middle_key(&tree, 1, 2)..get_middle_key(&tree, 2, 1);
        b.iter(|| {
            tree.range::<CString, _>(range.clone()).for_each(|(k, v)| {
                std::hint::black_box((k, v));
            });
        });
    });
}

criterion_group!(bench_iter_group, bench);
