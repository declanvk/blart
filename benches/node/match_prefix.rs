use blart::raw::{InnerNode, InnerNode256, InnerNode48, LeafNode, NodePtr};
use criterion::{criterion_group, Criterion};

fn bench(c: &mut Criterion) {
    let leaf = LeafNode::with_no_siblings(
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
    let key_small_mismatch = &[0u8, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    let key_large_match = &[
        0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0,
    ];
    let key_large_mismatch = &[
        0u8, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0,
    ];

    let p0 = &[0, 0, 0, 0, 0, 0, 0, 0];
    let mut node48_small = InnerNode48::<Box<[u8]>, usize, 16>::from_prefix(p0, p0.len());
    let mut node256_small = InnerNode256::<Box<[u8]>, usize, 16>::from_prefix(p0, p0.len());
    node48_small.write_child(99, leaf_opaque);
    node256_small.write_child(99, leaf_opaque);

    let p1 = &[
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    let mut node48_large = InnerNode48::<Box<[u8]>, usize, 16>::from_prefix(p1, p1.len());
    let mut node256_large = InnerNode256::<Box<[u8]>, usize, 16>::from_prefix(p1, p1.len());
    node48_large.write_child(99, leaf_opaque);
    node256_large.write_child(99, leaf_opaque);

    macro_rules! generate_benches {
        ($match_func:ident $($current_depth:literal)?) => {{
            let mut old_group = c.benchmark_group(stringify!($match_func));
            old_group.bench_function("node48/small/match", |b| {
                b.iter(|| std::hint::black_box(node48_small.$match_func(key_small_match $(, $current_depth)?)));
            });
            old_group.bench_function("node48/small/mismatch", |b| {
                b.iter(|| std::hint::black_box(node48_small.$match_func(key_small_mismatch $(, $current_depth)?)));
            });
            old_group.bench_function("node48/large/match", |b| {
                b.iter(|| std::hint::black_box(node48_large.$match_func(key_large_match $(, $current_depth)?)));
            });
            old_group.bench_function("node48/large/mismatch", |b| {
                b.iter(|| std::hint::black_box(node48_large.$match_func(key_large_mismatch $(, $current_depth)?)));
            });

            old_group.bench_function("node256/small/match", |b| {
                b.iter(|| std::hint::black_box(node256_small.$match_func(key_small_match $(, $current_depth)?)));
            });
            old_group.bench_function("node256/small/mismatch", |b| {
                b.iter(|| std::hint::black_box(node256_small.$match_func(key_small_mismatch $(, $current_depth)?)));
            });
            old_group.bench_function("node256/large/match", |b| {
                b.iter(|| std::hint::black_box(node256_large.$match_func(key_large_match $(, $current_depth)?)));
            });
            old_group.bench_function("node256/large/mismatch", |b| {
                b.iter(|| std::hint::black_box(node256_large.$match_func(key_large_mismatch $(, $current_depth)?)));
            });
        }};
    }

    generate_benches!(match_full_prefix 0);
    generate_benches!(attempt_pessimistic_match_prefix);
    generate_benches!(optimistic_match_prefix);

    drop(unsafe { Box::from_raw(leaf_ptr) });
}

criterion_group!(bench_match_prefix_group, bench);
