use blart::{
    deallocate_tree, insert_unchecked, maximum_unchecked, minimum_unchecked,
    tests_common::{generate_key_fixed_length, generate_keys_skewed},
    LeafNode, NodePtr,
};
use criterion::{criterion_group, criterion_main, Criterion};

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut skewed_keys = generate_keys_skewed(u8::MAX as usize);
    let mut fixed_length_keys = generate_key_fixed_length(25, 10);

    // size - skewed_keys = 256, fixed_length_keys = 251

    let mut skewed_root =
        NodePtr::allocate_node(LeafNode::new(skewed_keys.next().unwrap(), 0)).to_opaque();
    let mut fixed_length_root =
        NodePtr::allocate_node(LeafNode::new(fixed_length_keys.next().unwrap(), 0)).to_opaque();

    for (idx, key) in skewed_keys.enumerate() {
        skewed_root = unsafe { insert_unchecked(skewed_root, key, idx + 1).unwrap() };
    }
    for (idx, key) in fixed_length_keys.enumerate() {
        fixed_length_root = unsafe { insert_unchecked(fixed_length_root, key, idx + 1).unwrap() };
    }

    {
        let mut minimum_group = c.benchmark_group("minimum");
        minimum_group.bench_function("skewed", |b| {
            b.iter(|| unsafe { minimum_unchecked(skewed_root).unwrap() })
        });
        minimum_group.bench_function("fixed_length", |b| {
            b.iter(|| unsafe { minimum_unchecked(fixed_length_root).unwrap() })
        });
    }

    {
        let mut maximum_group = c.benchmark_group("maximum");
        maximum_group.bench_function("skewed", |b| {
            b.iter(|| unsafe { maximum_unchecked(skewed_root).unwrap() })
        });
        maximum_group.bench_function("fixed_length", |b| {
            b.iter(|| unsafe { maximum_unchecked(fixed_length_root).unwrap() })
        });
    }

    unsafe { deallocate_tree(fixed_length_root) };
    unsafe { deallocate_tree(skewed_root) };
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
