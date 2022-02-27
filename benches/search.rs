use blart::{
    deallocate_tree, insert_unchecked, search_unchecked,
    tests_common::{generate_key_fixed_length, generate_keys_skewed},
    LeafNode, NodePtr,
};
use criterion::{criterion_group, criterion_main, Criterion};

pub fn criterion_benchmark(c: &mut Criterion) {
    let skewed_keys: Vec<_> = generate_keys_skewed(u8::MAX as usize).collect();
    let fixed_length_keys: Vec<_> = generate_key_fixed_length(25, 10).collect();

    // size - skewed_keys = 256, fixed_length_keys = 251

    let mut skewed_root =
        NodePtr::allocate_node(LeafNode::new(skewed_keys[0].clone(), 0)).to_opaque();
    let mut fixed_length_root =
        NodePtr::allocate_node(LeafNode::new(fixed_length_keys[0].clone(), 0)).to_opaque();

    for (idx, key) in skewed_keys.iter().skip(1).cloned().enumerate() {
        skewed_root = unsafe { insert_unchecked(skewed_root, key, idx + 1).unwrap() };
    }
    for (idx, key) in fixed_length_keys.iter().skip(1).cloned().enumerate() {
        fixed_length_root = unsafe { insert_unchecked(fixed_length_root, key, idx + 1).unwrap() };
    }

    {
        let mut skewed_group = c.benchmark_group("search/skewed");
        let (first_key, middle_key, last_key) = (
            skewed_keys[0].as_ref(),
            skewed_keys[skewed_keys.len() / 2].as_ref(),
            skewed_keys[skewed_keys.len() - 1].as_ref(),
        );
        skewed_group.bench_function("first_key", |b| {
            b.iter(|| unsafe { search_unchecked(skewed_root, first_key).unwrap() })
        });
        skewed_group.bench_function("middle_key", |b| {
            b.iter(|| unsafe { search_unchecked(skewed_root, middle_key).unwrap() })
        });
        skewed_group.bench_function("last_key", |b| {
            b.iter(|| unsafe { search_unchecked(skewed_root, last_key).unwrap() })
        });
    }

    {
        let mut fixed_length_group = c.benchmark_group("search/fixed_length");
        let (first_key, middle_key, last_key) = (
            fixed_length_keys[0].as_ref(),
            fixed_length_keys[fixed_length_keys.len() / 2].as_ref(),
            fixed_length_keys[fixed_length_keys.len() - 1].as_ref(),
        );
        fixed_length_group.bench_function("first_key", |b| {
            b.iter(|| unsafe { search_unchecked(fixed_length_root, first_key).unwrap() })
        });
        fixed_length_group.bench_function("middle_key", |b| {
            b.iter(|| unsafe { search_unchecked(fixed_length_root, middle_key).unwrap() })
        });
        fixed_length_group.bench_function("last_key", |b| {
            b.iter(|| unsafe { search_unchecked(fixed_length_root, last_key).unwrap() })
        });
    }

    unsafe { deallocate_tree(fixed_length_root) };
    unsafe { deallocate_tree(skewed_root) };
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
