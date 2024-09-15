use crate::common::{dictionary_tree, with_prefixes_tree};
use criterion::{criterion_group, Criterion};

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("clone");

    // let skewed_tree = skewed_tree();
    let with_prefixes_tree = with_prefixes_tree();
    let dictionary_tree = dictionary_tree();

    // Skewed clone is not included because it causes a stack overflow.
    // group.bench_function("skewed", |b| b.iter(|| skewed_tree.clone()));
    group.bench_function("with_prefixes", |b| b.iter(|| with_prefixes_tree.clone()));
    group.bench_function("dictionary", |b| b.iter(|| dictionary_tree.clone()));
}

criterion_group!(bench_clone_group, criterion_benchmark);
