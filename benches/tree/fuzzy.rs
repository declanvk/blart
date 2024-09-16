use std::ffi::CString;

use criterion::{criterion_group, measurement::Measurement, Criterion};

use crate::common::dictionary_tree;

fn bench<M: Measurement>(c: &mut Criterion<M>) {
    let tree = dictionary_tree();
    let bytes: usize = tree.keys().map(|k| k.as_bytes_with_nul().len()).sum();

    let searches = [
        CString::new("house").unwrap(),
        CString::new("houze").unwrap(),
        CString::new("headphones").unwrap(),
        CString::new("headpones").unwrap(),
        CString::new("unavoided").unwrap(),
        CString::new("unavoid").unwrap(),
    ];

    let costs = [0, 3, 5, 10];

    for cost in costs {
        let mut group = c.benchmark_group(format!("fuzzy/{cost}"));
        group.throughput(criterion::Throughput::Bytes(bytes as u64));
        for search in &searches {
            group.bench_function(search.to_str().unwrap(), |b| {
                b.iter(|| std::hint::black_box(tree.fuzzy(search, cost).collect::<Vec<_>>()));
            });
        }
    }
}

criterion_group!(bench_fuzzy_group, bench);
