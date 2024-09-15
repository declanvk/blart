use std::ffi::CString;

use blart::TreeMap;
use criterion::{criterion_group, measurement::Measurement, Criterion};

fn bench<M: Measurement>(c: &mut Criterion<M>) {
    let words = include_str!("../data/medium-dict.txt");
    let mut bytes = 0;
    let tree: TreeMap<_, _> = words
        .lines()
        .map(|s| {
            let s = CString::new(s).unwrap();
            bytes += s.as_bytes_with_nul().len();
            (s, 0usize)
        })
        .collect();

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
