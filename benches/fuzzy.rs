use std::{ffi::CString, time::Duration};

use blart::TreeMap;
use criterion::{measurement::Measurement, Criterion};

fn bench<M: Measurement>(c: &mut Criterion<M>, prefix: &str) {
    let words = include_str!("dict.txt");
    let mut bytes = 0;
    let mut tree: TreeMap<_, _> = words
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
        let mut group = c.benchmark_group(format!("{prefix}/{cost}"));
        group.throughput(criterion::Throughput::Bytes(bytes as u64));
        group.warm_up_time(Duration::from_secs(5));
        group.measurement_time(Duration::from_secs(10));
        for search in &searches {
            group.bench_function(search.to_str().unwrap(), |b| {
                b.iter(|| std::hint::black_box(tree.fuzzy(search, cost).collect::<Vec<_>>()));
            });
        }
    }
}

blart::gen_benches!(
    bench,
    (cycles, perfcnt::linux::HardwareEventType::CPUCycles),
    (
        instructions,
        perfcnt::linux::HardwareEventType::Instructions
    )
);
