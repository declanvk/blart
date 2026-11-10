//! Compare the common prefix length functions over different input lengths and
//! mismatch positions, to find where the relative performance difference crossover happens.

use std::hint::black_box;

use blart::raw::{longest_common_prefix_len, short_common_prefix_len};
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group};
use rand::{Rng, SeedableRng, rngs::StdRng};

/// Run `$body` once for each function, with `$function` bound to a direct
/// (not through a function pointer) call of it, so the always inlined function
/// is actually inlined into the benchmark loop.
macro_rules! for_each_function {
    (|$name:ident, $function:ident| $body:block) => {{
        {
            // Byte at a time, always inlined
            let $name = "short";
            #[allow(unused_macros)]
            macro_rules! $function {
                ($a:expr, $b:expr) => {
                    short_common_prefix_len($a, $b)
                };
            }
            $body
        }
        {
            // 16 bytes at a time, behind a function call
            let $name = "longest";
            #[allow(unused_macros)]
            macro_rules! $function {
                ($a:expr, $b:expr) => {
                    longest_common_prefix_len($a, $b)
                };
            }
            $body
        }
    }};
}

const MAX_LEN: usize = 64;

const LENGTHS: &[usize] = &[
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 20, 24, 32, 48, 64,
];

/// Return a copy of `base` where the byte at `mismatch_at` is different, or an
/// identical copy if `mismatch_at` is past the end.
fn with_mismatch(base: &[u8], mismatch_at: usize) -> Vec<u8> {
    let mut other = base.to_vec();
    if let Some(byte) = other.get_mut(mismatch_at) {
        *byte ^= 0xFF;
    }
    other
}

/// Benchmark a single input repeated, so the branch predictor learns its
/// pattern. This is the best case for both loops.
fn bench_fixed(c: &mut Criterion) {
    let base: Vec<u8> = (0..MAX_LEN as u8).collect();

    for (match_name, mismatch_at) in [
        ("mismatch_first", (|_len: usize| 0) as fn(usize) -> usize),
        ("mismatch_middle", |len| len / 2),
        ("full_match", |len| len),
    ] {
        let mut group = c.benchmark_group(format!("common_prefix_len/fixed/{match_name}"));
        for &len in LENGTHS {
            let a = &base[..len];
            let b = with_mismatch(a, mismatch_at(len));
            for_each_function!(|fn_name, function| {
                group.bench_with_input(BenchmarkId::new(fn_name, len), &len, |bencher, _| {
                    bencher.iter(|| function!(black_box(a), black_box(&b)))
                });
            });
        }
        group.finish();
    }
}

/// Benchmark a batch of inputs with random lengths up to a maximum and random
/// mismatch positions, which is closer to a trie search, where each inner node
/// has a different prefix length.
fn bench_mixed(c: &mut Criterion) {
    const BATCH: usize = 256;

    let base: Vec<u8> = (0..MAX_LEN as u8).collect();
    let mut group = c.benchmark_group("common_prefix_len/mixed");
    group.throughput(Throughput::Elements(BATCH as u64));

    for max_len in [4, 8, 10, 16, 24, 32] {
        let mut rng = StdRng::seed_from_u64(0xC0FFEE ^ max_len as u64);
        let inputs: Vec<(Vec<u8>, Vec<u8>)> = (0..BATCH)
            .map(|_| {
                let len = rng.random_range(0..=max_len);
                // Mismatch positions past the end of the input are full matches
                let mismatch_at = rng.random_range(0..=len);
                let a = base[..len].to_vec();
                let b = with_mismatch(&a, mismatch_at);
                (a, b)
            })
            .collect();

        for_each_function!(|fn_name, function| {
            group.bench_with_input(
                BenchmarkId::new(fn_name, max_len),
                &max_len,
                |bencher, _| {
                    bencher.iter(|| {
                        let mut total = 0;
                        for (a, b) in &inputs {
                            total += function!(black_box(a.as_slice()), black_box(b.as_slice()));
                        }
                        total
                    })
                },
            );
        });
    }
    group.finish();
}

criterion_group!(
    name = bench_common_prefix_len_group;
    config = Criterion::default()
        .warm_up_time(std::time::Duration::from_millis(300))
        .measurement_time(std::time::Duration::from_millis(700))
        .sample_size(30);
    targets = bench_fixed, bench_mixed
);
