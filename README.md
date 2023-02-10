# BLART

## Documentation

- [Documentation for the `main` branch](https://declanvk.github.io/blart/)

## Testing

### Miri

Currently we're using some specific crates (`sptr` and in the future back to `core::ptr::*`) to ensure that we're compatible with [Strict Provenance][sp-issue]. The following `MIRIFLAGS` setup should enable checking to make sure that we're compatible.

```bash
MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-symbolic-alignment-check" cargo +nightly miri test
```

I think this is useful because we're doing some pointer times with our tagged pointers implementation, mutating the contents of the pointer to store bits of data.

## Fuzzing

To run the fuzzer I use the command:

```bash
cargo +nightly fuzz run -j 8 -s address fuzz_raw_api -- -max_len=32768 -max_total_time=3600 && cargo +nightly fuzz cmin fuzz_raw_api
```

This will run the fuzzer for a total of 3600 seconds (1 hour), using 8 jobs (half of the total number of cores on my dev box), and using the address sanitizer. The `cmin` command is used to compact the corpus after generating new entries.

### Coverage

To generate coverage reports from fuzzing corpus:

```bash
# replace with own triple as required
TARGET_TRIPLE="x86_64-unknown-linux-gnu"
cargo +nightly fuzz coverage fuzz_raw_api && cargo cov -- show fuzz/target/"$TARGET_TRIPLE"/release/fuzz_raw_api \
    --format=html \
    -instr-profile=fuzz/coverage/fuzz_raw_api/coverage.profdata \
    > index.html
```

## Benchmarks

To run the benchmarks, install [`cargo-criterion`](https://github.com/bheisler/cargo-criterion), then run:

```bash
cargo +nightly criterion --history-id "$(git rev-parse --short HEAD)-0"
```

If you get a "Permission denied" error, update perf_event_paranoid:
```bash
sudo sh -c 'echo 1 >/proc/sys/kernel/perf_event_paranoid'
```
For further details please take a look at the following [link](https://superuser.com/questions/980632/run-perf-without-root-rights).


## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[sp-issue]: https://github.com/rust-lang/rust/issues/95228
