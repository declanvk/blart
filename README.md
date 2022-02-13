# BLART

## Documentation

- [Documentation for the `main` branch](https://declanvk.github.io/blart/)

## Fuzzing

To run the fuzzer I use the command:

```bash
cargo fuzz run -j 8 -s address fuzz_raw_api -- -max_len=32768 -max_total_time=3600 && cargo fuzz cmin fuzz_raw_api
```

This will run the fuzzer for a total of 3600 seconds (1 hour), using 8 jobs (half of the total number of cores on my dev box), and using the address sanitizer. The `cmin` command is used to compact the corpus after generating new entries.

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
