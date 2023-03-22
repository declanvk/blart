# BLART

[![Crates.io][crates-badge]][crates-url]
[![Docs.rs][docs-badge]][docs-url]

BLART is an implementation of an adaptive radix tree, used as backing for map and set data structures. Adaptive radix
trees offer great space efficiency and performance on keys that decompose into byte strings.

[crates-badge]: https://img.shields.io/crates/v/blart
[crates-url]: https://crates.io/crates/blart
[docs-badge]: https://img.shields.io/docsrs/blart
[docs-url]: https://docs.rs/blart/latest/blart/

## Example

Here is an example of using the `TreeMap` type (blatantly stolen from [the standard library][stdlib-example-1]):

```rust
use blart::TreeMap;

// type inference lets us omit an explicit type signature (which
// would be `TreeMap<&str, &str>` in this example).
let mut movie_reviews = TreeMap::new();

// review some movies.
let _ = movie_reviews.try_insert("Office Space",       "Deals with real issues in the workplace.").unwrap();
let _ = movie_reviews.try_insert("Pulp Fiction",       "Masterpiece.").unwrap();
let _ = movie_reviews.try_insert("The Godfather",      "Very enjoyable.").unwrap();
let _ = movie_reviews.try_insert("The Blues Brothers", "Eye lyked it a lot.").unwrap();

// check for a specific one.
if !movie_reviews.contains_key("Les Misérables") {
    println!("We've got {} reviews, but Les Misérables ain't one.",
             movie_reviews.len());
}

// oops, this review has a lot of spelling mistakes, let's delete it.
movie_reviews.remove("The Blues Brothers");

// look up the values associated with some keys.
let to_find = ["Up!", "Office Space"];
for movie in &to_find {
    match movie_reviews.get(movie) {
       Some(review) => println!("{movie}: {review}"),
       None => println!("{movie} is unreviewed.")
    }
}

// Look up the value for a key (will panic if the key is not found).
println!("Movie review: {}", movie_reviews["Office Space"]);

// iterate over everything.
for (movie, review) in &movie_reviews {
    println!("{movie}: \"{review}\"");
}
```

[stdlib-example-1]: https://doc.rust-lang.org/stable/std/collections/struct.BTreeMap.html#examples

## Documentation

- [Documentation for the `main` branch][declanvk-blart-docs]

[declanvk-blart-docs]: https://declanvk.github.io/blart/

## Testing

### Miri

Currently we're using some specific crates (`sptr` and in the future back to `core::ptr::*`) to ensure that we're compatible with [Strict Provenance][sp-issue]. The following `MIRIFLAGS` setup should enable checking to make sure that we're compatible.

```bash
MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-symbolic-alignment-check" cargo +nightly miri test
```

I think this is useful because we're doing some pointer times with our tagged pointers implementation, mutating the contents of the pointer to store bits of data.

[sp-issue]: https://github.com/rust-lang/rust/issues/95228

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

To run the benchmarks, install [`cargo-criterion`][cargo-criterion], then run:

```bash
cargo +nightly criterion --history-id "$(git rev-parse --short HEAD)-0"
```

If you get a "Permission denied" error, update perf_event_paranoid:
```bash
sudo sh -c 'echo 1 >/proc/sys/kernel/perf_event_paranoid'
```
For further details please take a look at the following [link][superuser-run-perf].

[cargo-criterion]: https://github.com/bheisler/cargo-criterion
[superuser-run-perf]: https://superuser.com/questions/980632/run-perf-without-root-rights

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
