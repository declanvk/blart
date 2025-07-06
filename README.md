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
let mut movie_reviews: TreeMap<_, _> = TreeMap::new();

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
cargo +nightly fuzz run -j 8 -s address tree_map_api -- -max_len=32768 -max_total_time=3600 && cargo +nightly fuzz cmin tree_map_api
```

This will run the fuzzer for a total of 3600 seconds (1 hour), using 8 jobs (half of the total number of cores on my dev box), and using the address sanitizer. The `cmin` command is used to compact the corpus after generating new entries.

### Coverage

To generate coverage reports from fuzzing corpus:

```bash
TARGET_TRIPLE="$(rustc --print host-tuple)"
"$(rustc --print sysroot)/lib/rustlib/${TARGET_TRIPLE}/bin/llvm-cov" show \
  --show-instantiations --show-line-counts-or-regions --Xdemangler=rustfilt --format=html \
  --ignore-filename-regex='\.cargo/registry' --ignore-filename-regex='rustlib/src/rust/' \
  --instr-profile=fuzz/coverage/tree_map_api/coverage.profdata \
  "target/${TARGET_TRIPLE}/coverage/${TARGET_TRIPLE}/release/tree_map_api" > cov.html
```

View the `cov.html` in the browser. To see a summary of coverage, broken down by file:

```bash
TARGET_TRIPLE="$(rustc --print host-tuple)"
"$(rustc --print sysroot)/lib/rustlib/${TARGET_TRIPLE}/bin/llvm-cov" report \
  --Xdemangler=rustfilt --show-branch-summary=false --show-functions --use-color \
  --ignore-filename-regex='\.cargo/registry' --ignore-filename-regex='rustlib/src/rust/' \
  --instr-profile=fuzz/coverage/tree_map_api/coverage.profdata \
  "target/${TARGET_TRIPLE}/coverage/${TARGET_TRIPLE}/release/tree_map_api" \
  "src/" | less --chop-long-lines --RAW-CONTROL-CHARS
```

## Benchmarks

To run the benchmarks, install [`cargo-criterion`][cargo-criterion], then run:

```bash
cargo +nightly criterion --history-id "$(git rev-parse --short HEAD)-0" --features bench-perf-events
```

or

```bash
cargo bench --bench <bench_name> --features bench-perf-events
```

If you get a "Permission denied" error, update perf_event_paranoid:
```bash
sudo sh -c 'echo 1 >/proc/sys/kernel/perf_event_paranoid'
```
For further details please take a look at the following [link][superuser-run-perf].

[cargo-criterion]: https://github.com/bheisler/cargo-criterion
[superuser-run-perf]: https://superuser.com/questions/980632/run-perf-without-root-rights

## Profiling

I use a somewhat realistic benchmark: counting words in a text file. To get started, download a text file like:

```bash
curl -o profiling-data/Ulysses.txt https://www.gutenberg.org/cache/epub/4300/pg4300.txt
```

Then build the word count example using the `profiling` profile:

```bash
RUSTFLAGS="-C force-frame-pointers=yes" cargo build --profile profiling --examples
```

Then run the count words workload on the downloaded data while profiling:

```bash
samply record ./target/profiling/examples/count_words blart profiling-data/book-chapters-combined.txt
```

## Mutation Testing

> cargo-mutants helps you improve your program's quality by finding places where bugs could be inserted without causing any tests to fail.

 - https://github.com/sourcefrog/cargo-mutants
 - https://mutants.rs/

To get the initial list of failed mutants, run:

```bash
cargo mutants
```

To iterate on an existing `mutants.out` directory, update the code with more tests and run:

```bash
cargo mutants --iterate
```

If you want to run mutants for a specific file, use:

```bash
cargo mutants -f example.rs
```

If you have `cargo-nextest` installed, you can add `--test-tool=nextest` to the CLI invocations.

To get the current list of mutants:

```bash
cargo mutants --iterate --list | sort
```

The `sort` call is useful to group files together.

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
