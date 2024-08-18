# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

<!-- next-header -->

## [Unreleased] - ReleaseDate

## [0.2.0] - 2024-08-18

The 0.2.0 has been entirely (99%) contributed by @Gab-Menezes, thank you for all the new features!

Some of the most exciting work they did was to re-implement much of the inner node lookups using SIMD-accelerated searches! The `nightly` feature turns on these optimizations using the new `std::simd` modules. The optimization here also include tactical use of the `likely`, `unlikely`, and `assume` hints to provide the compiler with better optimization material.

They also implemented the "implicit" prefix optimization from the original ART paper, where inner node prefixes longer than X bytes are only stored to X bytes. This means removing the `SmallVec<[u8; X]>` that was previously used to store bytes, which removes the allocation, and overall reduces the memory used.

### Added

 - `TreeMap::entry*` API was added with `try_entry` and `entry_ref` variants. This allows for query and mutating with a single `TreeMap` API call, and can reduce the overhead of a read + mutation.
 - Added `TreeMap::fuzzy*` iterator APIs which iterate over keys based on an initial key and a bound on the Levenshtein distance from the original key.
 - Added `TreeMap::prefix*` iterator APIs which iterate over keys whose prefix is equal to a given argument
 - The `ConcatTuple` type been added so that users can quickly construct a `BytesMapping` for a collection of heterogenous types that individually implement `BytesMapping`. The `ConcatTuple` uses a little bit of type-level mapping, so the generated docs are not the cleanest.
 - Implement `BytesMapping` for a restricted set of integer arrays and integer types, which need to be transformed in order for their byte representation to satisfy the `OrderedBytes` trait.

### Changed

 - Increase MSRV to 1.78
 - Added new `const PREFIX_LEN: usize` const generic to the `TreeMap` type, with a default value of `16`. This type controls the number of bytes used in each inner node header for storing compressed prefixes. More bytes means storing longer prefixes without without falling back to the implicit prefix, which makes some insertion cases slower. Less bytes means less overall memory usage, and could possibly speed-up lookups.
     - This type parameter was added to a lot of other places as well, other functions and traits.
 - For the visitor types (`DotPrinter`, `WellFormedChecker`, `TreeStatsCollector`) the functions used to run the visitor on the `TreeMap` are now safe.
 - The `TreeStatsCollector` now returns additional stats, grouped by node type.
 - Reworked the `BytesMapping` trait so that it is generic over the input type as well, allowing for transformations which can convert multiple different types into bytes.

### Removed

 - Removed implementation of `OrderedBytes` on `[{bool,char,NonZero<*>,i/u-integers}]`. This was replace in favour of restricted implementations on `Vec<T>` or `Box<[T]>` instead.
 - Removed the unimplemented `DrainFilter` and some other iterator types that were just stub implementations.

## [0.1.2] - 2023-02-13

### Changed
 - Added more folder (`.github/` & others) to the crate `exclude` list so they
   aren't included in the packaged crate.

## [0.1.1] - 2023-02-13

### Changed
 - Updated crate description

## [0.1.0] - 2023-02-13

### Added

The `blart` crate is an implementation of an adaptive radix tree (ART) which is a fast and space-efficient in-memory indexing structure.

The `0.1.0` release includes:
 - An implementation of a `TreeMap` interface, mirroring the `BTreeMap` interface that `std` provides
 - Access to the raw node-level types of the tree
 - Visitor types for visualizing the tree, gathering statistics about the nodes in the tree, and checked the well-formed-ness of the tree.
 - Traits for transforming common types into byte slices to use as keys into the tree
 - Feature flags for switching between nightly APIs and stable APIs. By default the crate works with stable, but can opt-in to nightly usage in some places.

The minimum supported Rust version at this version is 1.67.

The crate is tested several ways:
 - Fuzz tests running separately on the node-level interface and the map-level interface
 - The Github Actions CI runs `miri` on the unit test suite
 - There are tests using `dhat-rs` that assert on the maximum heap usage of the
   tree, and unit tests for the sizes of the different node types.

<!-- next-url -->
[Unreleased]: https://github.com/declanvk/wall-a/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/declanvk/blart/compare/v0.1.2...v0.2.0
[0.1.2]: https://github.com/declanvk/blart/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/declanvk/blart/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/declanvk/blart/compare/54af3b8...v0.1.0
