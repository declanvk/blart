# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

<!-- next-header -->

## [Unreleased] - ReleaseDate

### Added

TODO

### Changed

TODO

### Removed

TODO

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
[Unreleased]: https://github.com/declanvk/blart/compare/v0.1.2...HEAD
[0.1.2]: https://github.com/declanvk/blart/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/declanvk/blart/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/declanvk/blart/compare/54af3b8...v0.1.0
