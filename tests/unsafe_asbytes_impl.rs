//! Regression test for unsafe implementations of [`AsBytes`].
//!
//! `AsBytes` is safe to implement (no `unsafe` methods and trait is safe), but asks that
//! implementers deterministically produce `&[u8]` from `&self`. However, a adversarial
//! implementation could non-deterministically produce bytes and the `TreeMap`/`TreeSet`
//! implementation must not produce UB.
//!
//! Previously there were some internal assumptions (using `assert_unchecked`), but were later
//! removed. This test is designed to run under Miri and return an error for UB if we start to make
//! unreliable assumptions yet again.

use core::cell::Cell;

use blart::{AsBytes, NoPrefixesBytes, TreeMap, visitor::WellFormedChecker};

/// A malicious `AsBytes` implemenetor that is non-deterministic.
///
/// The first call returns `first`, every later call returns `rest`.
struct Adversary {
    first: Vec<u8>,
    rest: Vec<u8>,
    calls: Cell<usize>,
}

impl Adversary {
    /// A well-behaved key.
    fn stable(bytes: Vec<u8>) -> Self {
        Adversary {
            first: bytes.clone(),
            rest: bytes,
            calls: Cell::new(0),
        }
    }

    /// A key that returns `first` on its first `as_bytes()` call and `rest`
    /// afterwards.
    fn shrinking(first: Vec<u8>, rest: Vec<u8>) -> Self {
        Adversary {
            first,
            rest,
            calls: Cell::new(0),
        }
    }
}

impl AsBytes for Adversary {
    fn as_bytes(&self) -> &[u8] {
        let n = self.calls.get();
        self.calls.set(n + 1);
        if n == 0 { &self.first } else { &self.rest }
    }
}

/// Use every leaf in the tree and then remove them all, to surface any dangling pointers left by
/// an earlier operation.
fn exercise(mut map: TreeMap<Adversary, u32>) {
    let _ = WellFormedChecker::check_without_ordering(&map).unwrap();

    while map.pop_last().is_some() {}
    assert!(map.is_empty());
}

#[test]
fn nondeterministic_as_bytes_must_not_be_ub() {
    let mut map: TreeMap<Adversary, u32> = TreeMap::new();

    map.try_insert(Adversary::stable(vec![10, 20]), 1).unwrap();

    // The insert is placed using the bytes `[10, 30]` from the search, and the key is never asked
    // for its bytes again during the insert
    map.try_insert(Adversary::shrinking(vec![10, 30], vec![10]), 2)
        .unwrap();
    assert_eq!(map.len(), 2);

    exercise(map);
}

// The insert operation previously read the key bytes multiple times, but that let to problems with
// adversarial `as_bytes` implementations. These are regression tests to confirm the issue stays
// mostly fixed.

#[test]
fn nondeterministic_as_bytes_split_leaf() {
    let mut map: TreeMap<Adversary, u32> = TreeMap::new();
    map.try_insert(Adversary::stable(vec![255]), 1).unwrap();

    // The search splits the leaf at the first byte (`126` vs `255`), a later read gives `255`
    map.try_insert(Adversary::shrinking(vec![126], vec![255]), 2)
        .unwrap();
    assert_eq!(map.len(), 2);

    exercise(map);
}

#[test]
fn nondeterministic_as_bytes_split_leaf_entry() {
    let mut map: TreeMap<Adversary, u32> = TreeMap::new();
    map.try_insert(Adversary::stable(vec![255]), 1).unwrap();

    // Same as above, but the insert point is kept in a vacant entry before it is applied
    let _ = map
        .try_entry(Adversary::shrinking(vec![126], vec![255]))
        .unwrap()
        .or_insert(2);
    assert_eq!(map.len(), 2);

    exercise(map);
}

#[test]
fn nondeterministic_as_bytes_into_existing_node() {
    let mut map: TreeMap<Adversary, u32> = TreeMap::new();
    map.try_insert(Adversary::stable(vec![1, 0]), 1).unwrap();
    map.try_insert(Adversary::stable(vec![2, 0]), 2).unwrap();

    // The search finds no child at `3` in the root, a later read gives the existing child `1`
    map.try_insert(Adversary::shrinking(vec![3, 0], vec![1, 0]), 3)
        .unwrap();
    assert_eq!(map.len(), 3);

    exercise(map);
}

#[test]
fn nondeterministic_as_bytes_mismatch_prefix() {
    let mut map: TreeMap<Adversary, u32> = TreeMap::new();
    map.try_insert(Adversary::stable(vec![1, 5, 5, 1]), 1)
        .unwrap();
    map.try_insert(Adversary::stable(vec![1, 5, 5, 2]), 2)
        .unwrap();

    // The search finds a mismatch with the root prefix `[1, 5, 5]` at `6`, a later read gives the
    // prefix byte `5`
    map.try_insert(Adversary::shrinking(vec![1, 6, 0, 0], vec![1, 5, 0, 0]), 3)
        .unwrap();
    assert_eq!(map.len(), 3);

    exercise(map);
}

#[test]
fn nondeterministic_as_bytes_extract_if() {
    let mut map: TreeMap<Adversary, u32> = TreeMap::new();
    map.try_insert(Adversary::stable(vec![193]), 1).unwrap();
    // Inserted under `173`, but claims to be `193` afterwards
    map.try_insert(Adversary::shrinking(vec![173], vec![193]), 2)
        .unwrap();

    // Removing the leaf at `173` searches for it by its key, which finds the leaf at `193`. That
    // leaf used to be freed while the iterator still pointed to it as the next leaf.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        map.extract_if(.., |_, _| true).count()
    }));
    assert!(
        result.is_err(),
        "extract_if should panic before modifying the tree"
    );
    assert_eq!(map.len(), 2);

    exercise(map);
}

#[test]
fn nondeterministic_as_bytes_fuzzy() {
    let mut map: TreeMap<Adversary, u32> = TreeMap::new();
    map.try_insert(Adversary::stable(vec![85]), 1).unwrap();
    // Inserted under `83`, but has no bytes afterwards
    map.try_insert(Adversary::shrinking(vec![83], vec![]), 2)
        .unwrap();

    // The fuzzy search reaches the second leaf after examining one key byte, and used to slice
    // that leaf's (now empty) key from index 1 without a bounds check. The result is unspecified.
    let _ = map.fuzzy(&Adversary::stable(vec![]), 3).count();

    exercise(map);
}

/// A key that always returns 4 bytes, but switches to `alt` once `flipped` is set.
///
/// This type satisfies the `NoPrefixesBytes` guarantee because every key has the same length, even
/// though they're inconsistent.
struct FixedLenFlip {
    normal: [u8; 4],
    alt: [u8; 4],
    flipped: Cell<bool>,
}

impl FixedLenFlip {
    fn new(normal: [u8; 4], alt: [u8; 4]) -> Self {
        FixedLenFlip {
            normal,
            alt,
            flipped: Cell::new(false),
        }
    }
}

impl AsBytes for FixedLenFlip {
    fn as_bytes(&self) -> &[u8] {
        if self.flipped.get() {
            &self.alt
        } else {
            &self.normal
        }
    }
}

// SAFETY: Every value of `as_bytes` is exactly 4 bytes long
unsafe impl NoPrefixesBytes for FixedLenFlip {}

/// Build a tree whose root has children `0 -> A` and `1 -> B`, then change A's bytes so the
/// search for `[0, 0, 0, 0]` reaches A and sees matching bytes from depth 1 onwards. The insert
/// search reports that as a prefix error, which `insert` and `entry` used to `unwrap_unchecked`.
fn flipped_no_prefixes_map() -> TreeMap<FixedLenFlip, u32> {
    let mut map = TreeMap::new();
    map.insert(FixedLenFlip::new([0, 0, 0, 0], [5, 0, 0, 0]), 0);
    map.insert(FixedLenFlip::new([1, 0, 0, 0], [1, 0, 0, 0]), 1);
    for key in map.keys() {
        key.flipped.set(true);
    }
    map
}

#[test]
#[should_panic = "`AsBytes` impl is inconsistent"]
fn nondeterministic_as_bytes_no_prefixes_insert() {
    let mut map = flipped_no_prefixes_map();
    map.insert(FixedLenFlip::new([0, 0, 0, 0], [0, 0, 0, 0]), 2);
}

#[test]
#[should_panic = "`AsBytes` impl is inconsistent"]
fn nondeterministic_as_bytes_no_prefixes_entry() {
    let mut map = flipped_no_prefixes_map();
    let _ = map.entry(FixedLenFlip::new([0, 0, 0, 0], [0, 0, 0, 0]));
}
