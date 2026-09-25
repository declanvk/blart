//! Regression test for unsafe implementations of [`AsBytes`].
//!
//! `AsBytes` is safe to implement (no `unsafe` methods and trait is safe), but asks that
//! implementers deterministically produce `&[u8]` from `&self`. However, a adversarial
//! implementation could non-deterministically produce and the `TreeMap`/`TreeSet` implementation
//! must not produce UB.
//!
//! Previously there were some internal assumptions (using `assert_unchecked`), but were later
//! removed. This test is designed to run under Miri and return an error for UB if we start to make
//! unreliable assumptions yet again.

use core::cell::Cell;

use blart::{AsBytes, TreeMap};

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
        if n == 0 {
            &self.first
        } else {
            &self.rest
        }
    }
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn nondeterministic_as_bytes_must_not_be_ub() {
    let mut map: TreeMap<Adversary, u32> = TreeMap::new();

    map.try_insert(Adversary::stable(vec![10, 20]), 1).unwrap();

    map.try_insert(Adversary::shrinking(vec![10, 30], vec![10]), 2)
        .unwrap();
}
