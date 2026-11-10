use alloc::{boxed::Box, collections::BTreeMap, vec::Vec};
use core::ops::Bound;

use rand::{RngCore, SeedableRng, rngs::SmallRng};

use crate::{TreeMap, visitor::WellFormedChecker};

/// Build a tree with a small `PREFIX_LEN` from keys which share long runs of
/// bytes, so that most inner nodes have prefixes which are skipped by the
/// search. Then check range and prefix iterators, point lookups, and removes
/// against a [`BTreeMap`] model, for search keys which diverge from the tree
/// at random depths.
fn optimistic_descent_with_long_shared_runs<const PREFIX_LEN: usize>(seed: u64) {
    let mut state = SmallRng::seed_from_u64(seed);
    let mut next = move || state.next_u64();

    let base: Vec<u8> = (0..40).map(|_| (next() % 3) as u8).collect();
    let mut tree = TreeMap::<Box<[u8]>, usize, PREFIX_LEN>::with_prefix_len();
    let mut model = BTreeMap::<Box<[u8]>, usize>::new();
    let mut keys: Vec<Vec<u8>> = Vec::new();

    let num_keys = if cfg!(miri) { 40 } else { 200 };
    for value in 0..num_keys {
        let mut key = if keys.is_empty() || next() % 4 == 0 {
            base.clone()
        } else {
            keys[(next() % keys.len() as u64) as usize].clone()
        };
        let idx = (next() % key.len() as u64) as usize;
        key[idx] = (next() % 3) as u8;
        let key: Box<[u8]> = key.into_boxed_slice();
        if tree.try_insert(key.clone(), value).is_ok() {
            model.insert(key.clone(), value);
            keys.push(key.into_vec());
        }
    }

    // Search keys derived from the tree keys, which diverge at random depths
    let mut make_query = || -> Box<[u8]> {
        let mut query = keys[(next() % keys.len() as u64) as usize].clone();
        match next() % 4 {
            0 => {},
            1 => {
                let idx = (next() % query.len() as u64) as usize;
                query[idx] = (next() % 4) as u8;
            },
            2 => query.truncate((next() % (query.len() as u64 + 1)) as usize),
            _ => query.push((next() % 4) as u8),
        }
        query.into_boxed_slice()
    };

    let num_queries = if cfg!(miri) { 40 } else { 400 };
    for _ in 0..num_queries {
        let query = make_query();
        let q: &[u8] = &query;

        assert!(
            tree.range::<[u8], _>((Bound::Included(q), Bound::Unbounded))
                .take(3)
                .eq(model
                    .range::<[u8], _>((Bound::Included(q), Bound::Unbounded))
                    .take(3)),
            "range {q:?}.. PREFIX_LEN {PREFIX_LEN}, seed {seed}"
        );
        assert!(
            tree.range::<[u8], _>((Bound::Excluded(q), Bound::Unbounded))
                .take(3)
                .eq(model
                    .range::<[u8], _>((Bound::Excluded(q), Bound::Unbounded))
                    .take(3)),
            "range ({q:?}).. PREFIX_LEN {PREFIX_LEN}, seed {seed}"
        );
        assert!(
            tree.range::<[u8], _>((Bound::Unbounded, Bound::Included(q)))
                .rev()
                .take(3)
                .eq(model
                    .range::<[u8], _>((Bound::Unbounded, Bound::Included(q)))
                    .rev()
                    .take(3)),
            "range ..={q:?} PREFIX_LEN {PREFIX_LEN}, seed {seed}"
        );
        assert!(
            tree.range::<[u8], _>((Bound::Unbounded, Bound::Excluded(q)))
                .rev()
                .take(3)
                .eq(model
                    .range::<[u8], _>((Bound::Unbounded, Bound::Excluded(q)))
                    .rev()
                    .take(3)),
            "range ..{q:?} PREFIX_LEN {PREFIX_LEN}, seed {seed}"
        );

        let other = make_query();
        let (low, high) = if query <= other {
            (&query, &other)
        } else {
            (&other, &query)
        };
        let (low, high): (&[u8], &[u8]) = (low, high);
        assert!(
            tree.range::<[u8], _>((Bound::Included(low), Bound::Included(high)))
                .eq(model.range::<[u8], _>((Bound::Included(low), Bound::Included(high)))),
            "range {low:?}..={high:?} PREFIX_LEN {PREFIX_LEN}, seed {seed}"
        );

        assert!(
            tree.prefix(q)
                .eq(model.iter().filter(|(key, _)| key.starts_with(q))),
            "prefix {q:?} PREFIX_LEN {PREFIX_LEN}, seed {seed}"
        );

        // Point lookups use the same search, so check them here as well
        assert_eq!(
            tree.get(q),
            model.get(q),
            "get {q:?} PREFIX_LEN {PREFIX_LEN}, seed {seed}"
        );
        assert_eq!(
            tree.prefix_get_key_value(q),
            model.iter().find(|(key, _)| q.starts_with(key)),
            "prefix_get {q:?} PREFIX_LEN {PREFIX_LEN}, seed {seed}"
        );
    }

    // Remove keys with the same kind of search keys, some of which will not be
    // in the tree
    for _ in 0..num_queries {
        let query = make_query();
        let q: &[u8] = &query;
        assert_eq!(
            tree.remove(q),
            model.remove(q),
            "remove {q:?} PREFIX_LEN {PREFIX_LEN}, seed {seed}"
        );
        WellFormedChecker::check(&tree).unwrap_or_else(|err| {
            panic!(
                "tree malformed after removing {q:?}, PREFIX_LEN {PREFIX_LEN}, seed {seed}: {err}"
            )
        });
    }
    assert!(tree.iter().eq(model.iter()));
}

#[test]
fn optimistic_descent_with_long_shared_runs_small_prefix_len() {
    let num_seeds = if cfg!(miri) { 1 } else { 8 };
    for seed in 1..=num_seeds {
        optimistic_descent_with_long_shared_runs::<0>(seed);
        optimistic_descent_with_long_shared_runs::<1>(seed);
        optimistic_descent_with_long_shared_runs::<2>(seed);
        optimistic_descent_with_long_shared_runs::<4>(seed);
        optimistic_descent_with_long_shared_runs::<8>(seed);
        optimistic_descent_with_long_shared_runs::<16>(seed);
    }
}
