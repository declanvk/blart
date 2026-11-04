//! Fuzz the `TreeMap` API with keys whose [`AsBytes`] implementation is adversarial.
//!
//! See the "Determinism" section of the `AsBytes` docs. An implementation of
//! `AsBytes` that does not obey the restrictions of "Determinism" is considered
//! adversarial. It is the responsibility of the library to not cause UB if the
//! impl is adversarial. Additionally, it shouldn't leak memory and the tree
//! data structure should be usable after a panic (no corruption).
//!
//! However, the tree is allowed to do an arbitrary, but consistent, action on a
//! panic in an `AsBytes`. That means that we don't have an oracle to model
//! correct behavior. Instead, this fuzz target relies on:
//!  - AddressSanitizer for use-after-free, double free, and out-of-bounds access
//!  - LeakSanitizer for leaked nodes
//!  - debug assertions (enabled in the fuzz profile) which turn violated `assert_unchecked`
//!    preconditions into non-unwinding panics that abort

#![no_main]

use std::{
    cell::Cell,
    hash::{BuildHasher, Hash, Hasher, RandomState},
    mem,
    panic::{self, AssertUnwindSafe},
    sync::Once,
};

use blart::{
    map::{Entry, OccupiedEntry, PrefixEntry},
    visitor::WellFormedChecker,
    AsBytes, TreeMap,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

mod common;

use common::{Action, EntryAction, OccupiedEntryAction, PrefixEntryAction};

/// How an [`AdversarialKey`] responds to `as_bytes` calls.
#[derive(Arbitrary, Debug, Clone)]
struct KeyBehavior {
    /// The `n`th call to `as_bytes` returns `responses[n % responses.len()]`, or an empty slice if
    /// there are no responses.
    responses: Vec<Vec<u8>>,
    /// Panic on this call to `as_bytes` (counting from 0), only once.
    panic_on_call: Option<u8>,
}

#[derive(Debug, Clone)]
struct AdversarialKey {
    behavior: KeyBehavior,
    calls: Cell<usize>,
}

impl AdversarialKey {
    /// A key which always returns the same bytes.
    fn stable(bytes: Vec<u8>) -> Self {
        KeyBehavior {
            responses: vec![bytes],
            panic_on_call: None,
        }
        .into()
    }
}

impl From<KeyBehavior> for AdversarialKey {
    fn from(behavior: KeyBehavior) -> Self {
        AdversarialKey {
            behavior,
            calls: Cell::new(0),
        }
    }
}

impl<'a> Arbitrary<'a> for AdversarialKey {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        KeyBehavior::arbitrary(u).map(Into::into)
    }
}

impl AsBytes for AdversarialKey {
    fn as_bytes(&self) -> &[u8] {
        let call = self.calls.get();
        self.calls.set(call.wrapping_add(1));

        if self.behavior.panic_on_call.map(usize::from) == Some(call) {
            panic!("adversarial panic in as_bytes");
        }

        let responses = &self.behavior.responses;
        if responses.is_empty() {
            &[]
        } else {
            &responses[call % responses.len()]
        }
    }
}

impl Hash for AdversarialKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_bytes().hash(state);
    }
}

type Tree = TreeMap<AdversarialKey, u32>;

fn apply(tree: &mut Tree, other: &mut Tree, next_value: &mut u32, action: Action<AdversarialKey>) {
    let mut value = || {
        *next_value = next_value.wrapping_add(1);
        *next_value
    };

    match action {
        Action::Clear => tree.clear(),
        Action::ContainsKey(key) => {
            let _ = tree.contains_key(&key);
        },
        Action::GetMinimum => {
            let _ = tree.first_key_value();
        },
        Action::PopMinimum => {
            let _ = tree.pop_first();
        },
        Action::GetMaximum => {
            let _ = tree.last_key_value();
        },
        Action::PopMaximum => {
            let _ = tree.pop_last();
        },
        Action::GetKey(key) => {
            if let Some(value) = tree.get_mut(&key) {
                *value = value.wrapping_add(1);
            }
        },
        Action::GetPrefixKey(key) => {
            if let Some(value) = tree.prefix_get_mut(&key) {
                *value = value.wrapping_add(1);
            }
        },
        Action::CheckLen => {
            let _ = tree.len();
        },
        Action::CheckIter => {
            tree.iter_mut()
                .for_each(|(_, value)| *value = value.wrapping_add(1));
            tree.iter_mut()
                .rev()
                .for_each(|(_, value)| *value = value.wrapping_sub(1));
        },
        Action::Remove(key) => {
            let _ = tree.remove(&key);
        },
        Action::RemovePrefix(prefix) => {
            let to_remove: Vec<_> = tree.prefix(&prefix).map(|(key, _)| key.clone()).collect();
            for key in to_remove {
                let _ = tree.remove(&key);
            }
        },
        Action::TryInsert(key) => {
            let _ = tree.try_insert(key, value());
        },
        Action::TryInsertMany(prefix, count) => {
            let mut key = Vec::from(prefix);
            key.push(0);
            for suffix in 0..=count {
                *key.last_mut().unwrap() = suffix;
                let _ = tree.try_insert(AdversarialKey::stable(key.clone()), value());
            }
        },
        Action::PrefixInsert(key) => {
            tree.prefix_insert(key, value());
        },
        Action::Clone => *other = tree.clone(),
        Action::Hash => {
            let _ = RandomState::new().hash_one(&*tree);
        },
        Action::Entry(action, key) => {
            if let Ok(entry) = tree.try_entry(key) {
                apply_entry_action(action, entry, value());
            }
        },
        Action::PrefixEntry(action, key) => {
            apply_prefix_entry_action(action, tree.prefix_entry(key), value());
        },
        Action::Fuzzy(key) => {
            let _ = tree.fuzzy(&key, 3).count();
        },
        Action::Prefix(prefix) => {
            let _ = tree.prefix(&prefix).count();
        },
        Action::IntoIter {
            take_front,
            take_back,
        } => {
            let mut it = mem::take(tree).into_iter();
            let _ = it.by_ref().take(take_front).count();
            let _ = it.rev().take(take_back).count();
        },
        Action::Range(start, end) => {
            let _ = tree.range((start.as_bound(), end.as_bound())).count();
        },
        Action::ExtractIf(start, end, kind) => {
            let _ = tree
                .extract_if((start.as_bound(), end.as_bound()), kind.predicate())
                .count();
        },
        Action::Retain(kind) => tree.retain(kind.predicate()),
        Action::SplitOff(key) => *other = tree.split_off(&key),
        Action::SwapTrees => mem::swap(tree, other),
    }
}

fn apply_entry_action(action: EntryAction, entry: Entry<'_, AdversarialKey, u32>, value: u32) {
    match action {
        EntryAction::AndModify(action) => {
            let entry = entry.and_modify(|v| *v = v.wrapping_sub(1));
            if let Some(action) = action {
                apply_entry_action(*action, entry, value);
            }
        },
        EntryAction::InsertEntry(action) => {
            let entry = entry.insert_entry(value);
            if let Some(action) = action {
                apply_occupied_entry_action(action, entry, value);
            }
        },
        EntryAction::OrDefault => {
            let _ = entry.or_default();
        },
        EntryAction::OrInsert => {
            let _ = entry.or_insert(value);
        },
        EntryAction::OrInsertWith => {
            let _ = entry.or_insert_with(|| value);
        },
        EntryAction::OrInsertWithKey => {
            let _ = entry.or_insert_with_key(|_| value);
        },
    }
}

fn apply_prefix_entry_action(
    action: PrefixEntryAction,
    entry: PrefixEntry<'_, AdversarialKey, u32>,
    value: u32,
) {
    match action {
        PrefixEntryAction::InsertEntry(action) => {
            let entry = entry.insert_entry(value);
            if let Some(action) = action {
                apply_occupied_entry_action(action, entry, value);
            }
        },
        PrefixEntryAction::OrDefault => {
            let _ = entry.or_default();
        },
        PrefixEntryAction::OrInsert => {
            let _ = entry.or_insert(value);
        },
        PrefixEntryAction::OrInsertWith => {
            let _ = entry.or_insert_with(|| value);
        },
        PrefixEntryAction::OrInsertWithKey => {
            let _ = entry.or_insert_with_key(|_| value);
        },
    }
}

fn apply_occupied_entry_action(
    action: OccupiedEntryAction,
    mut entry: OccupiedEntry<'_, AdversarialKey, u32>,
    value: u32,
) {
    match action {
        OccupiedEntryAction::Insert => {
            let _ = entry.insert(value);
        },
        OccupiedEntryAction::Remove => {
            let _ = entry.remove();
        },
    }
}

libfuzzer_sys::fuzz_target!(|actions: Vec<Action<AdversarialKey>>| {
    static SILENCE_PANICS: Once = Once::new();
    // Panics from adversarial keys are expected, so replace the libFuzzer hook (which aborts on
    // any panic) with one that does nothing. Non-unwinding panics still abort.
    SILENCE_PANICS.call_once(|| panic::set_hook(Box::new(|_| {})));

    let mut tree = Tree::new();
    let mut other = Tree::new();
    let mut next_value = 0;

    for action in actions {
        let _ = panic::catch_unwind(AssertUnwindSafe(|| {
            apply(&mut tree, &mut other, &mut next_value, action)
        }));
    }

    // Only check the structure, since a full check compares key bytes, which are allowed to be
    // inconsistent. The panic hook is silenced above, so print the error before aborting.
    for tree in [&tree, &other] {
        if let Err(err) = WellFormedChecker::check_without_ordering(tree) {
            eprintln!("tree is not structurally well-formed: {err:?}");
            std::process::abort();
        }
    }
});
