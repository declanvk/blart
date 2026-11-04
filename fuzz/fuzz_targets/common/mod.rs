//! Actions on a `TreeMap` that are shared between fuzz targets.

use std::ops::Bound;

use libfuzzer_sys::arbitrary::{self, Arbitrary};

#[derive(Arbitrary, Debug)]
pub enum Action<K> {
    Clear,
    ContainsKey(K),
    GetMinimum,
    PopMinimum,
    GetMaximum,
    PopMaximum,
    GetKey(K),
    GetPrefixKey(K),
    CheckLen,
    CheckIter,
    Remove(K),
    RemovePrefix(Box<[u8]>),
    TryInsert(K),
    TryInsertMany(Box<[u8]>, u8),
    PrefixInsert(K),
    Clone,
    Hash,
    Entry(EntryAction, K),
    PrefixEntry(PrefixEntryAction, K),
    Fuzzy(K),
    Prefix(Box<[u8]>),
    IntoIter {
        take_front: usize,
        take_back: usize,
    },
    Range(RangeBound<K>, RangeBound<K>),
    ExtractIf(RangeBound<K>, RangeBound<K>, RetainKind),
    Retain(RetainKind),
    /// Split the tree, replacing the second tree with the split off part
    SplitOff(K),
    /// Swap the tree with the second tree
    SwapTrees,
}

#[derive(Arbitrary, Debug)]
pub enum EntryAction {
    AndModify(Option<Box<EntryAction>>),
    InsertEntry(Option<OccupiedEntryAction>),
    OrDefault,
    OrInsert,
    OrInsertWith,
    OrInsertWithKey,
}

#[derive(Arbitrary, Debug)]
pub enum PrefixEntryAction {
    InsertEntry(Option<OccupiedEntryAction>),
    OrDefault,
    OrInsert,
    OrInsertWith,
    OrInsertWithKey,
}

#[derive(Arbitrary, Debug)]
pub enum OccupiedEntryAction {
    Insert,
    Remove,
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum RetainKind {
    All,
    None,
    Half,
}

impl RetainKind {
    /// Return a predicate which keeps entries according to this kind.
    pub fn predicate<K, V>(self) -> impl FnMut(&K, &mut V) -> bool {
        let mut i = 0u64;
        move |_, _| {
            i += 1;
            match self {
                RetainKind::All => true,
                RetainKind::None => false,
                RetainKind::Half => i % 2 == 0,
            }
        }
    }
}

#[derive(Arbitrary, Debug)]
pub enum RangeBound<K> {
    Unbounded,
    Included(K),
    Excluded(K),
}

impl<K> RangeBound<K> {
    pub fn as_bound(&self) -> Bound<&K> {
        match self {
            RangeBound::Unbounded => Bound::Unbounded,
            RangeBound::Included(k) => Bound::Included(k),
            RangeBound::Excluded(k) => Bound::Excluded(k),
        }
    }
}
