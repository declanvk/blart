use std::{
    intrinsics::{assume, likely, unlikely},
    mem::MaybeUninit,
};

use typed_arena::Arena;

use crate::{
    AsBytes, HeaderNode, InnerNode, InnerNode256, InnerNode48, InnerNodeCompressed, LeafNode,
    OpaqueNodePtr,
};

#[repr(transparent)]
pub struct StackArenaRef(usize);

pub struct StackArena<T> {
    data: Vec<MaybeUninit<T>>,
    n: usize
}

impl<T> StackArena<T> {
    pub fn new(n: usize) -> Self {
        Self {
            data: Vec::new(),
            n
        }
    }

    pub fn push(&mut self) -> StackArenaRef {
        self.data.reserve(self.n);
        let old_len = self.data.len();
        let new_len = old_len + self.n;
        unsafe { self.data.set_len(new_len) };
        StackArenaRef(old_len)
    }

    pub fn get(&mut self, idx: StackArenaRef) -> &mut [MaybeUninit<T>] {
        &mut self.data[idx.0..(idx.0+self.n)]
    }

    pub fn pop(&mut self) {
        unsafe { self.data.set_len(self.data.len() - self.n) }
    }
}

// #[inline(never)]
fn edit_dist(
    key: &[u8],
    c: u8,
    old: &[usize],
    new: &mut [MaybeUninit<usize>],
    max_edit_dist: usize,
) -> bool {
    unsafe {
        assume(old.len() == new.len());
        assume(old.len() >= 1);
        assume(key.len() + 1 == old.len());
    }

    let first = *new[0].write(old[0] + 1);
    let mut keep = first <= max_edit_dist;
    for i in 1..new.len() {
        unsafe {
            let b = *key.get_unchecked(i - 1) == c;
            let k1 = b as usize;
            let k2 = !b as usize;
            let v1 = k1 * *old.get_unchecked(i - 1);
            let v2 = k2
                * ((*old.get_unchecked(i - 1))
                    .min(*old.get_unchecked(i))
                    .min(new.get_unchecked(i - 1).assume_init())
                    + 1);
            let v = *new.get_unchecked_mut(i).write(v1 + v2);

            keep |= v <= max_edit_dist;
        }
    }
    keep
}

#[inline(always)]
unsafe fn swap(old_row: &mut &mut [usize], new_row: &mut &mut [MaybeUninit<usize>]) {
    let temp = unsafe { std::mem::transmute(old_row) };
    std::mem::swap(temp, new_row);
}

pub struct FuzzyNode<'a, K, V> {
    pub node: OpaqueNodePtr<K, V>,
    pub old_row: &'a mut [usize],
}

impl<'a, K: AsBytes, V> FuzzyNode<'a, K, V> {
    pub fn new(node: OpaqueNodePtr<K, V>, old_row: &'a mut [usize]) -> Self {
        Self { node, old_row }
    }
}

pub trait FuzzySearch<K, V> {
    fn fuzzy_search<'s, 'a>(
        &'s self,
        arena: &'a Arena<usize>,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut &mut [MaybeUninit<usize>],
        fuzzy_nodes: &mut Vec<FuzzyNode<K, V>>,
        results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    );

    #[inline(always)]
    fn fuzzy_search_prefix(
        &self,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut &mut [MaybeUninit<usize>],
        max_edit_dist: usize,
    ) -> bool
    where
        Self: HeaderNode,
    {
        let prefix = self.header().read_prefix();
        let mut keep = true;
        for k in prefix {
            keep &= edit_dist(key, *k, &fuzzy_node.old_row, new_row, max_edit_dist);
            unsafe { swap(&mut fuzzy_node.old_row, new_row) };
        }
        keep
    }
}

impl<K: AsBytes, V, const SIZE: usize> FuzzySearch<K, V> for InnerNodeCompressed<K, V, SIZE> {
    fn fuzzy_search<'s, 'a>(
        &'s self,
        arena: &'a Arena<usize>,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut &mut [MaybeUninit<usize>],
        fuzzy_nodes: &mut Vec<FuzzyNode<K, V>>,
        _results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        if !self.fuzzy_search_prefix(key, fuzzy_node, new_row, max_edit_dist) {
            return;
        }

        let (keys, nodes) = self.initialized_portion();
        for (k, node) in keys.iter().zip(nodes) {
            let mut new_row = unsafe { arena.alloc_uninitialized(key.len() + 1) };
            if edit_dist(key, *k, &fuzzy_node.old_row, &mut new_row, max_edit_dist) {
                let fuzzy_node = FuzzyNode::new(*node, unsafe { std::mem::transmute(new_row) });
                fuzzy_nodes.push(fuzzy_node);
            }
        }
    }
}

impl<K: AsBytes, V> FuzzySearch<K, V> for InnerNode48<K, V> {
    fn fuzzy_search<'s, 'a>(
        &'s self,
        arena: &'a Arena<usize>,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut &mut [MaybeUninit<usize>],
        fuzzy_nodes: &mut Vec<FuzzyNode<K, V>>,
        _results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        if !self.fuzzy_search_prefix(key, fuzzy_node, new_row, max_edit_dist) {
            return;
        }

        let child_pointers = self.initialized_child_pointers();
        for (k, index) in self.child_indices.iter().enumerate() {
            if index.is_empty() {
                continue;
            }
            let mut new_row = unsafe { arena.alloc_uninitialized(key.len() + 1) };
            if edit_dist(
                key,
                k as u8,
                &fuzzy_node.old_row,
                &mut new_row,
                max_edit_dist,
            ) {
                let node = child_pointers[usize::from(*index)];
                let fuzzy_node = FuzzyNode::new(node, unsafe { std::mem::transmute(new_row) });
                fuzzy_nodes.push(fuzzy_node);
            }
        }
    }
}

impl<K: AsBytes, V> FuzzySearch<K, V> for InnerNode256<K, V> {
    fn fuzzy_search<'s, 'a>(
        &'s self,
        arena: &'a Arena<usize>,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut &mut [MaybeUninit<usize>],
        fuzzy_nodes: &mut Vec<FuzzyNode<K, V>>,
        _results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        if !self.fuzzy_search_prefix(key, fuzzy_node, new_row, max_edit_dist) {
            return;
        }

        for (k, node) in self.child_pointers.iter().enumerate() {
            let Some(node) = node else {
                continue;
            };
            let mut new_row = unsafe { arena.alloc_uninitialized(key.len() + 1) };
            if edit_dist(
                key,
                k as u8,
                &fuzzy_node.old_row,
                &mut new_row,
                max_edit_dist,
            ) {
                let fuzzy_node = FuzzyNode::new(*node, unsafe { std::mem::transmute(new_row) });
                fuzzy_nodes.push(fuzzy_node);
            }
        }
    }
}

impl<K: AsBytes, V> FuzzySearch<K, V> for LeafNode<K, V> {
    fn fuzzy_search<'s, 'a>(
        &'s self,
        _arena: &'a Arena<usize>,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut &mut [MaybeUninit<usize>],
        _fuzzy_nodes: &mut Vec<FuzzyNode<K, V>>,
        results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        let current_len = fuzzy_node.old_row[0];
        let remaining_key = &self.key_ref().as_bytes()[current_len..];
        for k in remaining_key {
            edit_dist(key, *k, &fuzzy_node.old_row, new_row, max_edit_dist);
            unsafe { swap(&mut fuzzy_node.old_row, new_row) };
        }
        let edit_dist = *fuzzy_node.old_row.last().unwrap();
        if edit_dist <= max_edit_dist {
            results.push(self.entry_ref());
        }
    }
}
