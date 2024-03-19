use std::{
    intrinsics::{assume, likely, unlikely},
    mem::MaybeUninit,
};

use typed_arena::Arena;

use crate::{
    AsBytes, HeaderNode, InnerNode, InnerNode256, InnerNode48, InnerNodeCompressed, LeafNode,
    OpaqueNodePtr,
};

pub struct StackArena<T: Copy> {
    data: Vec<MaybeUninit<T>>,
    n: usize
}

impl<T: Copy> StackArena<T> {
    pub fn new(n: usize) -> Self {
        Self {
            data: Vec::new(),
            n
        }
    }

    pub fn size(&self) -> usize {
        self.n
    }

    pub fn push(&mut self) -> &mut [MaybeUninit<T>] {
        let old_len = self.data.len();
        let new_len = old_len + self.n;
        self.data.resize_with(new_len, MaybeUninit::uninit);
        &mut self.data[old_len..new_len]
    }

    pub fn pop_copy<'a, 'b>(&mut self, buffer: &'a mut &'b mut [MaybeUninit<T>]) -> Option<&'a mut &'b mut [T]> {
        unsafe {
            assume(self.data.len() % self.n == 0);
        }

        if self.data.len() == 0 {
            return None;
        }

        let begin = self.data.len() - self.n;
        let end = self.data.len();
        buffer.copy_from_slice(&self.data[begin..end]);

        self.pop();

        Some(unsafe { std::mem::transmute(buffer) })
    }

    pub fn pop(&mut self) {
        self.data.truncate(self.data.len() - self.n);
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


pub trait FuzzySearch<K, V> {
    fn fuzzy_search<'s>(
        &'s self,
        arena: &mut StackArena<usize>,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V>>,
        results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    );

    #[inline(always)]
    fn fuzzy_search_prefix(
        &self,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        max_edit_dist: usize,
    ) -> bool
    where
        Self: HeaderNode,
    {
        let prefix = self.header().read_prefix();
        let mut keep = true;
        for k in prefix {
            keep &= edit_dist(key, *k, *old_row, *new_row, max_edit_dist);
            unsafe { swap(old_row, new_row) };
        }
        keep
    }
}

impl<K: AsBytes, V, const SIZE: usize> FuzzySearch<K, V> for InnerNodeCompressed<K, V, SIZE> {
    fn fuzzy_search<'s>(
        &'s self,
        arena: &mut StackArena<usize>,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V>>,
        _results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return;
        }

        let (keys, nodes) = self.initialized_portion();
        for (k, node) in keys.iter().zip(nodes) {
            let new_row = arena.push();
            if edit_dist(key, *k, *old_row, new_row, max_edit_dist) {
                nodes_to_search.push(*node);
            } else {
                arena.pop();
            }
        }
    }
}

impl<K: AsBytes, V> FuzzySearch<K, V> for InnerNode48<K, V> {
    fn fuzzy_search<'s>(
        &'s self,
        arena: &mut StackArena<usize>,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V>>,
        _results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return;
        }

        let child_pointers = self.initialized_child_pointers();
        for (k, index) in self.child_indices.iter().enumerate() {
            if index.is_empty() {
                continue;
            }
            let new_row = arena.push();
            if edit_dist(
                key,
                k as u8,
                *old_row,
                new_row,
                max_edit_dist,
            ) {
                let node = child_pointers[usize::from(*index)];
                nodes_to_search.push(node);
            } else {
                arena.pop();
            }
        }
    }
}

impl<K: AsBytes, V> FuzzySearch<K, V> for InnerNode256<K, V> {
    fn fuzzy_search<'s>(
        &'s self,
        arena: &mut StackArena<usize>,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V>>,
        _results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return;
        }

        for (k, node) in self.child_pointers.iter().enumerate() {
            let Some(node) = node else {
                continue;
            };
            let new_row = arena.push();
            if edit_dist(
                key,
                k as u8,
                *old_row,
                new_row,
                max_edit_dist,
            ) {
                nodes_to_search.push(*node);
            }
        }
    }
}

impl<K: AsBytes, V> FuzzySearch<K, V> for LeafNode<K, V> {
    fn fuzzy_search<'s>(
        &'s self,
        _arena: &mut StackArena<usize>,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        _nodes_to_search: &mut Vec<OpaqueNodePtr<K, V>>,
        results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        let current_len = old_row[0];
        let remaining_key = &self.key_ref().as_bytes()[current_len..];
        for k in remaining_key {
            edit_dist(key, *k, *old_row, *new_row, max_edit_dist);
            unsafe { swap(old_row, new_row) };
        }
        let edit_dist = *old_row.last().unwrap();
        if edit_dist <= max_edit_dist {
            results.push(self.entry_ref());
        }
    }
}
