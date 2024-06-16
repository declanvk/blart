use std::{intrinsics::assume, mem::MaybeUninit};

use crate::{
    AsBytes, InnerNode, InnerNode256, InnerNode48, InnerNodeCompressed, LeafNode, NodeHeader,
    OpaqueNodePtr,
};

pub struct StackArena {
    data: Vec<MaybeUninit<usize>>,
    n: usize,
}

impl StackArena {
    pub fn new(n: usize) -> Self {
        Self {
            data: Vec::new(),
            n,
        }
    }

    pub fn size(&self) -> usize {
        self.n
    }

    pub fn push(&mut self) -> &mut [MaybeUninit<usize>] {
        let old_len = self.data.len();
        let new_len = old_len + self.n;
        self.data.resize_with(new_len, MaybeUninit::uninit);
        unsafe { self.data.get_unchecked_mut(old_len..new_len) }
    }

    pub fn pop_copy<'a, 'b>(
        &mut self,
        buffer: &'a mut &'b mut [MaybeUninit<usize>],
    ) -> Option<&'a mut &'b mut [usize]> {
        unsafe {
            assume(self.data.len() % self.n == 0);
        }

        if self.data.is_empty() {
            return None;
        }

        let begin = self.data.len() - self.n;
        let end = self.data.len();
        let s = unsafe { &self.data.get_unchecked(begin..end) };

        unsafe {
            assume(buffer.len() == s.len());
        }

        buffer.copy_from_slice(s);

        self.pop();

        Some(unsafe {
            std::mem::transmute::<&mut &mut [std::mem::MaybeUninit<usize>], &mut &mut [usize]>(
                buffer,
            )
        })
    }

    pub fn pop(&mut self) {
        unsafe { self.data.set_len(self.data.len() - self.n) }
    }
}

#[inline(always)]
fn edit_dist(
    key: &[u8],
    c: u8,
    old: &[usize],
    new: &mut [MaybeUninit<usize>],
    max_edit_dist: usize,
) -> bool {
    unsafe {
        assume(old.len() == new.len());
        assume(!old.is_empty());
        assume(key.len() + 1 == old.len());
    }

    let first = *new[0].write(old[0] + 1);
    let mut keep = first <= max_edit_dist;
    for i in 1..new.len() {
        unsafe {
            let b = *key.get_unchecked(i - 1) == c;

            let k1 = b as usize;
            let k2 = !b as usize;

            let substitution = *old.get_unchecked(i - 1);
            let insertion = *old.get_unchecked(i);
            let deletion = new.get_unchecked(i - 1).assume_init();

            let v1 = k1 * substitution;
            // For some reason doing the operation in this exact order
            // generates better asm
            let v2 = k2 * (substitution.min(insertion).min(deletion) + 1);
            let v = *new.get_unchecked_mut(i).write(v1 + v2);

            // This generates worse asm than doing two multiplications
            // let substitution = *old.get_unchecked(i - 1) + !b as usize;
            // let insertion = *old.get_unchecked(i) + 1;
            // let deletion = new.get_unchecked(i - 1).assume_init() + 1;
            // let edit_dist = insertion.min(substitution).min(deletion);
            // let v = *new.get_unchecked_mut(i).write(edit_dist);

            keep |= v <= max_edit_dist;
        }
    }
    keep
}

#[inline(always)]
unsafe fn swap(old_row: &mut &mut [usize], new_row: &mut &mut [MaybeUninit<usize>]) {
    let temp = unsafe {
        std::mem::transmute::<&mut &mut [usize], &mut &mut [std::mem::MaybeUninit<usize>]>(old_row)
    };
    std::mem::swap(temp, new_row);
}

pub trait FuzzySearch<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
{
    #[allow(clippy::too_many_arguments)]
    fn fuzzy_search<'s>(
        &'s self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
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
        Self: InnerNode<NUM_PREFIX_BYTES>,
    {
        // We can use the fact that the first entry in the old_row holds,
        // the length of how many bytes we used so far, so this becomes de depth

        // SAFETY: old_row len >= 1, since it's length is defined as
        // key len + 1
        let (prefix, _) = unsafe { self.read_full_prefix(*old_row.first().unwrap_unchecked()) };
        let mut keep = true;
        for k in prefix {
            keep &= edit_dist(key, *k, old_row, new_row, max_edit_dist);
            unsafe { swap(old_row, new_row) };
        }
        keep
    }
}

impl<
        K: AsBytes,
        V,
        const NUM_PREFIX_BYTES: usize,
        H: NodeHeader<NUM_PREFIX_BYTES>,
        const SIZE: usize,
    > FuzzySearch<K, V, NUM_PREFIX_BYTES, H>
    for InnerNodeCompressed<K, V, NUM_PREFIX_BYTES, H, SIZE>
where
    Self: InnerNode<NUM_PREFIX_BYTES>,
{
    fn fuzzy_search<'s>(
        &'s self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
        _results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return;
        }

        let (keys, nodes) = self.initialized_portion();
        for (k, node) in keys.iter().zip(nodes) {
            let new_row = arena.push();
            if edit_dist(key, *k, old_row, new_row, max_edit_dist) {
                nodes_to_search.push(*node);
            } else {
                arena.pop();
            }
        }
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    FuzzySearch<K, V, NUM_PREFIX_BYTES, H> for InnerNode48<K, V, NUM_PREFIX_BYTES, H>
{
    fn fuzzy_search<'s>(
        &'s self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
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
            if edit_dist(key, k as u8, old_row, new_row, max_edit_dist) {
                let node = unsafe { *child_pointers.get_unchecked(usize::from(*index)) };
                nodes_to_search.push(node);
            } else {
                arena.pop();
            }
        }
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    FuzzySearch<K, V, NUM_PREFIX_BYTES, H> for InnerNode256<K, V, NUM_PREFIX_BYTES, H>
{
    fn fuzzy_search<'s>(
        &'s self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
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
            if edit_dist(key, k as u8, old_row, new_row, max_edit_dist) {
                nodes_to_search.push(*node);
            } else {
                arena.pop()
            }
        }
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    FuzzySearch<K, V, NUM_PREFIX_BYTES, H> for LeafNode<K, V, NUM_PREFIX_BYTES, H>
{
    fn fuzzy_search<'s>(
        &'s self,
        _arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        _nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
        results: &mut Vec<(&'s K, &'s V)>,
        max_edit_dist: usize,
    ) {
        let current_len = old_row[0];
        let remaining_key = unsafe { self.key_ref().as_bytes().get_unchecked(current_len..) };
        for k in remaining_key {
            edit_dist(key, *k, old_row, new_row, max_edit_dist);
            unsafe { swap(old_row, new_row) };
        }
        let edit_dist = unsafe { *old_row.last().unwrap_unchecked() };
        if edit_dist <= max_edit_dist {
            results.push(self.entry_ref());
        }
    }
}
