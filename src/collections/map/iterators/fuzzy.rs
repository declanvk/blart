use alloc::{boxed::Box, vec::Vec};
use core::{iter::FusedIterator, mem::MaybeUninit};

use crate::{
    allocator::{Allocator, Global},
    map::DEFAULT_PREFIX_LEN,
    raw::{
        ConcreteNodePtr, InnerNode, InnerNode256, InnerNode48, InnerNodeCompressed, LeafNode,
        OpaqueNodePtr,
    },
    AsBytes, TreeMap,
};

pub(crate) struct StackArena {
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
        // SAFETY: We just resized the vector, so it's safe
        // to get a slice
        unsafe { self.data.get_unchecked_mut(old_len..new_len) }
    }

    /// SAFETY: This function should only be called after [`Self::push`]
    ///
    /// SAFETY: The passed `buffer` must have the exact same
    /// size as the `n` from `new`
    pub fn pop_copy<'a, 'b>(
        &mut self,
        buffer: &'a mut &'b mut [MaybeUninit<usize>],
    ) -> Option<&'a mut &'b mut [usize]> {
        unsafe {
            // SAFETY: Every time we call `Self::push` the
            // vector is extended by `self.n`, so it's safe to
            // assume this
            core::hint::assert_unchecked(self.data.len() % self.n == 0);
        }

        if self.data.is_empty() {
            return None;
        }

        let begin = self.data.len() - self.n;
        let end = self.data.len();
        // SAFETY: We just checked that the vector is not empty
        // so we are sure that we have at least on `entry` (in
        // this case `self.n`) elements in the vector
        let s = unsafe { &self.data.get_unchecked(begin..end) };

        unsafe {
            // SAFETY: As said in the top level comment of the function,
            // buffer length == self.n
            core::hint::assert_unchecked(buffer.len() == s.len());
        }

        buffer.copy_from_slice(s);

        self.pop();

        // SAFETY: We just copied the data from the vector, and since we
        // expect after the `Self::push` call that the returned buffer is
        // filled with initialized data, them is safe to transmute here
        Some(unsafe {
            core::mem::transmute::<&mut &mut [core::mem::MaybeUninit<usize>], &mut &mut [usize]>(
                buffer,
            )
        })
    }

    /// SAFETY: This function should only be called after [`Self::push`]
    pub fn pop(&mut self) {
        // SAFETY: Since the inner type of the vector is trivial
        // we can just set the length to be the current one - self.n
        unsafe { self.data.set_len(self.data.len() - self.n) }
    }
}

/// SAFETY: `old` and `new` must have the same length, and be >= 1
///
/// SAFETY: `key` length + 1 == `new` or `old` length
#[inline]
pub(crate) fn edit_dist(
    key: &[u8],
    c: u8,
    old: &[usize],
    new: &mut [MaybeUninit<usize>],
    max_edit_dist: usize,
) -> bool {
    unsafe {
        // SAFETY: Covered by the top level comment
        core::hint::assert_unchecked(old.len() == new.len());
        core::hint::assert_unchecked(!old.is_empty());
        core::hint::assert_unchecked(key.len() + 1 == old.len());
    }

    let first = *new[0].write(old[0] + 1);
    let mut keep = first <= max_edit_dist;
    for i in 1..new.len() {
        // SAFETY: Given all of the safety requirements of the
        // function this `unchecked` operations are safe
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

/// SAFETY: `old_row` length == `new_row` length
#[inline]
unsafe fn swap(old_row: &mut &mut [usize], new_row: &mut &mut [MaybeUninit<usize>]) {
    // SAFETY: It's safe to transmute initialized data to uninitialized
    let temp = unsafe {
        core::mem::transmute::<&mut &mut [usize], &mut &mut [core::mem::MaybeUninit<usize>]>(
            old_row,
        )
    };
    core::mem::swap(temp, new_row);
}

trait FuzzySearch<K: AsBytes, V, const PREFIX_LEN: usize> {
    fn fuzzy_search(
        &self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, PREFIX_LEN>>,
        max_edit_dist: usize,
    ) -> bool;

    #[inline]
    fn fuzzy_search_prefix(
        &self,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        max_edit_dist: usize,
    ) -> bool
    where
        Self: InnerNode<PREFIX_LEN>,
        Self::Key: AsBytes,
    {
        // We can use the fact that the first entry in the old_row holds,
        // the length of how many bytes we used so far, so this becomes de depth

        // SAFETY: `old_row` length >= 1, since it's length is defined as
        // key len + 1
        let (prefix, _) = unsafe { self.read_full_prefix(*old_row.first().unwrap_unchecked()) };
        let mut keep = true;
        for k in prefix {
            keep &= edit_dist(key, *k, old_row, new_row, max_edit_dist);
            // SAFETY: We know that `old_row` length == `new_row` length
            unsafe { swap(old_row, new_row) };
        }
        keep
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize, const SIZE: usize> FuzzySearch<K, V, PREFIX_LEN>
    for InnerNodeCompressed<K, V, PREFIX_LEN, SIZE>
where
    Self: InnerNode<PREFIX_LEN, Key = K, Value = V>,
{
    fn fuzzy_search(
        &self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, PREFIX_LEN>>,
        max_edit_dist: usize,
    ) -> bool {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return false;
        }

        for (k, node) in self.iter() {
            let new_row = arena.push();
            if edit_dist(key, k, old_row, new_row, max_edit_dist) {
                nodes_to_search.push(node);
            } else {
                arena.pop();
            }
        }
        false
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> FuzzySearch<K, V, PREFIX_LEN>
    for InnerNode48<K, V, PREFIX_LEN>
{
    fn fuzzy_search(
        &self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, PREFIX_LEN>>,
        max_edit_dist: usize,
    ) -> bool {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return false;
        }

        for (k, node) in self.iter() {
            let new_row = arena.push();
            if edit_dist(key, k, old_row, new_row, max_edit_dist) {
                nodes_to_search.push(node);
            } else {
                arena.pop();
            }
        }
        false
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> FuzzySearch<K, V, PREFIX_LEN>
    for InnerNode256<K, V, PREFIX_LEN>
{
    fn fuzzy_search(
        &self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, PREFIX_LEN>>,
        max_edit_dist: usize,
    ) -> bool {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return false;
        }

        for (k, node) in self.iter() {
            let new_row = arena.push();
            if edit_dist(key, k, old_row, new_row, max_edit_dist) {
                nodes_to_search.push(node);
            } else {
                arena.pop()
            }
        }
        false
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> FuzzySearch<K, V, PREFIX_LEN>
    for LeafNode<K, V, PREFIX_LEN>
{
    fn fuzzy_search(
        &self,
        _arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        _nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, PREFIX_LEN>>,
        max_edit_dist: usize,
    ) -> bool {
        let current_len = old_row[0];
        // SAFETY: Since the `old_row` holds the current edit distance
        // it's by construction that the first value of the buffer is the
        // length of the already examined bytes of the key
        let remaining_key = unsafe { self.key_ref().as_bytes().get_unchecked(current_len..) };
        for k in remaining_key {
            edit_dist(key, *k, old_row, new_row, max_edit_dist);
            // SAFETY: We know that `old_row` length == `new_row` length
            unsafe { swap(old_row, new_row) };
        }
        // SAFETY: By the construction `old_row` always has at least one
        // element
        let edit_dist = unsafe { *old_row.last().unwrap_unchecked() };

        edit_dist <= max_edit_dist
    }
}

macro_rules! gen_iter {
    ($name:ident, $tree:ty, $ret:ty, $op:ident) => {
        /// An iterator over all the `LeafNode`s within a specific edit distance
        pub struct $name<
            'a,
            'b,
            K,
            V,
            const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN,
            A: Allocator = Global,
        > {
            nodes_to_search: Vec<OpaqueNodePtr<K, V, PREFIX_LEN>>,
            old_row: Box<[MaybeUninit<usize>]>,
            new_row: Box<[MaybeUninit<usize>]>,
            arena: StackArena,
            max_edit_dist: usize,
            key: &'b [u8],

            size: usize,
            _tree: $tree,
        }

        impl<'a, 'b, K: AsBytes, V, const PREFIX_LEN: usize, A: Allocator>
            $name<'a, 'b, K, V, PREFIX_LEN, A>
        {
            pub(crate) fn new(tree: $tree, key: &'b [u8], max_edit_dist: usize) -> Self {
                let mut arena = StackArena::new(key.len() + 1);
                let n = arena.size();
                let s = arena.push();

                for i in 0..n {
                    s[i].write(i);
                }

                Self {
                    nodes_to_search: tree
                        .state
                        .as_ref()
                        .map(|state| state.root)
                        .into_iter()
                        .collect(),
                    old_row: Box::new_uninit_slice(arena.size()),
                    new_row: Box::new_uninit_slice(arena.size()),
                    arena,
                    max_edit_dist,
                    key,

                    size: tree.num_entries,
                    _tree: tree,
                }
            }
        }

        impl<'a, 'b, K: AsBytes, V, A: Allocator, const PREFIX_LEN: usize> Iterator
            for $name<'a, 'b, K, V, PREFIX_LEN, A>
        {
            type Item = $ret;

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                let mut old_row = self.old_row.as_mut();
                let mut new_row = self.new_row.as_mut();

                while let (Some(node), Some(old_row)) = (
                    self.nodes_to_search.pop(),
                    self.arena.pop_copy(&mut old_row),
                ) {
                    match node.to_node_ptr() {
                        ConcreteNodePtr::Node4(inner_ptr) => {
                            // SAFETY: Since `Self` holds a mutable/shared reference
                            // is safe to create a shared reference from it
                            let inner_node = unsafe { inner_ptr.as_ref() };
                            inner_node.fuzzy_search(
                                &mut self.arena,
                                self.key,
                                old_row,
                                &mut new_row,
                                &mut self.nodes_to_search,
                                self.max_edit_dist,
                            );
                        },
                        ConcreteNodePtr::Node16(inner_ptr) => {
                            // SAFETY: Since `Self` holds a mutable/shared reference
                            // is safe to create a shared reference from it
                            let inner_node = unsafe { inner_ptr.as_ref() };
                            inner_node.fuzzy_search(
                                &mut self.arena,
                                self.key,
                                old_row,
                                &mut new_row,
                                &mut self.nodes_to_search,
                                self.max_edit_dist,
                            );
                        },
                        ConcreteNodePtr::Node48(inner_ptr) => {
                            // SAFETY: Since `Self` holds a mutable/shared reference
                            // is safe to create a shared reference from it
                            let inner_node = unsafe { inner_ptr.as_ref() };
                            inner_node.fuzzy_search(
                                &mut self.arena,
                                self.key,
                                old_row,
                                &mut new_row,
                                &mut self.nodes_to_search,
                                self.max_edit_dist,
                            );
                        },
                        ConcreteNodePtr::Node256(inner_ptr) => {
                            // SAFETY: Since `Self` holds a mutable/shared reference
                            // is safe to create a shared reference from it
                            let inner_node = unsafe { inner_ptr.as_ref() };
                            inner_node.fuzzy_search(
                                &mut self.arena,
                                self.key,
                                old_row,
                                &mut new_row,
                                &mut self.nodes_to_search,
                                self.max_edit_dist,
                            );
                        },
                        ConcreteNodePtr::LeafNode(inner_ptr) => {
                            self.size -= 1;

                            // SAFETY: Since `Self` holds a mutable/shared reference
                            // is safe to create a shared reference from it
                            let inner_node = unsafe { inner_ptr.as_ref() };
                            if inner_node.fuzzy_search(
                                &mut self.arena,
                                self.key,
                                old_row,
                                &mut new_row,
                                &mut self.nodes_to_search,
                                self.max_edit_dist,
                            ) {
                                return unsafe { Some(inner_ptr.$op()) };
                            }
                        },
                    };
                }

                None
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (0, Some(self.size))
            }
        }

        impl<'a, 'b, K: AsBytes, V, A: Allocator, const PREFIX_LEN: usize> FusedIterator
            for $name<'a, 'b, K, V, PREFIX_LEN, A>
        {
        }
    };
}

// SAFETY: Since we hold a shared reference is safe to
// create a shared reference to the leaf
gen_iter!(
    Fuzzy,
    &'a TreeMap<K, V, PREFIX_LEN, A>,
    (&'a K, &'a V),
    as_key_value_ref
);

// SAFETY: This iterator is safe to `Send` across threads when the `K` and `V`
// are `Sync` because it holds a `&TreeMap<K, V>`. `&TreeMap<K, V>` is `Send`
// when `TreeMap<K, V>` is `Sync`.
//
// The other parts of this iterator are safe to send cross thread.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for Fuzzy<'_, '_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

// SAFETY: This iterator is safe to share immutable across threads because there
// is no interior mutability and the underlying tree reference is `Send`.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for Fuzzy<'_, '_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

// SAFETY: Since we hold a mutable reference is safe to
// create a mutable reference to the leaf
gen_iter!(
    FuzzyMut,
    &'a mut TreeMap<K, V, PREFIX_LEN, A>,
    (&'a K, &'a mut V),
    as_key_ref_value_mut
);

// SAFETY:
//  1. `FuzzyMut` holds a mutable reference to the original tree
//  2. `&mut T` is `Send` when `T` is `Send`
//  3. `TreeMap<K, V, PREFIX_LEN, A>` is `Send` if `K`, `V`, and `A` are all
//     `Send`
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for FuzzyMut<'_, '_, K, V, PREFIX_LEN, A>
where
    K: Send,
    V: Send,
    A: Send + Allocator,
{
}

// SAFETY:
//  1. `FuzzyMut` holds a mutable reference to the original tree
//  2. `&mut T` is `Sync` if and only if `T` is `Sync`
//  3. `TreeMap<K, V, PREFIX_LEN, A>` is `Sync` if `K`, `V`, and `A` are all
//     `Sync`
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for FuzzyMut<'_, '_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

#[cfg(test)]
mod tests;
