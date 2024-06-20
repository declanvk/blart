use crate::{rust_nightly_apis::box_new_uninit_slice, FuzzySearch1, AsBytes, ConcreteNodePtr, InnerNode, NodeHeader, NodePtr, OpaqueNodePtr, RawTreeMap, StackArena};
use std::{collections::VecDeque, iter::FusedIterator, mem::MaybeUninit};

/// abc
pub struct Fuzzy<
    'a,
    'b,
    K: AsBytes,
    V,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
> {
    nodes_to_search: Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
    old_row: Box<[MaybeUninit<usize>]>,
    new_row: Box<[MaybeUninit<usize>]>,
    arena: StackArena,
    max_edit_dist: usize,
    key: &'b [u8],

    size: usize,
    _tree: &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
}

impl<'a, 'b, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Fuzzy<'a, 'b, K, V, NUM_PREFIX_BYTES, H>
{
    pub(crate) fn new(tree: &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>, key: &'b [u8], max_edit_dist: usize) -> Self {
        let mut arena = StackArena::new(key.len() + 1);
        let n = arena.size();
        let s = arena.push();

        #[allow(clippy::needless_range_loop)]
        for i in 0..n {
            s[i].write(i);
        }
        
        Self {
            nodes_to_search: tree.root.into_iter().collect(),
            old_row: box_new_uninit_slice(arena.size()),
            new_row: box_new_uninit_slice(arena.size()),
            arena,
            max_edit_dist,
            key,

            size: tree.num_entries,
            _tree: tree,
        }
    }
}

impl<'a, 'b, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> Iterator for Fuzzy<'a, 'b, K, V, NUM_PREFIX_BYTES, H> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let mut old_row = self.old_row.as_mut();
        let mut new_row = self.new_row.as_mut();

        while let (Some(node), Some(old_row)) =
            (self.nodes_to_search.pop(), self.arena.pop_copy(&mut old_row))
        {
            match node.to_node_ptr() {
                ConcreteNodePtr::Node4(inner_ptr) => {
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

                    let inner_node = unsafe { inner_ptr.as_ref() };
                    if inner_node.fuzzy_search(
                        &mut self.arena,
                        self.key,
                        old_row,
                        &mut new_row,
                        &mut self.nodes_to_search,
                        self.max_edit_dist,
                    ) {
                        return Some(inner_node.entry_ref())
                    }
                },
            };
        }

        None
    }
}