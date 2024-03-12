use std::intrinsics::assume;

use crate::{
    AsBytes, HeaderNode, InnerNode, InnerNode256, InnerNode48, InnerNodeCompressed, LeafNode, OpaqueNodePtr
};

fn edit_dist(key: &[u8], c: u8, old: &[usize], new: &mut [usize], max_edit_dist: usize) -> bool {
    unsafe {
        assume(old.len() == new.len());
        assume(old.len() >= 1);
        assume(key.len() + 1 == old.len());
    }

    new[0] = old[0] + 1;
    let mut keep = new[0] <= max_edit_dist;
    for i in 1..new.len() {
        // let cost = (key[i - 1] == c) as usize;
        // new[i] = (old[i - 1] + cost).min(old[i] + 1).min(new[i-1] + 1);

        new[i] = if unsafe { *key.get_unchecked(i - 1) } == c {
            // new[i] = old[i - 1];
            unsafe { *old.get_unchecked(i - 1) }
        } else {
            // new[i] = (old[i - 1] + 1).min(old[i] + 1).min(new[i-1] + 1);
            unsafe {
                (*old.get_unchecked(i - 1) + 1)
                    .min(*old.get_unchecked(i) + 1)
                    .min(*new.get_unchecked(i - 1) + 1)
            }
        };
        keep |= new[i] <= max_edit_dist;
    }
    keep
}

pub struct FuzzyNode<K, V> {
    pub node: OpaqueNodePtr<K, V>,
    pub old_row: Vec<usize>,
}

impl<K: AsBytes, V> FuzzyNode<K, V> {
    pub fn new(node: OpaqueNodePtr<K, V>, old_row: Vec<usize>) -> Self {
        Self { node, old_row }
    }
}

pub trait FuzzySearch<K, V> {
    fn fuzzy_search<'a>(
        &'a self,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut Vec<usize>,
        fuzzy_nodes: &mut Vec<FuzzyNode<K, V>>,
        results: &mut Vec<(&'a K, &'a V)>,
        max_edit_dist: usize,
    );

    #[inline(always)]
    fn fuzzy_search_prefix(
        &self,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut Vec<usize>,
        max_edit_dist: usize,
    ) -> bool
    where
        Self: HeaderNode,
    {
        let prefix = self.header().read_prefix();
        let mut keep = true;
        for k in prefix {
            keep &= edit_dist(key, *k, &fuzzy_node.old_row, new_row, max_edit_dist);
            std::mem::swap(&mut fuzzy_node.old_row, new_row);
        }
        keep
    }
}

impl<K: AsBytes, V, const SIZE: usize> FuzzySearch<K, V> for InnerNodeCompressed<K, V, SIZE> {
    fn fuzzy_search<'a>(
        &'a self,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut Vec<usize>,
        fuzzy_nodes: &mut Vec<FuzzyNode<K, V>>,
        _: &mut Vec<(&'a K, &'a V)>,
        max_edit_dist: usize,
    ) {
        if !self.fuzzy_search_prefix(key, fuzzy_node, new_row, max_edit_dist) {
            return;
        }

        let (keys, nodes) = self.initialized_portion();
        for (k, node) in keys.iter().zip(nodes) {
            let mut new_row = vec![0usize; key.len() + 1];
            if edit_dist(key, *k, &fuzzy_node.old_row, &mut new_row, max_edit_dist) {
                let fuzzy_node = FuzzyNode::new(*node, new_row);
                fuzzy_nodes.push(fuzzy_node);
            }
        }
    }
}

impl<K: AsBytes, V> FuzzySearch<K, V> for InnerNode48<K, V> {
    fn fuzzy_search<'a>(
        &'a self,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut Vec<usize>,
        fuzzy_nodes: &mut Vec<FuzzyNode<K, V>>,
        _: &mut Vec<(&'a K, &'a V)>,
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
            let mut new_row = vec![0usize; key.len() + 1];
            if edit_dist(
                key,
                k as u8,
                &fuzzy_node.old_row,
                &mut new_row,
                max_edit_dist,
            ) {
                let node = child_pointers[usize::from(*index)];
                let fuzzy_node = FuzzyNode::new(node, new_row);
                fuzzy_nodes.push(fuzzy_node);
            }
        }
    }
}

impl<K: AsBytes, V> FuzzySearch<K, V> for InnerNode256<K, V> {
    fn fuzzy_search<'a>(
        &'a self,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut Vec<usize>,
        fuzzy_nodes: &mut Vec<FuzzyNode<K, V>>,
        _: &mut Vec<(&'a K, &'a V)>,
        max_edit_dist: usize,
    ) {
        if !self.fuzzy_search_prefix(key, fuzzy_node, new_row, max_edit_dist) {
            return;
        }

        for (k, node) in self.child_pointers.iter().enumerate() {
            let Some(node) = node else {
                continue;
            };
            let mut new_row = vec![0usize; key.len() + 1];
            if edit_dist(
                key,
                k as u8,
                &fuzzy_node.old_row,
                &mut new_row,
                max_edit_dist,
            ) {
                let fuzzy_node = FuzzyNode::new(*node, new_row);
                fuzzy_nodes.push(fuzzy_node);
            }
        }
    }
}

impl<K: AsBytes, V> FuzzySearch<K, V> for LeafNode<K, V> {
    fn fuzzy_search<'a>(
        &'a self,
        key: &[u8],
        fuzzy_node: &mut FuzzyNode<K, V>,
        new_row: &mut Vec<usize>,
        _: &mut Vec<FuzzyNode<K, V>>,
        results: &mut Vec<(&'a K, &'a V)>,
        max_edit_dist: usize,
    ) {
        let current_len = fuzzy_node.old_row[0];
        let remaining_key = &self.key_ref().as_bytes()[current_len..];
        for k in remaining_key {
            edit_dist(key, *k, &fuzzy_node.old_row, new_row, max_edit_dist);
            std::mem::swap(&mut fuzzy_node.old_row, new_row);
        }
        let edit_dist = *fuzzy_node.old_row.last().unwrap();
        if edit_dist <= max_edit_dist {
            results.push(self.entry_ref());
        }
    }
}
