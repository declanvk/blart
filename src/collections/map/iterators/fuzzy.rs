use crate::{
    rust_nightly_apis::{assume, box_new_uninit_slice},
    AsBytes, ConcreteNodePtr, InnerNode, InnerNode256, InnerNode48, InnerNodeCompressed, LeafNode,
    NodeHeader, OpaqueNodePtr, RawTreeMap,
};
use std::{iter::FusedIterator, mem::MaybeUninit};

struct StackArena {
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
        #[allow(unused_unsafe)]
        unsafe {
            assume!(self.data.len() % self.n == 0);
        }

        if self.data.is_empty() {
            return None;
        }

        let begin = self.data.len() - self.n;
        let end = self.data.len();
        let s = unsafe { &self.data.get_unchecked(begin..end) };

        #[allow(unused_unsafe)]
        unsafe {
            assume!(buffer.len() == s.len());
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
    #[allow(unused_unsafe)]
    unsafe {
        assume!(old.len() == new.len());
        assume!(!old.is_empty());
        assume!(key.len() + 1 == old.len());
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

trait FuzzySearch<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> {
    #[allow(clippy::too_many_arguments)]
    fn fuzzy_search(
        &self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
        max_edit_dist: usize,
    ) -> bool;

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
    fn fuzzy_search(
        &self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
        max_edit_dist: usize,
    ) -> bool {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return false;
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
        false
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    FuzzySearch<K, V, NUM_PREFIX_BYTES, H> for InnerNode48<K, V, NUM_PREFIX_BYTES, H>
{
    fn fuzzy_search(
        &self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
        max_edit_dist: usize,
    ) -> bool {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return false;
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
        false
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    FuzzySearch<K, V, NUM_PREFIX_BYTES, H> for InnerNode256<K, V, NUM_PREFIX_BYTES, H>
{
    fn fuzzy_search(
        &self,
        arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
        max_edit_dist: usize,
    ) -> bool {
        if !self.fuzzy_search_prefix(key, old_row, new_row, max_edit_dist) {
            return false;
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
        false
    }
}

impl<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    FuzzySearch<K, V, NUM_PREFIX_BYTES, H> for LeafNode<K, V, NUM_PREFIX_BYTES, H>
{
    fn fuzzy_search(
        &self,
        _arena: &mut StackArena,
        key: &[u8],
        old_row: &mut &mut [usize],
        new_row: &mut &mut [MaybeUninit<usize>],
        _nodes_to_search: &mut Vec<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
        max_edit_dist: usize,
    ) -> bool {
        let current_len = old_row[0];
        let remaining_key = unsafe { self.key_ref().as_bytes().get_unchecked(current_len..) };
        for k in remaining_key {
            edit_dist(key, *k, old_row, new_row, max_edit_dist);
            unsafe { swap(old_row, new_row) };
        }
        let edit_dist = unsafe { *old_row.last().unwrap_unchecked() };

        edit_dist <= max_edit_dist
    }
}

macro_rules! gen_iter {
    ($name:ident, $tree:ty, $ret:ty, $op:ident) => {
        /// An iterator over all the `LeafNode`s with a within a specifix edit distance
        pub struct $name<
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
            _tree: $tree,
        }

        impl<
                'a,
                'b,
                K: AsBytes,
                V,
                const NUM_PREFIX_BYTES: usize,
                H: NodeHeader<NUM_PREFIX_BYTES>,
            > $name<'a, 'b, K, V, NUM_PREFIX_BYTES, H>
        {
            pub(crate) fn new(tree: $tree, key: &'b [u8], max_edit_dist: usize) -> Self {
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

        impl<
                'a,
                'b,
                K: AsBytes,
                V,
                const NUM_PREFIX_BYTES: usize,
                H: NodeHeader<NUM_PREFIX_BYTES>,
            > Iterator for $name<'a, 'b, K, V, NUM_PREFIX_BYTES, H>
        {
            type Item = $ret;

            #[inline(always)]
            fn next(&mut self) -> Option<Self::Item> {
                let mut old_row = self.old_row.as_mut();
                let mut new_row = self.new_row.as_mut();

                while let (Some(node), Some(old_row)) = (
                    self.nodes_to_search.pop(),
                    self.arena.pop_copy(&mut old_row),
                ) {
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

        impl<
                'a,
                'b,
                K: AsBytes,
                V,
                const NUM_PREFIX_BYTES: usize,
                H: NodeHeader<NUM_PREFIX_BYTES>,
            > FusedIterator for $name<'a, 'b, K, V, NUM_PREFIX_BYTES, H>
        {
        }
    };
}

gen_iter!(
    Fuzzy,
    &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    (&'a K, &'a V),
    as_key_value_ref
);
gen_iter!(
    FuzzyMut,
    &'a mut RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    (&'a K, &'a mut V),
    as_key_ref_value_mut
);
gen_iter!(
    FuzzyKeys,
    &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    &'a K,
    as_key_ref
);
gen_iter!(
    FuzzyValues,
    &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    &'a V,
    as_value_ref
);
gen_iter!(
    FuzzyValuesMut,
    &'a mut RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    &'a mut V,
    as_value_mut
);

#[cfg(test)]
mod tests {
    use std::ffi::CString;

    use crate::TreeMap;

    #[test]
    fn fuzzy() {
        for n in [4, 5, 17, 49] {
            let it = 48u8..48 + n;
            let mut tree: TreeMap<CString, usize> = TreeMap::new();
            let search = CString::new("a").unwrap();
            for c in it.clone() {
                let c = c as char;
                let s = CString::new(format!("a{c}")).unwrap();
                tree.insert(s, 0usize);
            }
            let results: Vec<_> = tree.fuzzy(&search, 1).collect();
            for ((k, _), c) in results.into_iter().rev().zip(it.clone()) {
                let c = c as char;
                let s = CString::new(format!("a{c}")).unwrap();
                assert_eq!(k, &s);
            }

            let mut tree: TreeMap<CString, usize> = TreeMap::new();
            let search = CString::new("a").unwrap();
            for c in it.clone() {
                let s = if c % 2 == 0 {
                    let c = c as char;
                    CString::new(format!("a{c}")).unwrap()
                } else {
                    let c = c as char;
                    CString::new(format!("a{c}a")).unwrap()
                };
                tree.insert(s, 0usize);
            }
            let results: Vec<_> = tree.fuzzy(&search, 1).collect();
            for ((k, _), c) in results.into_iter().rev().zip((it.clone()).step_by(2)) {
                let c = c as char;
                let s = CString::new(format!("a{c}")).unwrap();
                assert_eq!(k, &s);
            }

            let mut tree: TreeMap<CString, usize> = TreeMap::new();
            let search = CString::new("a").unwrap();
            for c in it.clone() {
                let s = if c % 2 == 0 {
                    let c = c as char;
                    CString::new(format!("a{c}")).unwrap()
                } else {
                    let c = c as char;
                    CString::new(format!("a{c}a")).unwrap()
                };
                tree.insert(s, 0usize);
            }
            let results: Vec<_> = tree.fuzzy(&search, 2).collect();
            for ((k, _), c) in results.into_iter().rev().zip(it.clone()) {
                let s = if c % 2 == 0 {
                    let c = c as char;
                    CString::new(format!("a{c}")).unwrap()
                } else {
                    let c = c as char;
                    CString::new(format!("a{c}a")).unwrap()
                };
                assert_eq!(k, &s);
            }
        }
    }
}
