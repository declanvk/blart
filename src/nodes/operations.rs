//! Tie node lookup and manipulation

use super::{InnerNode4, InnerNodePtr, LeafNode, NodePtr, OpaqueNodePtr};
use std::ptr;

/// Search in the given tree for the value stored with the given key.
///
/// # Safety
///
///   - The reference returned from this function must not outlive the leaf node
///     it was derived from. Generally, the reference should not be live past a
///     mutation of this same tree via the `insert` or `delete` methods, as it
///     may invalidate the reference.
pub unsafe fn search<'k, 'v, V>(root: OpaqueNodePtr<V>, key: &'k [u8]) -> Option<&'v V> {
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        if let Some(leaf_node_ptr) = current_node.cast::<LeafNode<V>>() {
            let leaf_node = leaf_node_ptr.read();

            // Specifically we are matching the leaf node stored key against the full search
            // key to confirm that it is the right value. Due to the method used for prefix
            // compression, we don't explicity store all the compressed prefixes down the
            // tree.
            if leaf_node.matches_key(key) {
                let value_ref = unsafe {
                    let value_ptr = ptr::addr_of_mut!((*leaf_node_ptr.to_ptr()).value);

                    value_ptr.as_ref().unwrap()
                };

                return Some(value_ref);
            } else {
                return None;
            }
        }

        let header = current_node.read();
        if header.match_prefix(&key[current_depth..]) != header.prefix_size {
            return None;
        }

        // Since the prefix matched, we need to advance the depth by the size
        // of the prefix
        current_depth += usize::try_from(header.prefix_size).unwrap();

        let next_key_fragment = if current_depth < key.len() {
            key[current_depth]
        } else {
            return None;
        };

        // SAFETY: We checked that the current node is not a leaf earlier in the loop
        let next_child_node = unsafe { lookup_child_unchecked(current_node, next_key_fragment) };

        current_node = next_child_node?;
        // Increment by a single byte
        current_depth += 1;
    }
}

/// Insert the given key-value pair into the tree.
///
/// # Panics
///
///   - Panics if the key already exists in the trie.
///   - Panics if the key is a prefix of another key that exists in the trie.
///
/// # Safety
///
///  - The `root` [`OpaqueNodePtr`] must be a unique pointer to the underlying
///    node object, otherwise a deallocation may create dangling pointers.
pub unsafe fn insert<V>(root: &mut OpaqueNodePtr<V>, new_leaf: LeafNode<V>) {
    let current_node = root;
    let mut current_depth = 0;

    loop {
        if let Some(leaf_node_ptr) = current_node.cast::<LeafNode<V>>() {
            let leaf_node = leaf_node_ptr.read();

            let mut new_n4 = InnerNode4::empty();
            let prefix_size = leaf_node.key[current_depth..]
                .iter()
                .zip(new_leaf.key[current_depth..].iter())
                .take_while(|(k1, k2)| k1 == k2)
                .count();
            new_n4
                .header
                .write_prefix(&new_leaf.key[current_depth..prefix_size]);
            current_depth += prefix_size;

            let new_leaf_key_byte = new_leaf.key[current_depth];
            let new_leaf_pointer = NodePtr::allocate_node(new_leaf);

            new_n4.write_child(new_leaf_key_byte, new_leaf_pointer.to_opaque());
            new_n4.write_child(leaf_node.key[current_depth], *current_node);

            *current_node = NodePtr::allocate_node(new_n4).to_opaque();

            return;
        }

        // since header is mutable will need to write it back
        let mut header = current_node.read();
        let matched_prefix_size = header.match_prefix(&(new_leaf.key)[current_depth..]);
        if matched_prefix_size != header.prefix_size {
            // prefix mismatch, need to split prefix into two separate nodes and take the
            // common prefix into a new parent node
            let mut new_n4 = InnerNode4::empty();
            let matched_prefix_size = usize::try_from(matched_prefix_size).unwrap();

            let new_leaf_key_byte = new_leaf.key[current_depth + matched_prefix_size];
            let new_leaf_pointer = NodePtr::allocate_node(new_leaf).to_opaque();

            new_n4.write_child(new_leaf_key_byte, new_leaf_pointer);
            new_n4.write_child(header.read_prefix()[matched_prefix_size], *current_node);

            new_n4
                .header
                .write_prefix(&header.read_prefix()[..matched_prefix_size]);
            header.ltrim_prefix(matched_prefix_size + 1);

            // Updated the header information here
            current_node.write(*header);
            *current_node = NodePtr::allocate_node(new_n4).to_opaque();
            return;
        }

        current_depth += usize::try_from(header.prefix_size).unwrap();

        let next_key_fragment = if current_depth < new_leaf.key.len() {
            new_leaf.key[current_depth]
        } else {
            panic!(
                "Attempted to insert a key [{:?}] which is a prefix of an existing key in the \
                 tree!",
                new_leaf.key
            )
        };

        // SAFETY: We checked that the current node is not a leaf earlier in the loop
        let next_child_node = unsafe { lookup_child_unchecked(*current_node, next_key_fragment) };

        match next_child_node {
            Some(next_child_node) => {
                current_depth += 1;
                *current_node = next_child_node;
            },
            None => {
                if header.is_full() {
                    // we will create a new node of the next larger type and copy all the children
                    // over.

                    // SAFETY: We determine that the current node is not a leaf by checking earlier
                    // in the loop. The uniqueness requirement for the `current_node` must be upheld
                    // at the `insert` function level. The `insert` function does not create
                    // aliasing node pointers.
                    unsafe {
                        grow_unchecked(current_node);
                    }
                }

                // SAFETY: We determine that the current node is not a leaf by checking earlier
                // in the loop
                unsafe {
                    insert_child_unchecked(*current_node, new_leaf.key[current_depth], new_leaf)
                };

                return;
            },
        }
    }
}

/// Lookup the child of the current node, excluding the possibility of a
/// LeafNode.
///
/// # Safety
///
/// The current node must not be a leaf node.
unsafe fn lookup_child_unchecked<V>(
    current_node: OpaqueNodePtr<V>,
    next_key_fragment: u8,
) -> Option<OpaqueNodePtr<V>> {
    match current_node.to_node_ptr() {
        InnerNodePtr::Node4(inner_node) => inner_node.read().lookup_child(next_key_fragment),
        InnerNodePtr::Node16(inner_node) => inner_node.read().lookup_child(next_key_fragment),
        InnerNodePtr::Node48(inner_node) => inner_node.read().lookup_child(next_key_fragment),
        InnerNodePtr::Node256(inner_node) => inner_node.read().lookup_child(next_key_fragment),
        InnerNodePtr::LeafNode(_) => unreachable!(
            "This branch is not possible because of the safety invariants of the function."
        ),
    }
}

/// Grow the current node into the next larger size, excluding the possibility
/// of a LeafNode.
///
/// # Safety
///
///  - The current node must not be a leaf node.
///  - The `current_node` must be a reference to the only existing pointer to
///    the node object, otherwise the possible deallocation may create dangling
///    pointers.
unsafe fn grow_unchecked<V>(current_node: &mut OpaqueNodePtr<V>) {
    match current_node.to_node_ptr() {
        InnerNodePtr::Node4(old_node) => {
            let inner_node = old_node.read();
            let new_node = inner_node.grow();
            let new_node = NodePtr::allocate_node(new_node).to_opaque();
            *current_node = new_node;
            // SAFETY: The `deallocate_node` function is only called a single time. The
            // uniqueness requirement is passed up to the `grow_unchecked` safet
            // requirements.
            unsafe {
                NodePtr::deallocate_node(old_node);
            }
        },
        InnerNodePtr::Node16(old_node) => {
            let inner_node = old_node.read();
            let new_node = inner_node.grow();
            let new_node = NodePtr::allocate_node(new_node).to_opaque();
            *current_node = new_node;
            // SAFETY: The `deallocate_node` function is only called a single time. The
            // uniqueness requirement is passed up to the `grow_unchecked` safet
            // requirements.
            unsafe {
                NodePtr::deallocate_node(old_node);
            }
        },
        InnerNodePtr::Node48(old_node) => {
            let inner_node = old_node.read();
            let new_node = inner_node.grow();
            let new_node = NodePtr::allocate_node(new_node).to_opaque();
            *current_node = new_node;
            // SAFETY: The `deallocate_node` function is only called a single time. The
            // uniqueness requirement is passed up to the `grow_unchecked` safet
            // requirements.
            unsafe {
                NodePtr::deallocate_node(old_node);
            }
        },
        InnerNodePtr::Node256(_) => {
            panic!("Unable to grow a Node256, something went wrong!")
        },
        InnerNodePtr::LeafNode(_) => unreachable!(
            "This branch is not possible because of the safety invariants of the function."
        ),
    }
}

/// Insert a new child into the current node, excluding the possibility of a
/// leaf node.
///
/// # Safety
///
/// The current node must not be a leaf node.
unsafe fn insert_child_unchecked<V>(
    current_node: OpaqueNodePtr<V>,
    key_fragment: u8,
    new_leaf: LeafNode<V>,
) {
    match current_node.to_node_ptr() {
        InnerNodePtr::Node4(old_node) => {
            old_node.update(|mut inner_node| {
                let new_leaf_ptr = NodePtr::allocate_node(new_leaf);
                inner_node.write_child(key_fragment, new_leaf_ptr.to_opaque());
                inner_node
            });
        },
        InnerNodePtr::Node16(old_node) => {
            old_node.update(|mut inner_node| {
                let new_leaf_ptr = NodePtr::allocate_node(new_leaf);
                inner_node.write_child(key_fragment, new_leaf_ptr.to_opaque());
                inner_node
            });
        },
        InnerNodePtr::Node48(old_node) => {
            old_node.update(|mut inner_node| {
                let new_leaf_ptr = NodePtr::allocate_node(new_leaf);
                inner_node.write_child(key_fragment, new_leaf_ptr.to_opaque());
                inner_node
            });
        },
        InnerNodePtr::Node256(old_node) => {
            old_node.update(|mut inner_node| {
                let new_leaf_ptr = NodePtr::allocate_node(new_leaf);
                inner_node.write_child(key_fragment, new_leaf_ptr.to_opaque());
                inner_node
            });
        },
        InnerNodePtr::LeafNode(_) => unreachable!(
            "This branch is not possible because of the safety invariants of the function."
        ),
    }
}

#[cfg(test)]
mod lookup_tests;

#[cfg(test)]
mod insert_tests;
