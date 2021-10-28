//! Tie node lookup and manipulation

use std::ptr;

use super::{
    InnerNode16, InnerNode256, InnerNode4, InnerNode48, LeafNode, NodeType, OpaqueNodePtr,
};

/// Search in the given tree for the value stored with the given key. The depth
///
/// # Safety
///
///   - The provided value type parameter, `T`, must be equal to the value type
///     of all the leaves stored in the tree.
pub unsafe fn search<T>(root: OpaqueNodePtr, key: &[u8]) -> Option<&T>
where
    T: Copy,
{
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        if let Some(og_leaf_node) = current_node.cast::<LeafNode<T>>() {
            let leaf_node = og_leaf_node.read();

            // Specifically we are matching the leaf node stored key against the full search
            // key to confirm that it is the right value. Due to the method used for prefix
            // compression, we don't explicity store all the compressed prefixes down the
            // tree.
            if leaf_node.matches_key(key) {
                let value_ref = unsafe {
                    let value_ptr = ptr::addr_of_mut!((*og_leaf_node.to_ptr()).value);

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

        let next_child_node = match header.node_type {
            NodeType::Node4 => {
                let inner_node = current_node.cast::<InnerNode4>().unwrap().read();
                inner_node.lookup_child(next_key_fragment)
            },
            NodeType::Node16 => {
                let inner_node = current_node.cast::<InnerNode16>().unwrap().read();
                inner_node.lookup_child(next_key_fragment)
            },
            NodeType::Node48 => {
                let inner_node = current_node.cast::<InnerNode48>().unwrap().read();
                inner_node.lookup_child(next_key_fragment)
            },
            NodeType::Node256 => {
                let inner_node = current_node.cast::<InnerNode256>().unwrap().read();
                inner_node.lookup_child(next_key_fragment)
            },
            NodeType::Leaf => unreachable!(
                "This branch is not possible because we checked for a LeafNode earlier in the \
                 loop."
            ),
        };

        current_node = next_child_node?;
        // Increment by a single byte
        current_depth += 1;
    }
}

#[cfg(test)]
mod lookup_tests;
