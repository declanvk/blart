use crate::{ConcreteNodePtr, InnerNode, InsertError, LeafNode, NodePtr, OpaqueNodePtr};
use std::{fmt, ops::ControlFlow};

/// This struct contains the results from searching for an insert point for
/// a new node in the tree.
///
/// It contains all the relevant information needed to perform the insert
/// and update the tree.
pub struct InsertSearchResult<V> {
    /// The parent node pointer and key byte that points to the main node
    /// insert point.
    ///
    /// In the case that the root node is the main insert point, this will
    /// have a `None` value.
    pub(crate) parent_ptr_and_child_key_byte: Option<(OpaqueNodePtr<V>, u8)>,
    /// The type of operation that needs to be performed to insert the key
    pub(crate) insert_type: InsertSearchResultType<V>,
    /// The number of bytes that were read from the key to find the insert
    /// point.
    pub(crate) key_bytes_used: usize,
}

/// The type of insert
pub enum InsertSearchResultType<V> {
    /// An insert where an inner node had a differing prefix from the key.
    ///
    /// This insert type will create a new inner node with the portion of
    /// the prefix that did match, and update the existing inner node
    MismatchPrefix {
        matched_prefix_size: usize,
        mismatched_inner_node_ptr: OpaqueNodePtr<V>,
    },
    /// An insert where the node to be added matched all the way up to a
    /// leaf node.
    ///
    /// This insert type will create a new inner node, and assign the
    /// existing leaf and the new leaf as children to that node.
    SplitLeaf { leaf_node_ptr: NodePtr<LeafNode<V>> },
    /// An insert where the search terminated at an existing inner node that
    /// did not have a child with the key byte.
    ///
    /// If the inner node is full, it will be grown to the next largest
    /// size.
    IntoExisting { inner_node_ptr: OpaqueNodePtr<V> },
}

impl<V> fmt::Debug for InsertSearchResultType<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchPrefix {
                matched_prefix_size,
                mismatched_inner_node_ptr,
            } => f
                .debug_struct("MismatchPrefix")
                .field("matched_prefix_size", matched_prefix_size)
                .field("mismatched_inner_node_ptr", mismatched_inner_node_ptr)
                .finish(),
            Self::SplitLeaf { leaf_node_ptr } => f
                .debug_struct("SplitLeaf")
                .field("leaf_node_ptr", leaf_node_ptr)
                .finish(),
            Self::IntoExisting { inner_node_ptr } => f
                .debug_struct("IntoExisting")
                .field("inner_node_ptr", inner_node_ptr)
                .finish(),
        }
    }
}

/// Perform an iterative search for the insert point for the given key,
/// starting at the given root node.
pub fn search_for_insert_point<V>(
    root: OpaqueNodePtr<V>,
    key: &[u8],
) -> Result<InsertSearchResult<V>, InsertError> {
    fn test_prefix_identify_insert<V, N: InnerNode<Value = V>>(
        inner_ptr: NodePtr<N>,
        key: &[u8],
        current_depth: &mut usize,
    ) -> Result<ControlFlow<usize, Option<OpaqueNodePtr<V>>>, InsertError> {
        // SAFETY: The lifetime produced from this is bounded to this scope and does not
        // escape. Further, no other code mutates the node referenced, which is further
        // enforced the "no concurrent reads or writes" requirement on the
        // `search_unchecked` function.
        let inner_node = unsafe { inner_ptr.as_ref() };
        let header = inner_node.header();
        let matched_prefix_size = header.match_prefix(&key[*current_depth..]);
        if matched_prefix_size != header.prefix_size() {
            return Ok(ControlFlow::Break(matched_prefix_size));
        }

        // Since the prefix matched, advance the depth by the size of the prefix
        *current_depth += matched_prefix_size;

        let next_key_fragment = if *current_depth < key.len() {
            key[*current_depth]
        } else {
            // then the key has insufficient bytes to be unique. It must be
            // a prefix of an existing key

            return Err(InsertError::PrefixKey(Box::from(key)));
        };

        Ok(ControlFlow::Continue(
            inner_node.lookup_child(next_key_fragment),
        ))
    }

    let mut current_parent = None;
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        let lookup_result = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => {
                test_prefix_identify_insert(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                return Ok(InsertSearchResult {
                    key_bytes_used: current_depth,
                    parent_ptr_and_child_key_byte: current_parent,
                    insert_type: InsertSearchResultType::SplitLeaf { leaf_node_ptr },
                });
            },
        }?;

        match lookup_result {
            ControlFlow::Continue(next_child_node) => {
                match next_child_node {
                    Some(next_child_node) => {
                        current_parent = Some((current_node, key[current_depth]));
                        current_node = next_child_node;
                        // Increment by a single byte
                        current_depth += 1;
                    },
                    None => {
                        return Ok(InsertSearchResult {
                            key_bytes_used: current_depth,
                            insert_type: InsertSearchResultType::IntoExisting {
                                inner_node_ptr: current_node,
                            },
                            parent_ptr_and_child_key_byte: current_parent,
                        })
                    },
                }
            },
            ControlFlow::Break(matched_prefix_size) => {
                return Ok(InsertSearchResult {
                    key_bytes_used: current_depth,
                    insert_type: InsertSearchResultType::MismatchPrefix {
                        matched_prefix_size,
                        mismatched_inner_node_ptr: current_node,
                    },
                    parent_ptr_and_child_key_byte: current_parent,
                })
            },
        };
    }
}

#[cfg(test)]
mod tests;
