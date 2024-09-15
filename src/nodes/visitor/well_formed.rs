use crate::{
    nodes::visitor::{Visitable, Visitor},
    AsBytes, InnerNode, NodeType, OpaqueNodePtr, TreeMap,
};
use std::{
    collections::{hash_map::Entry, HashMap},
    error::Error,
    fmt,
};

/// A portion of an entire key that should uniquely identify each node in
/// the tree.
///
/// We assume that this should be unique for each node given no loops in the
/// tree.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct KeyPrefix(Box<[u8]>);

impl From<&[u8]> for KeyPrefix {
    fn from(src: &[u8]) -> Self {
        KeyPrefix(Box::from(src))
    }
}

impl<const LEN: usize> PartialEq<[u8; LEN]> for KeyPrefix {
    fn eq(&self, other: &[u8; LEN]) -> bool {
        self.0.as_ref() == other.as_slice()
    }
}

/// An issue with the well-formed-ness of the tree. See the documentation on
/// [`WellFormedChecker`] for more context.
#[derive(PartialEq, Eq)]
pub enum MalformedTreeError<K, V, const PREFIX_LEN: usize> {
    /// A loop was observed between nodes
    LoopFound {
        /// The node that was observed more than once while traversing the tree
        node_ptr: OpaqueNodePtr<K, V, PREFIX_LEN>,
        /// The key prefix when the node was first observed
        first_observed: KeyPrefix,
        /// The key prefix when the node was observed a second time
        later_observed: KeyPrefix,
    },
    /// An inner node had an incorrect number of children
    WrongChildrenCount {
        /// The key prefix identifying the inner node
        key_prefix: KeyPrefix,
        /// The type of the inner node (InnerNode4, InnerNode16, etc)
        ///
        /// This field is guaranteed not to be [`NodeType::Leaf`]
        inner_node_type: NodeType,
        /// The number of children found at the inner node
        num_children: usize,
    },
    /// The expected key prefix did not match the actual prefix that was present
    /// in the leaf
    PrefixMismatch {
        /// The expected key prefix
        expected_prefix: KeyPrefix,
        /// The entire key
        entire_key: K,
    },
    /// The length of the tree is not 0, even though the root is
    /// [`Option::None`]
    EmptyTreeWithLen,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for MalformedTreeError<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LoopFound {
                node_ptr,
                first_observed,
                later_observed,
            } => f
                .debug_struct("LoopFound")
                .field("node_ptr", node_ptr)
                .field("first_observed", first_observed)
                .field("later_observed", later_observed)
                .finish(),
            Self::WrongChildrenCount {
                key_prefix,
                inner_node_type,
                num_children,
            } => f
                .debug_struct("WrongChildrenCount")
                .field("key_prefix", key_prefix)
                .field("inner_node_type", inner_node_type)
                .field("num_children", num_children)
                .finish(),
            Self::PrefixMismatch {
                expected_prefix,
                entire_key,
            } => f
                .debug_struct("PrefixMismatch")
                .field("expected_prefix", expected_prefix)
                .field("entire_key", &entire_key.as_bytes() as &dyn fmt::Debug)
                .finish(),
            Self::EmptyTreeWithLen => f.debug_struct("EmptyTreeWithLen").finish(),
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Display for MalformedTreeError<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MalformedTreeError::LoopFound {
                node_ptr,
                first_observed,
                later_observed,
            } => {
                write!(
                    f,
                    "Found a loop in the tree containing the node [{node_ptr:?}]. First observed \
                     that node at [{first_observed:?}], then later observed the same node at \
                     [{later_observed:?}]",
                )
            },
            MalformedTreeError::WrongChildrenCount {
                key_prefix,
                inner_node_type,
                num_children,
            } => {
                write!(
                    f,
                    "Found an inner node of type [{inner_node_type:?}] at location \
                     [{key_prefix:?}] that had the wrong number of children! Expected children in \
                     range [{:?}], but found [{num_children}] children",
                    inner_node_type.capacity_range(),
                )
            },
            MalformedTreeError::PrefixMismatch {
                expected_prefix,
                entire_key,
            } => {
                write!(
                    f,
                    "Found a leaf that had a mismatched key from the expected prefix! Expected \
                     the leaf key to start with [{expected_prefix:?}], but the leaf key was [{:?}]",
                    entire_key.as_bytes()
                )
            },
            MalformedTreeError::EmptyTreeWithLen => {
                write!(
                    f,
                    "The length of the tree is not 0, even though the root is None",
                )
            },
        }
    }
}

impl<K: Clone, V, const PREFIX_LEN: usize> Clone for MalformedTreeError<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        match self {
            Self::LoopFound {
                node_ptr,
                first_observed,
                later_observed,
            } => Self::LoopFound {
                node_ptr: *node_ptr,
                first_observed: first_observed.clone(),
                later_observed: later_observed.clone(),
            },
            Self::WrongChildrenCount {
                key_prefix,
                inner_node_type,
                num_children,
            } => Self::WrongChildrenCount {
                key_prefix: key_prefix.clone(),
                inner_node_type: *inner_node_type,
                num_children: *num_children,
            },
            Self::PrefixMismatch {
                expected_prefix,
                entire_key,
            } => Self::PrefixMismatch {
                expected_prefix: expected_prefix.clone(),
                entire_key: entire_key.clone(),
            },
            Self::EmptyTreeWithLen => Self::EmptyTreeWithLen,
        }
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> Error for MalformedTreeError<K, V, PREFIX_LEN> {}

/// A visitor of the radix tree which checks that the tree is well-formed.
///
/// In this context, well-formed means that in the tree:
///  1. there are no loops between nodes
///  2. every inner node has a number of children that is in range for the inner
///     node type. For example, InnerNode16 has between 5 and 16 children.
///  3. the elements of the key (as part of inner node prefixes and child
///     pointers) combine to match the leaf node key prefix
///
/// #1 and #3 are unlikely, but #2 is a possibility if specific tree operations
/// are not implemented correctly. This visitor can be used to sanity check the
/// tree in unit tests or other test cases.
///
/// This checker will only return a single issue at a time. A tree is only
/// "well-formed" (by the definition given above) if the checker returns
/// `Ok(())`.
#[derive(Debug)]
pub struct WellFormedChecker<K, V, const PREFIX_LEN: usize> {
    current_key_prefix: Vec<u8>,
    seen_nodes: HashMap<OpaqueNodePtr<K, V, PREFIX_LEN>, KeyPrefix>,
}

impl<K, V, const PREFIX_LEN: usize> WellFormedChecker<K, V, PREFIX_LEN>
where
    K: AsBytes + Clone,
{
    /// Traverse the given tree and check that it is well-formed. Returns the
    /// number of nodes in the tree.
    ///
    /// # Errors
    ///  - Returns an error if the given tree is not well-formed.
    pub fn check(
        tree: &TreeMap<K, V, PREFIX_LEN>,
    ) -> Result<usize, MalformedTreeError<K, V, PREFIX_LEN>> {
        tree.root
            .map(|root| {
                // SAFETY: Since we get a reference to the TreeMap, we know no
                // mutation can happen to any of the nodes
                unsafe { Self::check_tree(root) }
            })
            .unwrap_or_else(|| {
                if tree.is_empty() {
                    Ok(0)
                } else {
                    Err(MalformedTreeError::EmptyTreeWithLen)
                }
            })
    }

    /// Traverse the given tree and check that it is well-formed. Returns the
    /// number of nodes in the tree.
    ///
    /// # Safety
    ///  - For the duration of this function, the given node and all its
    ///    children nodes must not get mutated.
    ///
    /// # Errors
    ///  - Returns an error if the given tree is not well-formed.
    unsafe fn check_tree(
        tree: OpaqueNodePtr<K, V, PREFIX_LEN>,
    ) -> Result<usize, MalformedTreeError<K, V, PREFIX_LEN>> {
        let mut visitor = WellFormedChecker {
            current_key_prefix: vec![],
            seen_nodes: HashMap::new(),
        };

        // We see the root node at the empty prefix
        visitor.seen_nodes.insert(tree, KeyPrefix::default());

        tree.visit_with(&mut visitor)
    }

    fn visit_inner_node<N>(
        &mut self,
        inner_node: &N,
    ) -> Result<usize, MalformedTreeError<K, V, PREFIX_LEN>>
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
    {
        let original_key_prefix_len = self.current_key_prefix.len();

        // update running key prefix with inner node partial prefix
        // TODO: Fix this, here the we should return the full reconstructed prefix if
        // prefix len > PREFIX_LEN
        self.current_key_prefix
            .extend(inner_node.read_full_prefix(original_key_prefix_len).0);

        // SAFETY: The `child_it` does not live beyond the following loop and will not
        // overlap with any mutating access or operation, which is guaranteed by the
        // `check_tree` caller requirements.
        let child_it = inner_node.iter();

        let mut running_node_count = 0;
        let mut num_children: usize = 0;
        for (key_byte, child_pointer) in child_it {
            // update running key prefix with child pointer key fragment
            self.current_key_prefix.push(key_byte);

            let current_key_prefix: KeyPrefix = self.current_key_prefix.as_slice().into();

            match self.seen_nodes.entry(child_pointer) {
                Entry::Occupied(entry) => {
                    return Err(MalformedTreeError::LoopFound {
                        node_ptr: child_pointer,
                        first_observed: entry.get().clone(),
                        later_observed: current_key_prefix,
                    });
                },
                Entry::Vacant(entry) => {
                    entry.insert(current_key_prefix);
                },
            }

            running_node_count += child_pointer.visit_with(self)?;

            // remove child pointer key fragment
            assert_eq!(
                self.current_key_prefix
                    .pop()
                    .expect("should match push of key byte"),
                key_byte
            );

            num_children += 1;
        }

        // remove inner node partial key prefix
        self.current_key_prefix.truncate(original_key_prefix_len);

        if !(N::TYPE.capacity_range().contains(&num_children)) {
            let current_key_prefix: KeyPrefix = self.current_key_prefix.as_slice().into();
            return Err(MalformedTreeError::WrongChildrenCount {
                key_prefix: current_key_prefix,
                inner_node_type: N::TYPE,
                num_children,
            });
        }

        Ok(running_node_count + 1)
    }
}

impl<K, V, const PREFIX_LEN: usize> Visitor<K, V, PREFIX_LEN>
    for WellFormedChecker<K, V, PREFIX_LEN>
where
    K: Clone + AsBytes,
{
    type Output = Result<usize, MalformedTreeError<K, V, PREFIX_LEN>>;

    fn default_output(&self) -> Self::Output {
        // Chose zero so that any places that call `default_output` don't influence the
        // overall count
        Ok(0)
    }

    fn combine_output(&self, o1: Self::Output, o2: Self::Output) -> Self::Output {
        Ok(o1? + o2?)
    }

    fn visit_node4(&mut self, t: &crate::InnerNode4<K, V, PREFIX_LEN>) -> Self::Output {
        self.visit_inner_node(t)
    }

    fn visit_node16(&mut self, t: &crate::InnerNode16<K, V, PREFIX_LEN>) -> Self::Output {
        self.visit_inner_node(t)
    }

    fn visit_node48(&mut self, t: &crate::InnerNode48<K, V, PREFIX_LEN>) -> Self::Output {
        self.visit_inner_node(t)
    }

    fn visit_node256(&mut self, t: &crate::InnerNode256<K, V, PREFIX_LEN>) -> Self::Output {
        self.visit_inner_node(t)
    }

    fn visit_leaf(&mut self, t: &crate::LeafNode<K, V>) -> Self::Output {
        if !t.key_ref().as_bytes().starts_with(&self.current_key_prefix) {
            let current_key_prefix: KeyPrefix = self.current_key_prefix.as_slice().into();
            return Err(MalformedTreeError::PrefixMismatch {
                expected_prefix: current_key_prefix,
                entire_key: t.key_ref().clone(),
            });
        }

        Ok(1)
    }
}

#[cfg(test)]
mod tests {
    use std::ffi::CString;

    use super::*;
    use crate::{
        deallocate_tree,
        tests_common::{generate_key_fixed_length, setup_tree_from_entries},
        InnerNode16, InnerNode4, LeafNode, NodePtr, TreeMap,
    };

    #[test]
    fn check_well_formed_tree() {
        let mut num_leaves = 0;
        let keys = generate_key_fixed_length([3, 2, 1])
            .inspect(|_| {
                num_leaves += 1;
            })
            .enumerate()
            .map(|(idx, key)| (key, idx));

        let root: OpaqueNodePtr<_, usize, 16> = setup_tree_from_entries(keys);
        // 4  * 3 * 2
        assert_eq!(num_leaves, 24);

        assert_eq!(unsafe { WellFormedChecker::check_tree(root) }, Ok(41));

        unsafe { deallocate_tree(root) };
    }

    #[test]
    fn check_well_formed_tree_long_prefix() {
        let mut tree: TreeMap<CString, i32> = TreeMap::new();
        tree.insert(CString::new("1").unwrap(), 1);
        tree.insert(CString::new("2XX1XXXXXXXXXXXXXXXXXXXXXX1").unwrap(), 2);
        tree.insert(CString::new("2XX1XXXXXXXXXXXXXXXXXXXXXX2").unwrap(), 3);
        tree.insert(CString::new("2XX2").unwrap(), 4);

        assert_eq!(WellFormedChecker::check(&tree), Ok(7));
    }

    #[test]
    fn check_tree_with_loop() {
        // have to allocate in this one because miri didn't like us using `&mut _` to
        // make loops

        let l1 = LeafNode::new(Box::new([1, 2, 3, 5, 6, 1]), 123561);
        let l2 = LeafNode::new(Box::new([1, 2, 3, 5, 6, 2]), 123562);
        let l3 = LeafNode::new(Box::new([1, 2, 4, 7, 8, 3]), 124783);

        let l1_ptr: NodePtr<16, LeafNode<Box<[u8; 6]>, i32>> = NodePtr::allocate_node_ptr(l1);
        let l2_ptr = NodePtr::allocate_node_ptr(l2);
        let l3_ptr = NodePtr::allocate_node_ptr(l3);

        let n4_left = InnerNode4::from_prefix(&[5, 6], 2);
        let n4_right = InnerNode4::from_prefix(&[7, 8], 2);
        let n16 = InnerNode16::from_prefix(&[1, 2], 2);

        let n4_left_ptr = NodePtr::allocate_node_ptr(n4_left);
        let n4_right_ptr = NodePtr::allocate_node_ptr(n4_right);

        // construct root early
        let root = NodePtr::allocate_node_ptr(n16);

        {
            let n4_left = unsafe { n4_left_ptr.as_mut() };
            // Update inner node prefix and child slots
            n4_left.write_child(1, l1_ptr.to_opaque());
            n4_left.write_child(2, l2_ptr.to_opaque());
        }

        {
            let n4_right = unsafe { n4_right_ptr.as_mut() };

            n4_right.write_child(3, l3_ptr.to_opaque());
            // replace normal l4 pointer with loop back to root
            n4_right.write_child(4, root.to_opaque());
        }

        {
            let n16 = unsafe { root.as_mut() };
            n16.write_child(3, n4_left_ptr.to_opaque());
            n16.write_child(4, n4_right_ptr.to_opaque());
        }

        let check_result = unsafe { WellFormedChecker::check_tree(root.to_opaque()) }
            .expect_err("should have failed for loop");
        match check_result {
            MalformedTreeError::LoopFound {
                node_ptr,
                first_observed,
                later_observed,
            } => {
                assert_eq!(node_ptr, root.to_opaque());
                assert_eq!(first_observed, []);
                assert_eq!(later_observed, [1u8, 2, 4, 7, 8, 4]);
            },
            _ => {
                panic!("expected a LoopFound error")
            },
        }

        // We can't just call `deallocate_tree(root)` because the deallocate function
        // assumes no loops, if we did use `deallocate_tree` it would hit a
        // use-after-free error
        unsafe {
            let _ = NodePtr::deallocate_node_ptr(root);
        };
        unsafe {
            let _ = NodePtr::deallocate_node_ptr(n4_left_ptr);
        };
        unsafe {
            let _ = NodePtr::deallocate_node_ptr(n4_right_ptr);
        };
        unsafe {
            let _ = NodePtr::deallocate_node_ptr(l1_ptr);
        };
        unsafe {
            let _ = NodePtr::deallocate_node_ptr(l2_ptr);
        };
        unsafe {
            let _ = NodePtr::deallocate_node_ptr(l3_ptr);
        };
    }

    #[test]
    fn check_tree_with_wrong_child_count() {
        let mut l1 = LeafNode::new(Box::new([1, 2, 3, 5, 6, 1]), 123561);
        let mut l2 = LeafNode::new(Box::new([1, 2, 3, 5, 6, 2]), 123562);
        let mut l3 = LeafNode::new(Box::new([1, 2, 4, 7, 8, 3]), 124783);
        let mut l4 = LeafNode::new(Box::new([1, 2, 4, 7, 8, 4]), 124784);

        let l1_ptr: OpaqueNodePtr<Box<[u8; 6]>, i32, 16> = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        let mut n4_left = InnerNode4::from_prefix(&[5, 6], 2);
        let mut n4_right = InnerNode4::from_prefix(&[7, 8], 2);
        let mut n16 = InnerNode16::from_prefix(&[1, 2], 2);

        // Update inner node prefix and child slots
        n4_left.write_child(1, l1_ptr);
        n4_left.write_child(2, l2_ptr);

        n4_right.write_child(3, l3_ptr);
        n4_right.write_child(4, l4_ptr);

        let n4_left_ptr = NodePtr::from(&mut n4_left).to_opaque();
        let n4_right_ptr = NodePtr::from(&mut n4_right).to_opaque();

        n16.write_child(3, n4_left_ptr);
        n16.write_child(4, n4_right_ptr);

        let root = NodePtr::from(&mut n16).to_opaque();

        let check_result = unsafe { WellFormedChecker::check_tree(root) }
            .expect_err("should have failed for loop");
        match check_result {
            MalformedTreeError::WrongChildrenCount {
                key_prefix,
                inner_node_type,
                num_children,
            } => {
                assert_eq!(key_prefix, []);
                assert_eq!(inner_node_type, NodeType::Node16);
                assert_eq!(num_children, 2);
            },
            _ => {
                panic!("expected a WrongChildrenCount error")
            },
        }
    }

    #[test]
    fn check_tree_with_mismatched_key_prefix() {
        let mut l1 = LeafNode::new(Box::new([1, 2, 3, 5, 6, 1]), 123561);
        let mut l2 = LeafNode::new(Box::new([1, 2, 3, 5, 6, 2]), 123562);
        let mut l3 = LeafNode::new(Box::new([1, 2, 4, 7, 8, 3]), 124783);
        let mut l4 = LeafNode::new(Box::new([255, 255, 255, 255, 255, 255]), 124784);

        let l1_ptr: OpaqueNodePtr<Box<[u8; 6]>, i32, 16> = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        let mut n4_left = InnerNode4::from_prefix(&[5, 6], 2);
        let mut n4_right = InnerNode4::from_prefix(&[7, 8], 2);
        let mut n16 = InnerNode16::from_prefix(&[1, 2], 2);

        // Update inner node prefix and child slots
        n4_left.write_child(1, l1_ptr);
        n4_left.write_child(2, l2_ptr);

        n4_right.write_child(3, l3_ptr);
        n4_right.write_child(4, l4_ptr);

        let n4_left_ptr = NodePtr::from(&mut n4_left).to_opaque();
        let n4_right_ptr = NodePtr::from(&mut n4_right).to_opaque();

        n16.write_child(3, n4_left_ptr);
        n16.write_child(4, n4_right_ptr);

        let root = NodePtr::from(&mut n16).to_opaque();

        let check_result = unsafe { WellFormedChecker::check_tree(root) }
            .expect_err("should have failed for loop");
        match check_result {
            MalformedTreeError::PrefixMismatch {
                expected_prefix,
                entire_key,
            } => {
                assert_eq!(expected_prefix, [1, 2, 4, 7, 8, 4]);
                assert_eq!(entire_key.as_ref(), &[255u8, 255, 255, 255, 255, 255][..]);
            },
            _ => {
                panic!("expected a PrefixMismatch error")
            },
        }
    }
}
