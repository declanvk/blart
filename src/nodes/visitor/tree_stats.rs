use crate::{
    visitor::{Visitable, Visitor},
    AsBytes, Header, NodeType, OpaqueNodePtr,
};
use std::mem;

/// A visitor of the radix tree which collects statistics about the tree, like
/// how many inner nodes of each type, how many leaves
#[derive(Debug)]
pub struct TreeStatsCollector;

impl TreeStatsCollector {
    /// Run the tree stats collection on the given root node, then return the
    /// accumalated stats.
    ///
    /// # Safety
    ///  - For the duration of this function, the given node and all its
    ///    children nodes must not get mutated.
    pub unsafe fn collect<K, V>(root: OpaqueNodePtr<K, V>) -> TreeStats
    where
        K: AsBytes,
    {
        let mut collector = TreeStatsCollector;

        root.visit_with(&mut collector)
    }

    /// Iterate through the given tree and return the number of leaf nodes.
    ///
    /// # Safety
    ///  - For the duration of this function, the given node and all its
    ///    children nodes must not get mutated.
    pub unsafe fn count_leaf_nodes<K, V>(root: OpaqueNodePtr<K, V>) -> usize {
        struct LeafNodeCounter;

        impl<K, V> Visitor<K, V> for LeafNodeCounter {
            type Output = usize;

            fn default_output(&self) -> Self::Output {
                0
            }

            fn combine_output(&self, o1: Self::Output, o2: Self::Output) -> Self::Output {
                o1 + o2
            }

            fn visit_leaf(&mut self, _t: &crate::LeafNode<K, V>) -> Self::Output {
                1
            }
        }

        let mut counter = LeafNodeCounter;

        root.visit_with(&mut counter)
    }
}

/// Collection of stats about the number of nodes types present in a tree
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct TreeStats {
    /// Number of [`InnerNode4`][crate::nodes::InnerNode4]s present in the tree.
    pub node4_count: usize,

    /// Number of [`InnerNode16`][crate::nodes::InnerNode16]s present in the
    /// tree.
    pub node16_count: usize,

    /// Number of [`InnerNode48`][crate::nodes::InnerNode48]s present in the
    /// tree.
    pub node48_count: usize,

    /// Number of [`InnerNode256`][crate::nodes::InnerNode256]s present in the
    /// tree.
    pub node256_count: usize,

    /// Number of [`LeafNode`][crate::nodes::LeafNode]s present in the
    /// tree.
    pub leaf_count: usize,

    /// The number of empty slots in inner nodes, that could potentially contain
    /// a leaf node.
    ///
    /// This value is useful to measure occupancy in the tree, and how much
    /// space is potentially wasted.
    pub empty_capacity: usize,

    /// The total number of bytes of keys stored in the tree.
    pub total_key_bytes: usize,

    /// The total number of bytes used by inner nodes.
    pub total_inner_node_bytes: usize,
}

impl TreeStats {
    /// Returns the number of bytes of overhead per byte of key stored in the
    /// tree.
    ///
    /// Overheard in this case is all bytes used by the inner nodes.
    pub fn overhead_per_key_byte(&self) -> f64 {
        (self.total_inner_node_bytes as f64) / (self.total_key_bytes as f64)
    }
}

impl<K, V> Visitor<K, V> for TreeStatsCollector
where
    K: AsBytes,
{
    type Output = TreeStats;

    fn default_output(&self) -> Self::Output {
        TreeStats::default()
    }

    fn combine_output(&self, o1: Self::Output, o2: Self::Output) -> Self::Output {
        TreeStats {
            node16_count: o1.node16_count + o2.node16_count,
            node256_count: o1.node256_count + o2.node256_count,
            node48_count: o1.node48_count + o2.node48_count,
            node4_count: o1.node4_count + o2.node4_count,
            leaf_count: o1.leaf_count + o2.leaf_count,
            empty_capacity: o1.empty_capacity + o2.empty_capacity,
            total_inner_node_bytes: o1.total_inner_node_bytes + o2.total_inner_node_bytes,
            total_key_bytes: o1.total_key_bytes + o2.total_key_bytes,
        }
    }

    fn visit_node4(&mut self, t: &crate::InnerNode4<K, V>) -> Self::Output {
        let mut output = t.super_visit_with(self);
        output.node4_count += 1;
        output.empty_capacity += NodeType::Node4.upper_capacity() - t.header.num_children();
        output.total_inner_node_bytes +=
            mem::size_of_val(t) + header_extra_allocated_size(&t.header);
        output
    }

    fn visit_node16(&mut self, t: &crate::InnerNode16<K, V>) -> Self::Output {
        let mut output = t.super_visit_with(self);
        output.node16_count += 1;
        output.empty_capacity += NodeType::Node16.upper_capacity() - t.header.num_children();
        output.total_inner_node_bytes +=
            mem::size_of_val(t) + header_extra_allocated_size(&t.header);
        output
    }

    fn visit_node48(&mut self, t: &crate::InnerNode48<K, V>) -> Self::Output {
        let mut output = t.super_visit_with(self);
        output.node48_count += 1;
        output.empty_capacity += NodeType::Node48.upper_capacity() - t.header.num_children();
        output.total_inner_node_bytes +=
            mem::size_of_val(t) + header_extra_allocated_size(&t.header);
        output
    }

    fn visit_node256(&mut self, t: &crate::InnerNode256<K, V>) -> Self::Output {
        let mut output = t.super_visit_with(self);
        output.node256_count += 1;
        output.empty_capacity += NodeType::Node256.upper_capacity() - t.header.num_children();
        output.total_inner_node_bytes +=
            mem::size_of_val(t) + header_extra_allocated_size(&t.header);
        output
    }

    fn visit_leaf(&mut self, t: &crate::LeafNode<K, V>) -> Self::Output {
        let mut output = TreeStats::default();
        output.leaf_count += 1;
        output.total_key_bytes += t.key_ref().as_bytes().len();
        output
    }
}

fn header_extra_allocated_size(header: &Header) -> usize {
    if header.is_prefix_on_heap() {
        header.prefix_len()
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::deallocate_tree;

    #[test]
    fn mostly_empty_tree_stats_fixed_length_tree() {
        let root = crate::tests_common::setup_tree_from_entries(
            crate::tests_common::generate_key_fixed_length([1, 1, 1, 1])
                .enumerate()
                .map(|(a, b)| (b, a)),
        );
        let stats = unsafe { TreeStatsCollector::collect(root) };

        assert_eq!(
            stats,
            TreeStats {
                node4_count: 15,
                node16_count: 0,
                node48_count: 0,
                node256_count: 0,
                leaf_count: 16,
                empty_capacity: 30,
                total_key_bytes: 64,
                total_inner_node_bytes: 1080
            }
        );

        unsafe { deallocate_tree(root) };
    }

    #[test]
    fn full_tree_stats_fixed_length_tree() {
        let root = crate::tests_common::setup_tree_from_entries(
            crate::tests_common::generate_key_fixed_length([15, 3])
                .enumerate()
                .map(|(a, b)| (b, a)),
        );
        let stats = unsafe { TreeStatsCollector::collect(root) };

        assert_eq!(
            stats,
            TreeStats {
                node4_count: 16,
                node16_count: 1,
                node48_count: 0,
                node256_count: 0,
                leaf_count: 64,
                empty_capacity: 0,
                total_key_bytes: 128,
                total_inner_node_bytes: 1328,
            }
        );

        unsafe { deallocate_tree(root) };
    }
}
