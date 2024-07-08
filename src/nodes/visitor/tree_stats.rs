use std::ops::Add;

use crate::{
    visitor::{Visitable, Visitor},
    AsBytes, InnerNode, InnerNode16, InnerNode256, InnerNode4, InnerNode48, LeafNode, TreeMap,
};

/// A visitor of the radix tree which collects statistics about the tree, like
/// how many inner nodes of each type, how many leaves
#[derive(Debug)]
pub struct TreeStatsCollector {
    current: TreeStats,
}

impl TreeStatsCollector {
    /// Run the tree stats collection on the given root node, then return the
    /// accumulated stats.
    pub fn collect<K: AsBytes, V, const PREFIX_LEN: usize>(
        tree: &TreeMap<K, V, PREFIX_LEN>,
    ) -> Option<TreeStats> {
        if let Some(root) = tree.root {
            let mut collector = TreeStatsCollector {
                current: TreeStats::default(),
            };

            root.visit_with(&mut collector);

            Some(collector.current)
        } else {
            None
        }
    }

    /// Iterate through the given tree and return the number of leaf nodes.
    pub fn count_leaf_nodes<K: AsBytes, V, const PREFIX_LEN: usize>(
        tree: &TreeMap<K, V, PREFIX_LEN>,
    ) -> usize {
        struct LeafNodeCounter;

        impl<K: AsBytes, V, const PREFIX_LEN: usize> Visitor<K, V, PREFIX_LEN> for LeafNodeCounter {
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

        tree.root
            .map(|root| root.visit_with(&mut counter))
            .unwrap_or(0)
    }
}

/// Statistics for inner nodes
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct InnerNodeStats {
    /// The number of occurrences
    pub count: usize,

    /// The total number of slots in inner nodes
    pub total_slots: usize,

    /// The number of used slots in inner nodes
    pub sum_slots: usize,

    /// Sum of all header prefix lengths
    pub total_header_bytes: usize,

    /// Sum of all used prefix length
    pub sum_prefix_len_bytes: usize,

    /// Sum of all used prefix length capped
    /// to the maximum number of bytes in the header
    pub sum_capped_prefix_len_bytes: usize,

    /// Maximum prefix length in bytes
    pub max_prefix_len_bytes: usize,

    /// Total memory usage in bytes
    pub mem_usage: usize,
}

impl InnerNodeStats {
    fn aggregate_data<K: AsBytes, V, const PREFIX_LEN: usize, N>(&mut self, t: &N)
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
    {
        self.count += 1;
        self.total_slots += N::TYPE.upper_capacity();
        self.sum_slots += t.header().num_children();

        self.total_header_bytes += PREFIX_LEN;
        self.sum_prefix_len_bytes += t.header().prefix_len();
        self.sum_capped_prefix_len_bytes += t.header().capped_prefix_len();
        self.max_prefix_len_bytes = self.max_prefix_len_bytes.max(t.header().prefix_len());

        self.mem_usage += std::mem::size_of_val(t);
    }

    /// How many free slots
    pub fn free_slots(&self) -> usize {
        self.total_slots - self.sum_slots
    }

    /// Percentage of the maximum slots that is being used
    pub fn percentage_slots(&self) -> f64 {
        self.sum_slots as f64 / self.total_slots as f64
    }

    /// The average prefix length
    pub fn avg_prefix_len(&self) -> f64 {
        self.sum_prefix_len_bytes as f64 / self.count as f64
    }

    /// The average prefix length but capped to the header prefix length
    pub fn avg_capped_prefix_len(&self) -> f64 {
        self.sum_capped_prefix_len_bytes as f64 / self.count as f64
    }

    /// The average prefix length but capped to the header prefix length
    pub fn free_header_bytes(&self) -> usize {
        self.total_header_bytes - self.sum_capped_prefix_len_bytes
    }

    /// The average prefix length but capped to the header prefix length
    pub fn percentage_header_bytes(&self) -> f64 {
        self.sum_capped_prefix_len_bytes as f64 / self.total_header_bytes as f64
    }

    /// Gets the node size in bytes, if the node count is 0, than
    /// this method returns [`None`]
    pub fn node_size(&self) -> Option<usize> {
        self.mem_usage.checked_div(self.count)
    }
}

impl Add for InnerNodeStats {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            count: self.count + rhs.count,
            total_slots: self.total_slots + rhs.total_slots,
            sum_slots: self.sum_slots + rhs.sum_slots,
            total_header_bytes: self.total_header_bytes + rhs.total_header_bytes,
            sum_prefix_len_bytes: self.sum_prefix_len_bytes + rhs.sum_prefix_len_bytes,
            sum_capped_prefix_len_bytes: self.sum_capped_prefix_len_bytes
                + rhs.sum_capped_prefix_len_bytes,
            max_prefix_len_bytes: self.max_prefix_len_bytes.max(rhs.max_prefix_len_bytes),
            mem_usage: self.mem_usage + rhs.mem_usage,
        }
    }
}

/// Statistics for inner nodes
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct LeafStats {
    /// The number of occurrences
    pub count: usize,

    /// The sum of bytes of keys stored in the tree.
    pub sum_key_bytes: usize,

    /// Total memory usage
    pub mem_usage: usize,
}

impl Add for LeafStats {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            count: self.count + rhs.count,
            sum_key_bytes: self.sum_key_bytes + rhs.sum_key_bytes,
            mem_usage: self.mem_usage + rhs.mem_usage,
        }
    }
}

/// Collection of stats about the number of nodes types present in a tree
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct TreeStats {
    /// Stats for [`InnerNode4`]s
    pub node4: InnerNodeStats,

    /// Stats for [`InnerNode16`]s
    pub node16: InnerNodeStats,

    /// Stats for [`InnerNode48`]s
    pub node48: InnerNodeStats,

    /// Stats for [`InnerNode256`]s
    pub node256: InnerNodeStats,

    /// Stats for the whole tree
    pub tree: InnerNodeStats,

    /// Number of [`LeafNode`]s present in the
    /// tree.
    pub leaf: LeafStats,
}

impl TreeStats {
    /// Total memory usage of the tree (inner nodes + leaf)
    pub fn total_memory_usage(&self) -> usize {
        self.tree.mem_usage + self.leaf.mem_usage
    }

    /// Bytes used per entry in the tree (only inner node memory usage)
    pub fn bytes_per_entry(&self) -> f64 {
        self.tree.mem_usage as f64 / self.leaf.count as f64
    }

    /// Bytes used per entry in the tree (total memory usage)
    pub fn bytes_per_entry_with_leaf(&self) -> f64 {
        self.total_memory_usage() as f64 / self.leaf.count as f64
    }
}

impl<K, V, const PREFIX_LEN: usize> Visitor<K, V, PREFIX_LEN> for TreeStatsCollector
where
    K: AsBytes,
{
    type Output = ();

    fn default_output(&self) -> Self::Output {}

    fn combine_output(&self, _: Self::Output, _: Self::Output) -> Self::Output {}

    fn visit_node4(&mut self, t: &InnerNode4<K, V, PREFIX_LEN>) -> Self::Output {
        t.super_visit_with(self);
        self.current.node4.aggregate_data(t);
        self.current.tree.aggregate_data(t);
    }

    fn visit_node16(&mut self, t: &InnerNode16<K, V, PREFIX_LEN>) -> Self::Output {
        t.super_visit_with(self);
        self.current.node16.aggregate_data(t);
        self.current.tree.aggregate_data(t);
    }

    fn visit_node48(&mut self, t: &InnerNode48<K, V, PREFIX_LEN>) -> Self::Output {
        t.super_visit_with(self);
        self.current.node48.aggregate_data(t);
        self.current.tree.aggregate_data(t);
    }

    fn visit_node256(&mut self, t: &InnerNode256<K, V, PREFIX_LEN>) -> Self::Output {
        t.super_visit_with(self);
        self.current.node256.aggregate_data(t);
        self.current.tree.aggregate_data(t);
    }

    fn visit_leaf(&mut self, t: &LeafNode<K, V>) -> Self::Output {
        self.current.leaf.count += 1;
        self.current.leaf.sum_key_bytes += t.key_ref().as_bytes().len();
        self.current.leaf.mem_usage += std::mem::size_of_val(t);
    }
}

impl std::fmt::Display for TreeStats {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let TreeStats {
            node4,
            node16,
            node48,
            node256,
            tree,
            ..
        } = self;
        write!(f, "{:#?}", self)?;
        f.write_str("\n")?;
        f.write_fmt(format_args!("memory usage (inner nodes):        {} bytes\n", tree.mem_usage))?;
        f.write_fmt(format_args!("memory usage (inner nodes + leaf): {} bytes\n", self.total_memory_usage()))?;
        f.write_fmt(format_args!("bytes/entry:                       {:.5}\n", self.bytes_per_entry()))?;
        f.write_fmt(format_args!("bytes/entry (with leaf):           {:.5}\n", self.bytes_per_entry_with_leaf()))?;
        f.write_fmt(format_args!("avg prefix length:                 {:.5} bytes\n", tree.avg_prefix_len()))?;
        f.write_fmt(format_args!("avg capped prefix length:          {:.5} bytes\n", tree.avg_capped_prefix_len()))?;
        f.write_fmt(format_args!("% used header bytes (0-1):         {:.5}\n", tree.percentage_header_bytes()))?;
        f.write_fmt(format_args!("% used slots (0-1):                {:.5}\n", tree.percentage_slots()))?;
        f.write_fmt(format_args!("n4 size:                           {:?} bytes\n", node4.node_size()))?;
        f.write_fmt(format_args!("n16 size:                          {:?} bytes\n", node16.node_size()))?;
        f.write_fmt(format_args!("n48 size:                          {:?} bytes\n", node48.node_size()))?;
        f.write_fmt(format_args!("n256 size:                         {:?} bytes\n", node256.node_size()))?;
        f.write_fmt(format_args!("max prefix length:                 {} bytes", tree.max_prefix_len_bytes))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{tests_common::generate_key_fixed_length, TreeMap};

    #[test]
    fn mostly_empty_tree_stats_fixed_length_tree() {
        let mut tree = TreeMap::new();
        for (k, v) in generate_key_fixed_length([1, 1, 1, 1])
            .enumerate()
            .map(|(a, b)| (b, a))
        {
            tree.try_insert(k, v).unwrap();
        }
        let stats = TreeStatsCollector::collect(&tree).unwrap();

        let expected_inner = InnerNodeStats {
            count: 15,
            total_slots: 60,
            sum_slots: 30,
            total_header_bytes: 240,
            sum_prefix_len_bytes: 0,
            sum_capped_prefix_len_bytes: 0,
            max_prefix_len_bytes: 0,
            mem_usage: 960,
        };
        let expected = TreeStats {
            node4: expected_inner,
            tree: expected_inner,
            leaf: LeafStats {
                count: 16,
                sum_key_bytes: 64,
                mem_usage: 384,
            },
            ..Default::default()
        };

        assert_eq!(stats, expected);
    }

    #[test]
    fn full_tree_stats_fixed_length_tree() {
        let mut tree = TreeMap::new();
        for (k, v) in generate_key_fixed_length([15, 3])
            .enumerate()
            .map(|(a, b)| (b, a))
        {
            tree.try_insert(k, v).unwrap();
        }
        let stats = TreeStatsCollector::collect(&tree).unwrap();

        let node4 = InnerNodeStats {
            count: 16,
            total_slots: 64,
            sum_slots: 64,
            total_header_bytes: 256,
            sum_prefix_len_bytes: 0,
            sum_capped_prefix_len_bytes: 0,
            max_prefix_len_bytes: 0,
            mem_usage: 1024,
        };
        let node16 = InnerNodeStats {
            count: 1,
            total_slots: 16,
            sum_slots: 16,
            total_header_bytes: 16,
            sum_prefix_len_bytes: 0,
            sum_capped_prefix_len_bytes: 0,
            max_prefix_len_bytes: 0,
            mem_usage: 168,
        };
        let expected = TreeStats {
            node4,
            node16,
            tree: node4 + node16,
            leaf: LeafStats {
                count: 64,
                sum_key_bytes: 128,
                mem_usage: 1536,
            },
            ..Default::default()
        };

        assert_eq!(stats, expected);
    }
}
