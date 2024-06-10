use hdrhistogram::Histogram;

use crate::{
    visitor::{Visitable, Visitor},
    AsBytes, Header, NodeType, OpaqueNodePtr,
};
use std::{
    fmt, mem,
    ops::{Range, RangeInclusive},
};

/// A visitor of the radix tree which collects statistics about the tree, like
/// how many inner nodes of each type, how many leaves
#[derive(Debug)]
pub struct TreeStatsCollector {
    stats: TreeStats,
}

impl TreeStatsCollector {
    /// Run the tree stats collection on the given root node, then return the
    /// accumalated stats.
    ///
    /// # Safety
    ///  - For the duration of this function, the given node and all its
    ///    children nodes must not get mutated.
    pub unsafe fn collect<K, V>(root: &OpaqueNodePtr<K, V>) -> TreeStats
    where
        K: AsBytes,
    {
        let mut collector = TreeStatsCollector {
            stats: TreeStats::new(),
        };

        root.visit_with(&mut collector);

        collector.stats
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

const fn node_type_to_num_buckets(node_type: NodeType) -> usize {
    let range = node_type.capacity_range();

    range.end - range.start
}

/// Collection of stats about the number of nodes types present in a tree
#[derive(Debug, Clone, PartialEq)]
pub struct TreeStats {
    node4_num_children_dist: ExactHistogram<{ node_type_to_num_buckets(NodeType::Node4) }>,
    node16_num_children_dist: ExactHistogram<{ node_type_to_num_buckets(NodeType::Node16) }>,
    node48_num_children_dist: ExactHistogram<{ node_type_to_num_buckets(NodeType::Node48) }>,
    node256_num_children_dist: ExactHistogram<{ node_type_to_num_buckets(NodeType::Node256) }>,
    key_length: Histogram<u64>,
    total_inner_node_bytes: usize,
}

impl fmt::Display for TreeStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct DisplayAsDebug<'a, T>(&'a T);

        impl<'a, T: fmt::Display> fmt::Debug for DisplayAsDebug<'a, T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <T as fmt::Display>::fmt(self.0, f)
            }
        }

        struct HistogramAsDebug<'a>(&'a Histogram<u64>);

        impl<'a> fmt::Debug for HistogramAsDebug<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_map()
                    .entry(&"min", &self.0.min())
                    .entry(&"mean", &self.0.mean())
                    .entry(&"stdev", &self.0.stdev())
                    .entry(&"max", &self.0.max())
                    .entry(&"p25", &self.0.value_at_percentile(0.25))
                    .entry(&"p50", &self.0.value_at_percentile(0.5))
                    .entry(&"p75", &self.0.value_at_percentile(0.75))
                    .entry(&"p90", &self.0.value_at_percentile(0.90))
                    .entry(&"p95", &self.0.value_at_percentile(0.95))
                    .entry(&"p99", &self.0.value_at_percentile(0.99))
                    .entry(&"p99.9", &self.0.value_at_percentile(0.999))
                    .finish()
            }
        }

        f.debug_struct("TreeStats")
            .field("node4", &DisplayAsDebug(&self.node4_num_children_dist))
            .field("node16", &DisplayAsDebug(&self.node16_num_children_dist))
            .field("node48", &DisplayAsDebug(&self.node48_num_children_dist))
            .field("node256", &DisplayAsDebug(&self.node256_num_children_dist))
            .field("leaf_count", &self.leaf_count())
            .field("total_key_bytes", &self.total_key_bytes())
            .field("total_inner_node_bytes", &self.total_inner_node_bytes)
            .field("key_length", &HistogramAsDebug(&self.key_length))
            .field("empty_capacity", &self.empty_capacity())
            .finish()
    }
}

impl TreeStats {
    /// Create an empty collection of tree statistics.
    fn new() -> Self {
        const fn convert_range(input: Range<usize>) -> Range<u64> {
            Range {
                start: input.start as u64,
                end: input.end as u64,
            }
        }

        Self {
            node4_num_children_dist: ExactHistogram::new(convert_range(
                NodeType::Node4.capacity_range(),
            )),
            node16_num_children_dist: ExactHistogram::new(convert_range(
                NodeType::Node16.capacity_range(),
            )),
            node48_num_children_dist: ExactHistogram::new(convert_range(
                NodeType::Node48.capacity_range(),
            )),
            node256_num_children_dist: ExactHistogram::new(convert_range(
                NodeType::Node256.capacity_range(),
            )),
            key_length: Histogram::new(3)
                .expect("should be able to create a default histogram with no bounds and 3 sigfig"),
            total_inner_node_bytes: 0,
        }
    }

    /// Number of [`InnerNode4`][crate::nodes::InnerNode4]s present in the tree.
    pub fn node4_count(&self) -> u64 {
        self.node4_num_children_dist.total_count()
    }

    /// Number of [`InnerNode16`][crate::nodes::InnerNode16]s present in the
    /// tree.
    pub fn node16_count(&self) -> u64 {
        self.node16_num_children_dist.total_count()
    }

    /// Number of [`InnerNode48`][crate::nodes::InnerNode48]s present in the
    /// tree.
    pub fn node48_count(&self) -> u64 {
        self.node48_num_children_dist.total_count()
    }

    /// Number of [`InnerNode256`][crate::nodes::InnerNode256]s present in the
    /// tree.
    pub fn node256_count(&self) -> u64 {
        self.node256_num_children_dist.total_count()
    }

    /// Number of [`LeafNode`][crate::nodes::LeafNode]s present in the
    /// tree.
    pub fn leaf_count(&self) -> u64 {
        self.key_length.len()
    }

    /// The number of empty slots in inner nodes, that could potentially contain
    /// a leaf node.
    ///
    /// This value is useful to measure occupancy in the tree, and how much
    /// space is potentially wasted.
    pub fn empty_capacity(&self) -> u64 {
        let node4_empty: u64 = self
            .node4_num_children_dist
            .entries()
            .map(|(value, count)| count * ((NodeType::Node4.upper_capacity() as u64) - value))
            .sum();

        let node16_empty: u64 = self
            .node16_num_children_dist
            .entries()
            .map(|(value, count)| count * ((NodeType::Node16.upper_capacity() as u64) - value))
            .sum();

        let node48_empty: u64 = self
            .node48_num_children_dist
            .entries()
            .map(|(value, count)| count * ((NodeType::Node48.upper_capacity() as u64) - value))
            .sum();

        let node256_empty: u64 = self
            .node256_num_children_dist
            .entries()
            .map(|(value, count)| count * ((NodeType::Node256.upper_capacity() as u64) - value))
            .sum();

        node4_empty + node16_empty + node48_empty + node256_empty
    }

    /// The total number of bytes of keys stored in the tree.
    pub fn total_key_bytes(&self) -> u64 {
        self.key_length
            .iter_recorded()
            .map(|value| value.count_at_value() * value.value_iterated_to())
            .sum::<u64>()
    }

    /// The total number of bytes used by inner nodes.
    pub fn total_inner_node_bytes(&self) -> usize {
        self.total_inner_node_bytes
    }

    /// Returns the number of bytes of overhead per byte of key stored in the
    /// tree.
    ///
    /// Overheard in this case is all bytes used by the inner nodes.
    pub fn overhead_per_key_byte(&self) -> f64 {
        (self.total_inner_node_bytes as f64) / (self.total_key_bytes() as f64)
    }
}

impl<K, V> Visitor<K, V> for TreeStatsCollector
where
    K: AsBytes,
{
    type Output = ();

    fn default_output(&self) -> Self::Output {}

    fn combine_output(&self, _: Self::Output, _: Self::Output) -> Self::Output {}

    fn visit_node4(&mut self, t: &crate::InnerNode4<K, V>) -> Self::Output {
        t.super_visit_with(self);
        self.stats.node4_num_children_dist.record(
            t.header
                .num_children()
                .try_into()
                .expect("number of children should fit in a u64"),
        );
        self.stats.total_inner_node_bytes +=
            mem::size_of_val(t) + header_extra_allocated_size(&t.header);
    }

    fn visit_node16(&mut self, t: &crate::InnerNode16<K, V>) -> Self::Output {
        t.super_visit_with(self);
        self.stats.node16_num_children_dist.record(
            t.header
                .num_children()
                .try_into()
                .expect("number of children should fit in a u64"),
        );
        self.stats.total_inner_node_bytes +=
            mem::size_of_val(t) + header_extra_allocated_size(&t.header);
    }

    fn visit_node48(&mut self, t: &crate::InnerNode48<K, V>) -> Self::Output {
        t.super_visit_with(self);
        self.stats.node48_num_children_dist.record(
            t.header
                .num_children()
                .try_into()
                .expect("number of children should fit in a u64"),
        );
        self.stats.total_inner_node_bytes +=
            mem::size_of_val(t) + header_extra_allocated_size(&t.header);
    }

    fn visit_node256(&mut self, t: &crate::InnerNodeUncompressed<K, V>) -> Self::Output {
        t.super_visit_with(self);
        self.stats.node256_num_children_dist.record(
            t.header
                .num_children()
                .try_into()
                .expect("number of children should fit in a u64"),
        );
        self.stats.total_inner_node_bytes +=
            mem::size_of_val(t) + header_extra_allocated_size(&t.header);
    }

    fn visit_leaf(&mut self, t: &crate::LeafNode<K, V>) -> Self::Output {
        self.stats
            .key_length
            .record(
                t.key_ref()
                    .as_bytes()
                    .len()
                    .try_into()
                    .expect("should be able to convert usize bytestring length to u64"),
            )
            .expect("should be able to record arbitrary bytestring length in histogram");
    }
}

fn header_extra_allocated_size(header: &Header) -> usize {
    if header.is_prefix_on_heap() {
        header.prefix_len()
    } else {
        0
    }
}

/// This represents a discrete distribution of data with exactly `NUM_VALUES`
/// unique values.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ExactHistogram<const NUM_VALUES: usize>
where
    Self: Sized,
{
    value_range: Range<u64>,
    counts: [u64; NUM_VALUES],
    total_count: u64,
}

impl<const NUM_VALUES: usize> fmt::Display for ExactHistogram<NUM_VALUES>
where
    Self: Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();

        let mut zeros: Vec<RangeInclusive<u64>> = vec![];
        map.entries(self.entries().filter(|(value, count)| {
            let is_zero = *count == 0;

            if is_zero {
                if let Some(last) = zeros.last_mut() {
                    if *last.end() == (*value - 1) {
                        *last = (*last.start())..=(*value);
                    } else {
                        zeros.push(*value..=*value);
                    }
                } else {
                    zeros.push(*value..=*value);
                }
            }

            !is_zero
        }));

        if !zeros.is_empty() {
            map.entry(
                &"zeros",
                &zeros
                    .into_iter()
                    .map(|range| {
                        if range.start() == range.end() {
                            range.start().to_string()
                        } else {
                            format!("{}..={}", range.start(), range.end())
                        }
                    })
                    .collect::<Vec<_>>(),
            );
        }

        map.entry(&"total", &self.total_count());

        map.finish()
    }
}

impl<const NUM_VALUES: usize> ExactHistogram<NUM_VALUES> {
    /// Create a new histogram that will accept the given range of values.
    const fn new(value_range: Range<u64>) -> ExactHistogram<NUM_VALUES> {
        assert!((value_range.end as usize) - (value_range.start as usize) == NUM_VALUES);

        Self {
            value_range,
            counts: [0; NUM_VALUES],
            total_count: 0,
        }
    }

    /// Record a value in the histogram, incrementing its count by 1.
    ///
    /// # Panics
    ///
    /// This method will panic if the given value is not in the `value_range`
    /// that this histogram was created with.
    pub fn record(&mut self, value: u64) {
        assert!(
            self.value_range.contains(&value),
            "Value was not in expected range [{}, {}): {value}",
            self.value_range.start,
            self.value_range.end,
        );

        let translated_value = usize::try_from(value - self.value_range.start)
            .expect("scaled value should fit in usize");
        self.counts[translated_value] += 1;
        self.total_count += 1;
    }

    /// Return an iterator over the pairs of `(value, count)`, including
    /// `count`s of 0.
    pub fn entries(&self) -> impl Iterator<Item = (u64, u64)> + '_ {
        self.counts.iter().enumerate().map(move |(idx, count)| {
            let value = u64::try_from(idx).expect("should be able to fit index into u64")
                + self.value_range.start;

            (value, *count)
        })
    }

    /// Return the total number of recorded values
    pub fn total_count(&self) -> u64 {
        self.total_count
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
        let stats = unsafe { TreeStatsCollector::collect(&root) };

        assert_eq!(stats.node4_count(), 15);
        assert_eq!(stats.node16_count(), 0);
        assert_eq!(stats.node48_count(), 0);
        assert_eq!(stats.node256_count(), 0);
        assert_eq!(stats.leaf_count(), 16);
        assert_eq!(stats.empty_capacity(), 30);
        assert_eq!(stats.total_key_bytes(), 64);
        assert_eq!(stats.total_inner_node_bytes(), 1080);

        unsafe { deallocate_tree(root) };
    }

    #[test]
    fn full_tree_stats_fixed_length_tree() {
        let root = crate::tests_common::setup_tree_from_entries(
            crate::tests_common::generate_key_fixed_length([15, 3])
                .enumerate()
                .map(|(a, b)| (b, a)),
        );
        let stats = unsafe { TreeStatsCollector::collect(&root) };

        assert_eq!(stats.node4_count(), 16);
        assert_eq!(stats.node16_count(), 1);
        assert_eq!(stats.node48_count(), 0);
        assert_eq!(stats.node256_count(), 0);
        assert_eq!(stats.leaf_count(), 64);
        assert_eq!(stats.empty_capacity(), 0);
        assert_eq!(stats.total_key_bytes(), 128);
        assert_eq!(stats.total_inner_node_bytes(), 1328);

        unsafe { deallocate_tree(root) };
    }
}
