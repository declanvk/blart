//! This module contains functionality used to analyze key distributions and
//! determine optimal inner node sizes.

use std::{boxed::Box, fmt, iter, mem, num::NonZeroU8, ops::Sub, vec::Vec};

use blart::AsBytes;

/// This struct contains the running state needed to calculate an
/// [`InnerNodeWidthDistribution`] when fed a sorted list of keys.
#[derive(Debug)]
struct CalculateInnerNodeDist {
    last_key_bytes: Vec<u8>,
    is_first: bool,
    dist: InnerNodeWidthDistribution,
    prefix_stack: Vec<PrefixFrame>,
}

#[derive(Debug)]
struct PrefixFrame {
    prefix_length: usize,
    width: usize,
}

impl<K> Extend<K> for CalculateInnerNodeDist
where
    K: AsBytes,
{
    fn extend<T: IntoIterator<Item = K>>(&mut self, iter: T) {
        self.ingest(iter);
    }
}

impl<K> FromIterator<K> for CalculateInnerNodeDist
where
    K: AsBytes,
{
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
        let mut calculator = CalculateInnerNodeDist::new();

        calculator.ingest(iter);

        calculator
    }
}

impl CalculateInnerNodeDist {
    fn new() -> Self {
        Self {
            last_key_bytes: Vec::new(),
            is_first: true,
            dist: InnerNodeWidthDistribution::default(),
            prefix_stack: Vec::new(),
        }
    }

    /// Consume the given keys and add the results to the running inner node
    /// width distribution.
    ///
    /// This function assumes that the list of keys is sorted by their byte
    /// representation (as returned by [`AsBytes::as_bytes`]), otherwise it will
    /// return incorrect results. Also, the keys should be globally sorted over
    /// all invocations of [`ingest`][Self::ingest].
    ///
    /// # Panic
    ///
    /// This function also assumes that there are no key is a prefix of any
    /// other key in the list, other it may panic.
    fn ingest<K: AsBytes>(&mut self, keys: impl IntoIterator<Item = K>) {
        let mut keys = keys.into_iter();
        while let Some(key) = keys.next() {
            let key_bytes = key.as_bytes();

            let prefix_length = self.calculate_longest_common_prefix(key_bytes);
            self.update_last_key_bytes(key_bytes);

            loop {
                let Some(last_frame) = self.prefix_stack.last_mut() else {
                    // TODO: Figure out why we push a width of 0 for the top of the stack?????
                    self.prefix_stack.push(PrefixFrame {
                        prefix_length,
                        width: 0,
                    });
                    break;
                };

                if last_frame.prefix_length > prefix_length {
                    // Then we've finished processing all children of the top frame
                    let prefix_frame = self.prefix_stack.pop().unwrap();
                    Self::write_frame_into_dist(&mut self.dist, prefix_frame);
                    continue;
                } else if last_frame.prefix_length < prefix_length {
                    self.prefix_stack.push(PrefixFrame {
                        prefix_length,
                        width: 1,
                    });
                    break;
                } else {
                    last_frame.width += 1;
                    break;
                }
            }
        }
    }

    /// Consume the running state to produce the final inner node width
    /// distribution.
    fn finish(mut self) -> InnerNodeWidthDistribution {
        for prefix_frame in self.prefix_stack {
            Self::write_frame_into_dist(&mut self.dist, prefix_frame);
        }

        self.dist
    }

    fn calculate_longest_common_prefix(&mut self, new_key_bytes: &[u8]) -> usize {
        let last_key_bytes = self.last_key_bytes.as_slice();

        if !self.is_first {
            // Since the `keys` iterator is assumed to be ordered by byte representation,
            // the shorter key will always go before the longer key, so we only need to
            // check if `last_key_bytes` is the prefix.
            assert!(
                !new_key_bytes.starts_with(&last_key_bytes),
                "no prefixed keys allowed. {last_key_bytes:?} {new_key_bytes:?}"
            );
        } else {
            self.is_first = false;
        }

        // longest common prefix
        last_key_bytes
            .iter()
            .zip(new_key_bytes)
            .take_while(|(a, b)| **a == **b)
            .count()
    }

    fn update_last_key_bytes(&mut self, new_key_bytes: &[u8]) {
        self.last_key_bytes.clear();
        self.last_key_bytes.extend_from_slice(new_key_bytes);
    }

    fn write_frame_into_dist(
        dist: &mut InnerNodeWidthDistribution,
        PrefixFrame { width, .. }: PrefixFrame,
    ) {
        // TODO: Explain why we add 1 here!
        let width = width + 1;
        if width > 1 {
            dist.add(
                InnerNodeWidth::try_from(width).expect("width should fall within expected bounds"),
                1,
            );
        }
    }
}

/// Given a sorted iterator of keys, compute the distribution of inner node
/// widths.
pub fn analyze_sorted_key_iter<K>(keys: impl Iterator<Item = K>) -> InnerNodeWidthDistribution
where
    K: AsBytes,
{
    let mut calculator = CalculateInnerNodeDist::new();

    calculator.ingest(keys);

    calculator.finish()
}

/// This struct represents a distribution of inner node widths gathered
/// from a set of keys.
#[derive(Clone, PartialEq, Eq)]
pub struct InnerNodeWidthDistribution {
    /// This field store an array for each of the possible node width, from `[2,
    /// 256]`.
    ///
    /// It is not possible to have a node width of 0 or 1 (or greater than 256).
    /// Because of that, we store node width 2 at the 0th index, node width 3 at
    /// the 1st index, etc etc, and node width 256 at the 254th index.
    counts: [usize; 255],
}

impl Default for InnerNodeWidthDistribution {
    fn default() -> Self {
        Self { counts: [0; 255] }
    }
}

impl fmt::Debug for InnerNodeWidthDistribution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut builder = f.debug_struct("InnerNodeWidthDistribution");
        for (width, count) in self.iter().filter(|(_, count)| *count != 0) {
            builder.field(&format!("{width}"), &count);
        }
        builder.finish()
    }
}

impl InnerNodeWidthDistribution {
    /// For the [`InnerNodeWidth`] increase the corresponding count by `count`.
    #[inline]
    pub fn add(&mut self, width: InnerNodeWidth, count: usize) {
        self.counts[width.get() - 2] += count;
    }

    /// Retrieve the count for the given [`InnerNodeWidth`]
    #[inline]
    pub fn get(&self, width: InnerNodeWidth) -> usize {
        self.counts[width.get() - 2]
    }

    /// Return an iterator over all [`InnerNodeWidth`]s with non-zero count.
    pub fn iter(&self) -> impl Iterator<Item = (InnerNodeWidth, usize)> + use<'_> {
        self.counts
            .iter()
            .enumerate()
            .map(|(idx, count)| (InnerNodeWidth::try_from(idx + 2).unwrap(), *count))
            .filter(|(_, count)| *count != 0)
    }

    /// Find the optimal assignment of `num_inner_nodes - 1` inner nodes using
    /// this inner node width distribution as a factor in the cost.
    ///
    /// The optimization currently only takes into account the size of the node.
    /// See [`InnerNodeKind`] for details. A consequence of this is that the
    /// optimization results will only ever return inner node assignments of
    /// [`InnerNodeKind::KeyChildCompressed`] because it is always smaller than
    /// [`InnerNodeKind::ChildOnlyCompressed`].
    ///
    /// A future version of this function could decide to take into account the
    /// relative lookup or update performance of the two kinds and return a
    /// different result.
    pub fn find_optimal_assignment(&self, num_inner_nodes: usize) -> InnerNodeWidthAssignment {
        assert!(num_inner_nodes > 1);
        assert!(num_inner_nodes <= 256 - 2);
        // 1 inner node width is always assigned to 256 width
        let num_inner_nodes_to_assign = num_inner_nodes - 1;

        // memo[k][w], where k ranges over the node widths we need to assign and w
        // ranges over the possible values for the width [2, 255].
        const POSSIBLE_WIDTHS: usize = 256 - 2;
        let mut memo =
            vec![f64::MAX; POSSIBLE_WIDTHS * num_inner_nodes_to_assign * InnerNodeKind::ALL.len()];
        let mut backpointers =
            vec![
                None::<(InnerNodeWidth, InnerNodeKind)>;
                POSSIBLE_WIDTHS * num_inner_nodes_to_assign * InnerNodeKind::ALL.len()
            ];

        fn to_index(inner_node: usize, width: usize, kind: usize) -> usize {
            const NODE_STRIDE: usize = POSSIBLE_WIDTHS * InnerNodeKind::ALL.len();
            const WIDTH_STRIDE: usize = InnerNodeKind::ALL.len();
            inner_node * NODE_STRIDE + width * WIDTH_STRIDE + kind
        }

        // Base case - since we know there is at least 1 inner node to assign (first
        // assert)
        for width in (InnerNodeWidth::MIN.get()..InnerNodeWidth::MAX.get())
            .map(|w| InnerNodeWidth::new(w).unwrap())
        {
            for kind in InnerNodeKind::ALL {
                memo[to_index(0, width.get() - InnerNodeWidth::MIN.get(), kind as usize)] =
                    cost_between(None, width, kind, self);
            }
        }

        // Recurrence - use the previous width calculated to find the optimal new width
        for inner_node in 1..num_inner_nodes_to_assign {
            for width in (InnerNodeWidth::MIN.get()..InnerNodeWidth::MAX.get())
                .map(|w| InnerNodeWidth::new(w).unwrap())
            {
                for kind in InnerNodeKind::ALL {
                    let mut minimum_cost = f64::MAX;
                    let mut previous_width_with_min_cost = None;
                    for prev_width in (InnerNodeWidth::MIN.get()..width.get())
                        .map(|w| InnerNodeWidth::new(w).unwrap())
                    {
                        let cost = cost_between(Some(prev_width), width, kind, self)
                            + memo[to_index(
                                inner_node - 1,
                                prev_width.get() - InnerNodeWidth::MIN.get(),
                                kind as usize,
                            )];
                        if cost < minimum_cost {
                            minimum_cost = cost;
                            previous_width_with_min_cost = Some((prev_width, kind));
                        }
                    }
                    let index = to_index(
                        inner_node,
                        width.get() - InnerNodeWidth::MIN.get(),
                        kind as usize,
                    );
                    memo[index] = minimum_cost;
                    backpointers[index] = previous_width_with_min_cost;
                }
            }
        }

        // Compute the minimum cost when considering a final node256 at the end
        let mut minimum_cost = f64::MAX;
        let mut minimum_cost_prev_width = None;
        for kind in InnerNodeKind::ALL {
            for prev_width in (InnerNodeWidth::MIN.get()..InnerNodeWidth::MAX.get())
                .map(|w| InnerNodeWidth::new(w).unwrap())
            {
                let index = to_index(
                    num_inner_nodes_to_assign - 1,
                    prev_width.get() - InnerNodeWidth::MIN.get(),
                    kind as usize,
                );
                let cost =
                    cost_between(Some(prev_width), InnerNodeWidth::MAX, kind, self) + memo[index];
                if cost < minimum_cost {
                    minimum_cost = cost;
                    minimum_cost_prev_width = Some((prev_width, kind));
                }
            }
        }

        let mut assignment = Vec::with_capacity(num_inner_nodes_to_assign);
        let mut node_kinds = Vec::with_capacity(num_inner_nodes_to_assign);

        // Follow the back pointers to find the optimal assignment
        let mut current_minimum_cost_width = minimum_cost_prev_width;
        let mut next_inner_node = num_inner_nodes_to_assign - 1;
        while let Some((prev_width, prev_kind)) = current_minimum_cost_width {
            let index = to_index(
                next_inner_node,
                prev_width.get() - InnerNodeWidth::MIN.get(),
                prev_kind as usize,
            );
            assignment.push(prev_width);
            node_kinds.push(prev_kind);
            current_minimum_cost_width = backpointers[index];
            next_inner_node = next_inner_node.saturating_sub(1);
        }
        assignment.reverse();
        node_kinds.reverse();

        InnerNodeWidthAssignment::new(assignment.into_boxed_slice(), node_kinds.into_boxed_slice())
            .unwrap()
    }
}

/// This enum represents the different kinds of inner nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InnerNodeKind {
    /// This kind matches the `Node4` or `Node16` from the original ART paper,
    /// or a [`blart::raw::InnerNodeSorted`].
    ///
    /// In an inner node with width `w`, nodes of this kind have `w` values of
    /// `u8` representing the child key bytes and `w` values of roughly `*const
    /// ()` representing the pointers to children.
    KeyChildCompressed = 0,
    /// This kind matches the `Node48` from the original ART paper, or a
    /// [`blart::raw::InnerNode48`].
    ///
    /// In an inner node with width `w`, nodes of this kind have `256` values of
    /// `u8` representing the child key bytes and `w` values of roughly `*const
    /// ()` representing the pointers to children.
    ChildOnlyCompressed = 1,
}

impl InnerNodeKind {
    const ALL: [Self; 2] = [Self::KeyChildCompressed, Self::ChildOnlyCompressed];
}

impl Extend<(InnerNodeWidth, usize)> for InnerNodeWidthDistribution {
    fn extend<T: IntoIterator<Item = (InnerNodeWidth, usize)>>(&mut self, iter: T) {
        for (width, count) in iter {
            self.add(width, count);
        }
    }
}

impl FromIterator<(InnerNodeWidth, usize)> for InnerNodeWidthDistribution {
    fn from_iter<T: IntoIterator<Item = (InnerNodeWidth, usize)>>(iter: T) -> Self {
        let mut dist = Self::default();
        dist.extend(iter);
        dist
    }
}

/// This type represents an inner node width in the range `[2, 256]`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InnerNodeWidth(NonZeroU8);

impl InnerNodeWidth {
    /// The maximum inner node width of 256.
    pub const MAX: Self = Self(NonZeroU8::MAX);
    /// The minimum inner node width of 2.
    pub const MIN: Self = Self(NonZeroU8::MIN);

    /// Return a new [`InnerNodeWidth`] if the value is within `[2, 256]`,
    /// otherwise return `None`.
    pub const fn new(width: usize) -> Option<Self> {
        if width < 2 || width > 256 {
            return None;
        }

        Some(Self(NonZeroU8::new((width - 1) as u8).unwrap()))
    }

    /// Return the width value as a `usize`.
    pub const fn get(self) -> usize {
        // TODO: Use `usize::from` when trait methods are stable in const contexts
        (self.0.get() as usize) + 1
    }

    /// Return the next larger [`InnerNodeWidth`], or `None` if `self` is
    /// [`Self::MAX`].
    pub fn increment(self) -> Option<Self> {
        self.0.checked_add(1).map(Self)
    }
}

impl fmt::Display for InnerNodeWidth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "n{}", self.get())
    }
}

impl fmt::Debug for InnerNodeWidth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("InnerNodeWidth").field(&self.get()).finish()
    }
}

impl TryFrom<usize> for InnerNodeWidth {
    type Error = WidthTryFromIntError;

    fn try_from(width: usize) -> Result<Self, Self::Error> {
        Self::new(width).ok_or_else(|| WidthTryFromIntError { width })
    }
}

impl Sub<u8> for InnerNodeWidth {
    type Output = Option<InnerNodeWidth>;

    fn sub(self, rhs: u8) -> Self::Output {
        self.0
            .get()
            .checked_sub(rhs)
            .and_then(|v| Self::new(v as usize))
    }
}

/// This error is returned when attempting to convert from a `usize` to a
/// [`InnerNodeWidth`], but the `usize` is out of range.
#[derive(Debug, Clone, Copy)]
pub struct WidthTryFromIntError {
    width: usize,
}

impl fmt::Display for WidthTryFromIntError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        core::write!(
            f,
            "Width [{}] is outside the bounds [2, 256] for an inner node width",
            self.width
        )
    }
}

/// This struct represents a set of inner nodes of specific widths and kinds.
///
/// The assignment aspect is because typically this set is smaller than the
/// number of inner node widths in the original [`InnerNodeWidthDistribution`],
/// so the assignment will have some cost.
///
/// See [`InnerNodeKind`] for the different types of inner nodes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InnerNodeWidthAssignment {
    widths: Box<[InnerNodeWidth]>,
    kinds: Box<[InnerNodeKind]>,
}

impl Default for InnerNodeWidthAssignment {
    fn default() -> Self {
        Self {
            widths: Box::from([
                InnerNodeWidth::new(4).unwrap(),
                InnerNodeWidth::new(16).unwrap(),
                InnerNodeWidth::new(48).unwrap(),
            ]),
            kinds: Box::from([
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::ChildOnlyCompressed,
            ]),
        }
    }
}

impl InnerNodeWidthAssignment {
    /// Create a new assignment with the given widths and kinds.
    ///
    /// The widths are checked to make sure that:
    ///   1. [`InnerNodeWidth::MAX`] is not present
    ///   2. The list of widths is sorted
    ///
    /// Otherwise, this functions returns `None`.
    pub fn new(
        widths: impl Into<Box<[InnerNodeWidth]>>,
        kinds: impl Into<Box<[InnerNodeKind]>>,
    ) -> Option<Self> {
        let widths = widths.into();
        let kinds = kinds.into();
        let contains_256_width = widths
            .as_ref()
            .iter()
            .any(|width| *width == InnerNodeWidth::MAX);
        let is_sorted = widths.as_ref().is_sorted();
        if contains_256_width || !is_sorted {
            return None;
        }

        Some(Self { widths, kinds })
    }

    fn iter(&self) -> impl Iterator<Item = (InnerNodeWidth, InnerNodeKind)> + use<'_> {
        self.widths.iter().copied().zip(self.kinds.iter().copied())
    }

    /// Calculate the cost for this assignment given the inner node width
    /// distribution.
    pub fn cost_for(&self, dist: &InnerNodeWidthDistribution) -> f64 {
        let staggered_iter = iter::once(None).chain(self.iter().map(|(w, _)| Some(w)));

        let mut cost = 0.0;
        for (prev_width, (curr_width, curr_kind)) in staggered_iter.zip(self.iter()) {
            cost += cost_between(prev_width, curr_width, curr_kind, dist);
        }

        cost
    }
}

/// Calculate the cost for using an inner node of `new_width` preceded by a
/// inner node of width `prev_width` with the given `kind` calculated against
/// the given distribution.
///
/// This function allows for incrementally calculating the assignment cost by
/// summing the cost between successive pairs of widths in the assignment.
fn cost_between(
    prev_width: Option<InnerNodeWidth>,
    new_width: InnerNodeWidth,
    kind: InnerNodeKind,
    dist: &InnerNodeWidthDistribution,
) -> f64 {
    let mut current_width = match prev_width {
        // This is the typical case, where we're dealing with a previous width ranging from [2,
        // 256]
        Some(width) => {
            match width.increment() {
                Some(width) => width,
                // In this case we overflow the width value, so the range of possible costs
                // would have been empty. Returning 0 to represent 0 cost
                None => return 0.0,
            }
        },
        // This case indicates that there is no previous width and we're starting with the very
        // first width
        None => InnerNodeWidth::MIN,
    };

    let bytes_per_node = match kind {
        InnerNodeKind::KeyChildCompressed => {
            // for a node of width w, this kind has size (w * 1) + (w *
            // mem::size_of::<* const ()>())
            new_width.get() + (new_width.get() * mem::size_of::<*const ()>())
        },
        InnerNodeKind::ChildOnlyCompressed => {
            // for a node of width w, this kind has a size of (256 * 1) + (w
            // * mem::size_of::<* const ()>())
            256 + new_width.get() * mem::size_of::<*const ()>()
        },
    };
    let mut num_nodes = 0;
    while current_width <= new_width {
        let count = dist.get(current_width);
        num_nodes += count;

        current_width = match current_width.increment() {
            Some(w) => w,
            None => break,
        };
    }

    // This calculation of the cost only considers the space usage of the nodes.
    // Under this criteria, the `InnerNodeKind::KeyChildCompressed` will always have
    // better space usage than `InnerNodeKind::ChildOnlyCompressed`. A future
    // extension would be to calculate some weighted score that also consider
    // relative operation speed, since lookup (and maybe update) should be faster
    // for the `ChildOnlyCompressed` node kind.
    let total_cost = (bytes_per_node * num_nodes) as f64;

    total_cost
}

#[cfg(test)]
mod tests {
    use std::{iter, vec::Vec};

    use blart::{
        testing::{
            generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed,
            PrefixExpansion,
        },
        AsBytes, TreeMap,
    };

    use super::*;

    fn into_dist(
        expected_dist: impl IntoIterator<Item = (usize, usize)>,
    ) -> InnerNodeWidthDistribution {
        expected_dist
            .into_iter()
            .map(|(width, count)| match width.try_into() {
                Ok(width) => Ok((width, count)),
                Err(err) => Err(err),
            })
            .collect::<Result<InnerNodeWidthDistribution, _>>()
            .unwrap()
    }

    #[rustfmt::skip]
    const SOSD_KEYS_SAMPLE: [u64; 257] = [
        0, 3072, 3841, 5633, 514, 2306, 3331, 2821, 1542, 4102, 1033, 779, 2571, 4875,
        5387, 4364, 4621, 2062, 272, 3090, 19, 5139, 1812, 5908, 4374, 5654, 2839, 1560,
        2072, 4120, 3609, 1306, 796, 3872, 5410, 206984419875, 4900, 549, 3367, 1064,
        2088, 2345, 5673, 1322, 3114, 4138, 299, 44, 1836, 2604, 5933, 4398, 4655, 1584,
        2870, 3894, 5174, 826, 1083, 1851, 3643, 2365, 3389, 5437, 1343, 65, 3137, 2114,
        2626, 5700, 325, 1605, 214069925957, 4935, 5191, 4168, 585, 5961, 1100, 3660,
        4686, 3151, 3408, 81, 1874, 2386, 2644, 4438, 3671, 158750126168, 224094909784,
        2905, 3929, 1115, 5723, 1373, 350, 1630, 2142, 4191, 5471, 100, 868, 4708,
        228520747364, 5989, 3430, 4966, 5223, 2920, 3177, 1899, 2414, 2671, 1393, 4209,
        1139, 4467, 630, 5494, 375, 1655, 5751, 2169, 3449, 222260825465, 3706, 3197,
        894, 4222, 127, 5248, 1921, 2946, 6019, 3973, 1158, 2696, 393, 2443, 3467, 4491,
        652, 5517, 5773, 2190, 4751, 5007, 4241, 3730, 1684, 1942, 3223, 104332326807,
        5784, 2714, 668, 2972, 157, 1437, 227923632542, 2463, 3745, 4513, 5281, 2210,
        5538, 6051, 4004, 4263, 424, 1960, 3241, 226313987243, 4781, 48645451182, 1199,
        4527, 944, 2736, 3504, 2228, 5044, 1717, 2997, 694, 1463, 5303, 440, 5816, 2489,
        1980, 4287, 5567, 3778, 4035, 196, 224873033926, 3528, 206412705224, 2761, 4554,
        6091, 716, 972, 1228, 3277, 2254, 4814, 5070, 463, 2001, 5843, 1492, 5588, 5333,
        2519, 3031, 216, 1752, 4312, 729, 3545, 6105, 4060, 4572, 1249, 2273, 5089, 483,
        4835, 996, 1508, 5862, 3047, 232, 745, 4075, 6123, 3308, 2030, 4591, 5105, 3826,
        1523, 1779, 2547, 2803, 1013, 4855, 5368, 3578, 1275, 764, 4348, 5116, 5885
    ];

    #[rustfmt::skip]
    const SOSD_BOOKS_200M_UINT64_INNER_NODE_DIST: [(usize, usize); 184] = [
        (2, 11830642), (3, 5452371), (4, 3710455), (5, 2879737), (6, 2459903),
        (7, 2178760), (8, 1906493), (9, 1607749), (10, 1286507), (11, 970071),
        (12, 687658), (13, 456097), (14, 283274), (15, 165793), (16, 91452),
        (17, 47349), (18, 23737), (19, 11403), (20, 5369), (21, 2651), (22, 1694),
        (23, 1442), (24, 1731), (25, 2310), (26, 3207), (27, 4558), (28, 6115),
        (29, 8191), (30, 10385), (31, 12377), (32, 14708), (33, 16365), (34, 18349),
        (35, 19120), (36, 19566), (37, 19372), (38, 18634), (39, 17584), (40, 15815),
        (41, 14053), (42, 11884), (43, 10074), (44, 8212), (45, 6460), (46, 5150),
        (47, 3743), (48, 2773), (49, 2038), (50, 1458), (51, 967), (52, 651), (53, 457),
        (54, 277), (55, 178), (56, 108), (57, 78), (58, 41), (59, 33), (60, 10),
        (61, 7), (62, 5), (63, 2), (67, 1), (83, 3), (84, 1), (85, 2), (86, 4), (87, 4),
        (88, 5), (89, 6), (90, 16), (91, 27), (92, 42), (93, 56), (94, 91), (95, 123),
        (96, 184), (97, 235), (98, 299), (99, 469), (100, 652), (101, 797), (102, 1032),
        (103, 1357), (104, 1632), (105, 2066), (106, 2492), (107, 2916), (108, 3446),
        (109, 4104), (110, 4544), (111, 4989), (112, 5346), (113, 5868), (114, 6312),
        (115, 6614), (116, 6936), (117, 6825), (118, 6709), (119, 6789), (120, 6521),
        (121, 6327), (122, 5931), (123, 5456), (124, 4982), (125, 4446), (126, 3981),
        (127, 3484), (128, 3034), (129, 2556), (130, 2141), (131, 1693), (132, 1326),
        (133, 1084), (134, 849), (135, 654), (136, 511), (137, 397), (138, 275),
        (139, 183), (140, 131), (141, 92), (142, 75), (143, 47), (144, 37), (145, 22),
        (146, 17), (147, 8), (148, 2), (149, 3), (150, 2), (151, 3), (154, 1), (206, 4),
        (207, 2), (208, 5), (209, 11), (210, 20), (211, 33), (212, 59), (213, 85),
        (214, 162), (215, 250), (216, 371), (217, 558), (218, 732), (219, 1098),
        (220, 1484), (221, 2007), (222, 2439), (223, 3100), (224, 3703), (225, 4368),
        (226, 4686), (227, 5189), (228, 5393), (229, 5323), (230, 5120), (231, 4768),
        (232, 4212), (233, 3621), (234, 2981), (235, 2286), (236, 1737), (237, 1311),
        (238, 966), (239, 628), (240, 383), (241, 240), (242, 165), (243, 56),
        (244, 41), (245, 20), (246, 6), (247, 4), (248, 5), (249, 5), (250, 25),
        (251, 151), (252, 654), (253, 2417), (254, 6571), (255, 12917), (256, 47149),
    ];

    #[test]
    fn analyze_inner_node_width_cases() {
        #[track_caller]
        fn check(
            keys: impl Iterator<Item = impl AsBytes>,
            expected_dist: impl IntoIterator<Item = (usize, usize)>,
        ) {
            let expected_dist = into_dist(expected_dist);

            let mut tree = TreeMap::new();
            let keys = keys.inspect(|k| {
                let key = Vec::from(k.as_bytes()).into_boxed_slice();
                let _ = tree.try_insert(key, ());
            });

            let results = analyze_sorted_key_iter(keys);

            assert_eq!(results, expected_dist);
        }

        check(
            SOSD_KEYS_SAMPLE.into_iter(),
            [(2, 46), (3, 18), (4, 3), (166, 1)],
        );
        check(generate_keys_skewed(10), [(2, 9)]);
        check(
            generate_key_fixed_length([4, 3, 2, 1]),
            [(5, 1), (4, 5), (3, 20), (2, 60)],
        );
        check(iter::once([0, 0, 0, 0]), []);
        check([[0, 0, 0, 0], [1, 1, 1, 1]].into_iter(), [(2, 1)]);
        check(0u8..=u8::MAX, [(256, 1)]);
        check(
            generate_key_with_prefix(
                [4, 3, 2, 1],
                [
                    PrefixExpansion {
                        base_index: 0,
                        expanded_length: 4,
                    },
                    PrefixExpansion {
                        base_index: 3,
                        expanded_length: 4,
                    },
                ],
            ),
            [(5, 1), (4, 5), (3, 20), (2, 60)],
        );
    }

    #[test]
    fn lexicographic_ordering_for_slice_lengths() {
        let mut v: Vec<&[u8]> = vec![&[2, 1, 0], &[1, 0], &[0, 1], &[0], &[]];

        v.sort();

        assert_eq!(v, [&[], &[0u8][..], &[0, 1], &[1, 0], &[2, 1, 0]])
    }

    #[test]
    fn find_optimal_assignment_cases() {
        #[track_caller]
        fn check<const K: usize>(
            dist: impl IntoIterator<Item = (usize, usize)>,
            expected_cost: f64,
            expected_assignment: [InnerNodeWidth; K],
            expected_kinds: [InnerNodeKind; K],
        ) {
            let dist = into_dist(dist);
            let assignment = dist.find_optimal_assignment(K + 1);
            let cost = assignment.cost_for(&dist);

            assert_eq!(cost, expected_cost, "{assignment:?}");
            assert_eq!(assignment.widths, Box::from(expected_assignment));
            assert_eq!(assignment.kinds, Box::from(expected_kinds));
        }

        check(
            [(5, 1), (4, 5), (3, 20), (2, 60)],
            2250.0,
            [2.try_into().unwrap(), 5.try_into().unwrap()],
            [
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
            ],
        );
        check(
            SOSD_BOOKS_200M_UINT64_INNER_NODE_DIST,
            2797954047.0,
            [
                5.try_into().unwrap(),
                13.try_into().unwrap(),
                46.try_into().unwrap(),
            ],
            [
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
            ],
        );
        check(
            SOSD_BOOKS_200M_UINT64_INNER_NODE_DIST,
            2153940462.0,
            [
                2.try_into().unwrap(),
                4.try_into().unwrap(),
                7.try_into().unwrap(),
                11.try_into().unwrap(),
                16.try_into().unwrap(),
                46.try_into().unwrap(),
                132.try_into().unwrap(),
            ],
            [
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
                InnerNodeKind::KeyChildCompressed,
            ],
        )
    }

    #[test]
    fn cost_for_cases() {
        #[track_caller]
        fn check(
            assignment: InnerNodeWidthAssignment,
            key_dist: impl IntoIterator<Item = (usize, usize)>,
            expected_cost: f64,
        ) {
            let key_dist = into_dist(key_dist);
            let cost = assignment.cost_for(&key_dist);

            assert_eq!(cost, expected_cost);
        }

        check(
            InnerNodeWidthAssignment::default(),
            [(5, 1), (4, 5), (3, 20), (2, 60)],
            3204.0,
        );
        check(
            InnerNodeWidthAssignment::new(
                [2.try_into().unwrap(), 5.try_into().unwrap()],
                [
                    InnerNodeKind::KeyChildCompressed,
                    InnerNodeKind::KeyChildCompressed,
                ],
            )
            .unwrap(),
            [(5, 1), (4, 5), (3, 20), (2, 60)],
            2250.0,
        );
        check(
            InnerNodeWidthAssignment::default(),
            SOSD_BOOKS_200M_UINT64_INNER_NODE_DIST,
            3145151824.0,
        );
    }
}
