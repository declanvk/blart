use crate::{
    alloc::Allocator,
    raw::{InnerNode, NodeType, OpaqueNodePtr},
    visitor::{Visitable, Visitor},
    AsBytes, TreeMap,
};
use std::{
    fmt::{self},
    io::{self, Write},
};

/// Settings which customize the output of the [`DotPrinter`] visitor.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct DotPrinterSettings {
    /// Add node address to output in graphs
    pub display_node_address: bool,
}

/// A visitor of the radix trie that will print the tree in "dot" notation.
///
/// See ['DOT Language | Graphviz'](https://graphviz.org/doc/info/lang.html) for
/// information about syntax and example of the language.
pub struct DotPrinter<O: Write, K, V> {
    output: O,
    next_id: usize,
    settings: DotPrinterSettings,
    key_fmt: fn(&K, &mut fmt::Formatter<'_>) -> fmt::Result,
    value_fmt: fn(&V, &mut fmt::Formatter<'_>) -> fmt::Result,
}

impl<O: Write, K, V> DotPrinter<O, K, V> {
    /// Write the dot-format of the given tree to the given output.
    pub fn print<const PREFIX_LEN: usize, A: Allocator>(
        output: O,
        tree: &TreeMap<K, V, PREFIX_LEN, A>,
        settings: DotPrinterSettings,
    ) -> Option<io::Result<()>>
    where
        K: fmt::Display,
        V: fmt::Display,
    {
        Self::print_with_fmt(
            output,
            tree,
            settings,
            <K as fmt::Display>::fmt,
            <V as fmt::Display>::fmt,
        )
    }

    /// Write the dot-format of the given tree to the given output.
    pub fn print_with_fmt<const PREFIX_LEN: usize, A: Allocator>(
        output: O,
        tree: &TreeMap<K, V, PREFIX_LEN, A>,
        settings: DotPrinterSettings,
        key_fmt: fn(&K, &mut fmt::Formatter<'_>) -> fmt::Result,
        value_fmt: fn(&V, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> Option<io::Result<()>> {
        tree.state.as_ref().map(|state| {
            // SAFETY: Since we get a reference to the `TreeMap`, we know the
            // node and all descendants will not be mutated
            unsafe { Self::print_tree(output, &state.root, settings, key_fmt, value_fmt) }
        })
    }

    /// Write the dot-format of the given tree to the given output.
    ///
    /// # Safety
    ///  - For the duration of this function, the given node and all its
    ///    children nodes must not get mutated.
    pub(crate) unsafe fn print_tree<const PREFIX_LEN: usize>(
        output: O,
        tree: &OpaqueNodePtr<K, V, PREFIX_LEN>,
        settings: DotPrinterSettings,
        key_fmt: fn(&K, &mut fmt::Formatter<'_>) -> fmt::Result,
        value_fmt: fn(&V, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> io::Result<()> {
        let mut visitor = DotPrinter {
            output,
            next_id: 0,
            settings,
            key_fmt,
            value_fmt,
        };

        visitor.output_prelude()?;
        let _ = tree.visit_with(&mut visitor)?;
        visitor.output_epilogue()
    }

    fn output_prelude(&mut self) -> io::Result<()> {
        writeln!(self.output, "strict digraph G {{")?;
        writeln!(self.output, "node [shape=record]")
    }

    fn output_epilogue(&mut self) -> io::Result<()> {
        writeln!(self.output, "}}")
    }

    fn get_id(&mut self) -> usize {
        let new_id = self.next_id;
        self.next_id += 1;
        new_id
    }

    fn write_inner_node<N, const PREFIX_LEN: usize>(&mut self, inner_node: &N) -> io::Result<usize>
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
    {
        let header = inner_node.header();
        let node_id = self.get_id();
        write!(self.output, "n{node_id} ")?;
        write!(self.output, "[label=\"{{")?;
        // write header line
        if self.settings.display_node_address {
            write!(
                self.output,
                "{{<h0> {:p}}}  | {{{:?} | {:?} | {:?}}} | {{",
                inner_node as *const _,
                N::TYPE,
                header.prefix_len(),
                header.read_prefix()
            )?;
        } else {
            write!(
                self.output,
                "{{<h0> {:?} | {:?} | {:?}}} | {{",
                N::TYPE,
                header.prefix_len(),
                header.read_prefix()
            )?;
        }

        // SAFETY: The `child_it` does not live beyond the following loop and will not
        // overlap with any mutating access or operation, which is guaranteed by the
        // `print_tree` caller requirements.
        let child_it = inner_node.iter();
        for (idx, (key_fragment, _)) in child_it.enumerate() {
            if idx == 0 {
                write!(self.output, "<c{idx}> {key_fragment}")?;
            } else {
                write!(self.output, "| <c{idx}> {key_fragment}")?;
            }
        }
        writeln!(self.output, "}}}}\"]")?;

        // SAFETY: The `child_it` does not live beyond the following loop and will not
        // overlap with any mutating access or operation, which is guaranteed by the
        // `print_tree` caller requirements.
        let child_it = inner_node.iter();
        for (key_frag_id, (_, child)) in child_it.enumerate() {
            let child_id = child.visit_with(self)?;

            writeln!(self.output, "n{node_id}:c{key_frag_id} -> n{child_id}:h0")?;
        }

        Ok(node_id)
    }
}

impl<K, V, O, const PREFIX_LEN: usize> Visitor<K, V, PREFIX_LEN> for DotPrinter<O, K, V>
where
    O: Write,
{
    type Output = io::Result<usize>;

    fn default_output(&self) -> Self::Output {
        unimplemented!("this visitor should never use the default output")
    }

    fn combine_output(&self, _: Self::Output, _: Self::Output) -> Self::Output {
        unimplemented!("this visitor should never combine outputs")
    }

    fn visit_node4(&mut self, t: &super::InnerNode4<K, V, PREFIX_LEN>) -> Self::Output {
        self.write_inner_node(t)
    }

    fn visit_node16(&mut self, t: &super::InnerNode16<K, V, PREFIX_LEN>) -> Self::Output {
        self.write_inner_node(t)
    }

    fn visit_node48(&mut self, t: &super::InnerNode48<K, V, PREFIX_LEN>) -> Self::Output {
        self.write_inner_node(t)
    }

    fn visit_node256(&mut self, t: &super::InnerNode256<K, V, PREFIX_LEN>) -> Self::Output {
        self.write_inner_node(t)
    }

    fn visit_leaf(&mut self, t: &super::LeafNode<K, V, PREFIX_LEN>) -> Self::Output {
        let key = OverrideDisplay {
            value: t.key_ref(),
            fmt_fn: self.key_fmt,
        };
        let value = OverrideDisplay {
            value: t.value_ref(),
            fmt_fn: self.value_fmt,
        };

        let node_id = self.get_id();
        write!(self.output, "n{node_id} ")?;
        write!(self.output, "[label=\"{{")?;
        // write header line
        if self.settings.display_node_address {
            writeln!(
                self.output,
                "{{<h0> {:p}}} | {{{:?}}} | {{{}}} | {{{}}} | {{{:p} {:p}}} }}\"]",
                t as *const _,
                NodeType::Leaf,
                key,
                value,
                t.previous
                    .map_or(std::ptr::null_mut(), |prev| prev.to_ptr()),
                t.next.map_or(std::ptr::null_mut(), |next| next.to_ptr()),
            )?;
        } else {
            writeln!(
                self.output,
                "{{<h0> {:?}}} | {{{}}} | {{{}}}}}\"]",
                NodeType::Leaf,
                key,
                value
            )?;
        }

        Ok(node_id)
    }
}

#[derive(Debug)]
struct OverrideDisplay<'a, T> {
    value: &'a T,
    fmt_fn: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
}

impl<'a, T> fmt::Display for OverrideDisplay<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.fmt_fn)(&self.value, f)
    }
}

/// Print a given value using the [`Debug::fmt`] implementation.
///
/// This function can be used to override the formatting of key or value types
/// when printing with [`DotPrinter`].
///
/// [`Debug::fmt`]: std::fmt::Debug::fmt
pub fn debug_as_display_fmt(value: &impl fmt::Debug, f: &mut fmt::Formatter) -> fmt::Result {
    value.fmt(f)
}

/// Print the string "\[null\]".
///
/// This function can be used to override the formatting of key or value types
/// when printing with [`DotPrinter`].
pub fn null_display_fmt(_value: &impl fmt::Debug, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "[null]")
}

/// Print the byte representation of the given value as returned by [`AsBytes`].
///
/// This function can be used to override the formatting of key or value types
/// when printing with [`DotPrinter`].
pub fn bytes_display_fmt(value: &impl AsBytes, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{:?}", value.as_bytes())
}

#[cfg(test)]
mod tests {
    use crate::tests_common::swap;

    use super::*;

    #[test]
    fn simple_tree_output_to_dot() {
        let tree: TreeMap<_, _> = crate::tests_common::generate_key_fixed_length([3, 3])
            .enumerate()
            .map(swap)
            .collect();

        let mut buffer = Vec::new();

        DotPrinter::print_with_fmt(
            &mut buffer,
            &tree,
            DotPrinterSettings {
                display_node_address: false,
            },
            debug_as_display_fmt,
            <usize as fmt::Display>::fmt,
        )
        .unwrap()
        .unwrap();

        let output = String::from_utf8(buffer).unwrap();
        assert_eq!(
            output,
            "strict digraph G {
node [shape=record]
n0 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 1| <c2> 2| <c3> 3}}\"]
n1 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 1| <c2> 2| <c3> 3}}\"]
n2 [label=\"{{<h0> Leaf} | {[0, 0]} | {0}}\"]
n1:c0 -> n2:h0
n3 [label=\"{{<h0> Leaf} | {[0, 1]} | {1}}\"]
n1:c1 -> n3:h0
n4 [label=\"{{<h0> Leaf} | {[0, 2]} | {2}}\"]
n1:c2 -> n4:h0
n5 [label=\"{{<h0> Leaf} | {[0, 3]} | {3}}\"]
n1:c3 -> n5:h0
n0:c0 -> n1:h0
n6 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 1| <c2> 2| <c3> 3}}\"]
n7 [label=\"{{<h0> Leaf} | {[1, 0]} | {4}}\"]
n6:c0 -> n7:h0
n8 [label=\"{{<h0> Leaf} | {[1, 1]} | {5}}\"]
n6:c1 -> n8:h0
n9 [label=\"{{<h0> Leaf} | {[1, 2]} | {6}}\"]
n6:c2 -> n9:h0
n10 [label=\"{{<h0> Leaf} | {[1, 3]} | {7}}\"]
n6:c3 -> n10:h0
n0:c1 -> n6:h0
n11 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 1| <c2> 2| <c3> 3}}\"]
n12 [label=\"{{<h0> Leaf} | {[2, 0]} | {8}}\"]
n11:c0 -> n12:h0
n13 [label=\"{{<h0> Leaf} | {[2, 1]} | {9}}\"]
n11:c1 -> n13:h0
n14 [label=\"{{<h0> Leaf} | {[2, 2]} | {10}}\"]
n11:c2 -> n14:h0
n15 [label=\"{{<h0> Leaf} | {[2, 3]} | {11}}\"]
n11:c3 -> n15:h0
n0:c2 -> n11:h0
n16 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 1| <c2> 2| <c3> 3}}\"]
n17 [label=\"{{<h0> Leaf} | {[3, 0]} | {12}}\"]
n16:c0 -> n17:h0
n18 [label=\"{{<h0> Leaf} | {[3, 1]} | {13}}\"]
n16:c1 -> n18:h0
n19 [label=\"{{<h0> Leaf} | {[3, 2]} | {14}}\"]
n16:c2 -> n19:h0
n20 [label=\"{{<h0> Leaf} | {[3, 3]} | {15}}\"]
n16:c3 -> n20:h0
n0:c3 -> n16:h0
}
"
        );
    }

    #[test]
    fn debug_display_fmt_works() {
        struct TestFmt;

        impl fmt::Debug for TestFmt {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "This is the Debug impl!")
            }
        }

        let output = format!(
            "{}",
            OverrideDisplay {
                value: &TestFmt,
                fmt_fn: debug_as_display_fmt,
            }
        );
        assert_eq!(output, "This is the Debug impl!");
    }

    #[test]
    fn null_display_fmt_works() {
        let output = format!(
            "{}",
            OverrideDisplay {
                value: &(),
                fmt_fn: null_display_fmt,
            }
        );
        assert_eq!(output, "[null]");
    }

    #[test]
    fn bytes_display_fmt_works() {
        #[derive(Copy, Clone)]
        struct MyBytes(&'static [u8]);

        impl AsBytes for MyBytes {
            fn as_bytes(&self) -> &[u8] {
                self.0
            }
        }

        let value = MyBytes(&[0x01, 0x02, 0x03, 0x04]);
        let output = format!(
            "{}",
            OverrideDisplay {
                value: &value,
                fmt_fn: bytes_display_fmt
            }
        );
        assert_eq!(output, "[1, 2, 3, 4]");
    }

    #[test]
    fn print_empty_tree_returns_none() {
        let tree: TreeMap<u8, u8> = TreeMap::new();
        let mut buffer = Vec::new();

        let result = DotPrinter::print_with_fmt(
            &mut buffer,
            &tree,
            DotPrinterSettings::default(),
            debug_as_display_fmt,
            debug_as_display_fmt,
        );

        assert!(result.is_none());
        assert!(buffer.is_empty());
    }
}
