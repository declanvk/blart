use argh::FromArgs;
use rad_tree::{deallocate_tree, insert, visitor::DotPrinter, LeafNode, NodePtr, OpaqueNodePtr};
use std::{
    error::Error,
    fmt::Display,
    fs::OpenOptions,
    io::{self, BufWriter, Write},
    iter,
    str::FromStr,
};

#[derive(FromArgs)]
/// Reach new heights.
struct TreeToDotArgs {
    /// what shape of tree to generate
    #[argh(positional)]
    shape: TreeShape,

    /// how large the tree should be
    #[argh(positional)]
    size: usize,

    /// where to output the tree diagram
    ///
    /// To output to stdout, use '_'.
    #[argh(positional)]
    output_location: String,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: TreeToDotArgs = argh::from_env();

    let tree = if let Some(tree) = make_tree(args.shape.generate_keys(args.size)) {
        tree
    } else {
        return Err(Box::new(EmptyTreeError));
    };

    if args.output_location == "_" {
        let stdout = io::stdout();
        let handle = stdout.lock();

        let mut buffer = BufWriter::new(handle);

        write_tree(&mut buffer, &tree)?;
    } else {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(args.output_location)?;

        let mut buffer = BufWriter::new(file);

        write_tree(&mut buffer, &tree)?;
    }

    // SAFETY: The `tree` pointer is the only pointer to the underlying node. There
    // will be no dangling nodes from this.
    unsafe { deallocate_tree(tree) };

    Ok(())
}

fn make_tree(iter: impl Iterator<Item = Box<[u8]>>) -> Option<OpaqueNodePtr<usize>> {
    let mut iter = iter.enumerate();
    let (first_value, first_key) = iter.next()?;
    let mut current_root =
        NodePtr::allocate_node(LeafNode::new(first_key, first_value)).to_opaque();

    for (value, key) in iter {
        // SAFETY: There are no other pointers to `current_root` node. There are no
        // concurrent reads or writes to the `current_root` node ongoing.
        current_root = unsafe { insert(current_root, LeafNode::new(key, value)).unwrap() };
    }

    Some(current_root)
}

fn write_tree(output: &mut dyn Write, tree: &OpaqueNodePtr<usize>) -> Result<(), Box<dyn Error>> {
    DotPrinter::print_tree(output, &tree)?;

    Ok(())
}

#[derive(Debug)]
enum TreeShape {
    LeftSkew,
    FullNode4,
    FullNode16,
    FullNode48,
    FullNode256,
}

impl TreeShape {
    fn generate_keys(self, tree_size: usize) -> Box<dyn Iterator<Item = Box<[u8]>>> {
        match self {
            TreeShape::LeftSkew => Box::new(TreeShape::generate_left_skew_keys(tree_size)),
            TreeShape::FullNode4 => Box::new(TreeShape::generate_full_keys(tree_size, 4)),
            TreeShape::FullNode16 => Box::new(TreeShape::generate_full_keys(tree_size, 16)),
            TreeShape::FullNode48 => Box::new(TreeShape::generate_full_keys(tree_size, 48)),
            TreeShape::FullNode256 => Box::new(TreeShape::generate_full_keys(tree_size, 256)),
        }
    }

    fn generate_left_skew_keys(tree_size: usize) -> impl Iterator<Item = Box<[u8]>> {
        (0..tree_size).map(|key_size| {
            (0..key_size)
                .map(|_| 1u8)
                .chain(iter::once(u8::MAX))
                .collect::<Vec<_>>()
                .into_boxed_slice()
        })
    }

    fn generate_full_keys(
        tree_height: usize,
        node_width: usize,
    ) -> impl Iterator<Item = Box<[u8]>> {
        // tree size will be interpreted as the number of levels of all
        // InnerNode{node_width} with a last layer of leaves
        //
        // Assuming node_width = 4
        // 1 level - 4 leaves
        //  0,255:0|1,255:1|2,255:2|3,255:3
        // 2 levels - 16 leaves
        //  0,0,255:0|0,1,255:1|0,2,255:2|0,3,255:3
        //  1,0,255:0|1,1,255:1|1,2,255:2|1,3,255:3
        //  2,0,255:0|2,1,255:1|2,2,255:2|2,3,255:3
        //  3,0,255:0|3,1,255:1|3,2,255:2|3,3,255:3
        // 3 levels - 64 leaves

        // [0-3],[0-3],...,[0-3],256
        // \---- n numbers ----/
        // total key size is n + 1

        struct FullKeysIter {
            tree_height: usize,
            node_width: usize,
            digit_stack: Vec<u8>,
        }

        impl Iterator for FullKeysIter {
            type Item = Box<[u8]>;

            fn next(&mut self) -> Option<Self::Item> {
                if self.digit_stack.is_empty() {
                    return None;
                }

                let mut new_key = self.digit_stack.clone();
                new_key.push(u8::MAX);
                let new_key = new_key.into_boxed_slice();

                // update the stack for next value

                for digit_idx in (0..self.tree_height).rev() {
                    if let Some(updated_digit) = self.digit_stack[digit_idx].checked_add(1) {
                        self.digit_stack[digit_idx] = updated_digit
                    } else {
                        // At 256, max width
                        self.digit_stack.pop();
                        continue;
                    }

                    if usize::from(self.digit_stack[digit_idx]) >= self.node_width {
                        self.digit_stack.pop();
                    } else {
                        // under limit
                        break;
                    }
                }

                if !self.digit_stack.is_empty() {
                    while self.digit_stack.len() < self.tree_height {
                        self.digit_stack.push(0);
                    }
                }

                Some(new_key)
            }
        }

        Box::new(FullKeysIter {
            tree_height,
            node_width,
            digit_stack: vec![0; tree_height],
        })
    }
}

impl FromStr for TreeShape {
    type Err = ShapeParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "left_skew" => Ok(TreeShape::LeftSkew),
            "full_node4" => Ok(TreeShape::FullNode4),
            "full_node16" => Ok(TreeShape::FullNode16),
            "full_node48" => Ok(TreeShape::FullNode48),
            "full_node256" => Ok(TreeShape::FullNode256),
            _ => Err(ShapeParseError(s.into())),
        }
    }
}

#[derive(Debug)]
struct ShapeParseError(String);

impl Display for ShapeParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Unable to parse tree shape from argument value [{}].",
            self.0
        )
    }
}

#[derive(Debug)]
struct EmptyTreeError;

impl Display for EmptyTreeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "There were no keys to insert into the tree!")
    }
}

impl Error for EmptyTreeError {}
