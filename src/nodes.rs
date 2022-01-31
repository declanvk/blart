//! Trie node representation and manipulation

mod operations;
mod representation;
pub mod visitor;

pub use operations::*;
pub use representation::*;

#[cfg(test)]
mod tests_common;
