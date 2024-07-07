//! Trie node representation and manipulation

mod operations;
mod representation;

pub mod visitor;

pub(crate) use operations::*;
pub use representation::*;
