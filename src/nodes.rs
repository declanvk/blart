//! Trie node representation and manipulation

mod operations;
mod representation;

mod header;

pub mod visitor;

pub use header::*;
pub(crate) use operations::*;
pub use representation::*;
