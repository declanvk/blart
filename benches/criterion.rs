use criterion::criterion_main;

#[macro_use]
mod common;

mod node;
mod tree;

criterion_main!(
    node::match_prefix::bench_match_prefix_group,
    node::min_max::bench_min_max_group,
    tree::clone::bench_clone_group,
    tree::dict_get::bench_dict_get_group,
    tree::dict_insert::bench_dict_insert_group,
    tree::entry::bench_entry_group,
    tree::fuzzy::bench_fuzzy_group,
    tree::generated_get::bench_generated_get_group,
    tree::generated_insert::bench_generated_insert_group,
    tree::iter::bench_iter_group,
);
