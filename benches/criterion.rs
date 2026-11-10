use criterion::criterion_main;

#[macro_use]
mod common;

mod node;
mod tree;

criterion_main!(
    node::common_prefix_len::bench_common_prefix_len_group,
    node::min_max::bench_min_max_group,
    tree::clone::bench_clone_group,
    tree::dict_get::bench_dict_get_group,
    tree::dict_insert::bench_dict_insert_group,
    tree::dict_remove::bench_dict_remove_group,
    tree::entry::bench_entry_group,
    tree::fuzzy::bench_fuzzy_group,
    tree::generated_get::bench_generated_get_group,
    tree::generated_insert::bench_generated_insert_group,
    tree::int_keys::bench_int_keys_group,
    tree::iter::bench_iter_group,
    tree::long_prefix::bench_long_prefix_group,
);
