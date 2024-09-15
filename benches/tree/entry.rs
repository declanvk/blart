use std::ffi::CString;

use blart::TreeMap;
use criterion::{criterion_group, Criterion};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};

fn bench(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(69420);
    let words = include_str!("../data/medium-dict.txt");

    let mut words: Vec<_> = words.lines().map(|s| CString::new(s).unwrap()).collect();
    words.dedup();
    words.sort();

    let count = 200;

    let mut occupied: Vec<_> = words.choose_multiple(&mut rng, count).cloned().collect();
    occupied.sort();

    let mut vacant: Vec<_> = occupied
        .choose_multiple(&mut rng, count / 2)
        .cloned()
        .collect();
    vacant.sort();

    words.retain(|w| vacant.binary_search(w).is_err());
    occupied.retain(|w| vacant.binary_search(w).is_err());

    let tree: TreeMap<_, _> = words
        .into_iter()
        .map(|w| (CString::new(w).unwrap(), 0))
        .collect();

    {
        let mut group = c.benchmark_group("entry");

        for (ty, vals) in [("vacant", vacant.clone()), ("occupied", occupied.clone())] {
            group.bench_function(format!("{ty}/or_default"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            tree.entry(word).or_default();
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });

            group.bench_function(format!("{ty}/or_default_entry/remove"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            tree.entry(word).or_default_entry().remove();
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });

            group.bench_function(format!("{ty}/insert_entry"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            tree.entry(word).insert_entry(0);
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });

            group.bench_function(format!("{ty}/insert_entry/remove"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            tree.entry(word).insert_entry(0).remove();
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });

            group.bench_function(format!("{ty}/and_modify/or_default"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            tree.entry(word).and_modify(|v| *v = 0).or_default();
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });
        }
    }

    {
        let mut group = c.benchmark_group("entry/default");

        for (ty, vals) in [("vacant", vacant), ("occupied", occupied)] {
            group.bench_function(format!("{ty}/or_default"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            if tree.get(&word).is_none() {
                                tree.insert(word, i32::default());
                            }
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });

            group.bench_function(format!("{ty}/or_default_entry/remove"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            if tree.get(&word).is_none() {
                                tree.insert(word.clone(), i32::default());
                            }
                            tree.remove(&word);
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });

            group.bench_function(format!("{ty}/insert_entry"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            match tree.get_mut(&word) {
                                Some(v) => {
                                    *v = 0;
                                },
                                None => {
                                    tree.insert(word, 0);
                                },
                            };
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });

            group.bench_function(format!("{ty}/insert_entry/remove"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            match tree.get_mut(&word) {
                                Some(v) => {
                                    *v = 0;
                                },
                                None => {
                                    tree.insert(word.clone(), 0);
                                },
                            };
                            tree.remove(&word);
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });

            group.bench_function(format!("{ty}/and_modify/or_default"), |b| {
                b.iter_batched(
                    || (tree.clone(), vals.clone()),
                    |(mut tree, vals)| {
                        for word in vals {
                            if let Some(v) = tree.get_mut(&word) {
                                *v = 0;
                            } else {
                                tree.insert(word, i32::default());
                            };
                        }
                        tree
                    },
                    criterion::BatchSize::SmallInput,
                )
            });
        }
    }
}

criterion_group!(bench_entry_group, bench);
