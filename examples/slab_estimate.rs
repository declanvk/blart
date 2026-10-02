//! Estimate memory impact of 32-bit slab indices in place of 64-bit node pointers.
use blart::{
    testing::generate_key_fixed_length,
    visitor::{InnerNodeKind, TreeStats, TreeStatsCollector},
    AsBytes, TreeMap,
};
use rand::{seq::SliceRandom, Rng, SeedableRng};
use std::{hint::black_box, time::Instant};

fn time_gets<K: AsBytes + Clone, V>(tree: &TreeMap<K, V>, keys: &[K]) {
    let mut ks = keys.to_vec();
    ks.shuffle(&mut rand::rngs::StdRng::seed_from_u64(7));
    let reps = (4_000_000 / ks.len()).max(1);
    let mut best = f64::MAX;
    for _ in 0..3 {
        let t = Instant::now();
        for _ in 0..reps {
            for k in &ks {
                black_box(tree.get(black_box(k)));
            }
        }
        best = best.min(t.elapsed().as_nanos() as f64 / (reps * ks.len()) as f64);
    }
    // in-order lookups: neighbouring keys share most of the path (warm path)
    let t = Instant::now();
    for _ in 0..reps {
        for k in keys {
            black_box(tree.get(black_box(k)));
        }
    }
    let seq = t.elapsed().as_nanos() as f64 / (reps * keys.len()) as f64;
    println!("   get: random order {best:.1} ns/op, sorted order {seq:.1} ns/op");
}

// Projected inner node sizes with 4-byte child slots (main's 24-byte header, PREFIX_LEN=16)
// N4:   24 + 4 keys + 4*4  = 44
// N16:  24 + 16 keys + 16*4 = 104
// N48:  24 + 256 index + 48*4 = 472
// N256: 24 + 256*4 = 1048
const PROJ: [(InnerNodeKind, usize); 4] = [
    (InnerNodeKind::Node4, 44),
    (InnerNodeKind::Node16, 104),
    (InnerNodeKind::Node48, 472),
    (InnerNodeKind::Node256, 1048),
];

fn report<K: AsBytes, V>(name: &str, tree: &TreeMap<K, V>) {
    let s: TreeStats = TreeStatsCollector::collect(tree).unwrap();
    let n = s.leaf.count as f64;
    let leaf_size = s.leaf.mem_usage / s.leaf.count;
    // previous/next leaf pointers shrink 8 -> 4 each
    let proj_leaf_size = leaf_size - 8;

    let mut cur_inner = 0usize;
    let mut proj_inner = 0usize;
    let mut mix = String::new();
    for (kind, proj) in PROJ {
        if let Some(st) = s.inner_node.get(kind) {
            cur_inner += st.mem_usage;
            proj_inner += st.count * proj;
            mix += &format!(
                "{kind:?}={} ({:.0}% full) ",
                st.count,
                100.0 * st.percentage_slots()
            );
        }
    }
    let cur_total = cur_inner + s.leaf.mem_usage;
    let proj_total = proj_inner + s.leaf.count * proj_leaf_size;
    let depth: usize = s.path_kind_visits.iter().sum();
    let pv = s.path_kind_visits.map(|v| v as f64 / n);

    println!("== {name}: {} keys", s.leaf.count);
    println!("   inner nodes: {mix}");
    println!(
        "   avg inner depth {:.2} (max {}), path mix N4/N16/N48/N256 = {:.2}/{:.2}/{:.2}/{:.2}",
        depth as f64 / n,
        s.max_depth,
        pv[0],
        pv[1],
        pv[2],
        pv[3]
    );
    println!(
        "   inner bytes/key {:.1} -> {:.1} ({:+.1}%)",
        cur_inner as f64 / n,
        proj_inner as f64 / n,
        100.0 * (proj_inner as f64 / cur_inner as f64 - 1.0)
    );
    println!(
        "   leaf size {leaf_size} -> {proj_leaf_size}; total bytes/key {:.1} -> {:.1} ({:+.1}%)",
        cur_total as f64 / n,
        proj_total as f64 / n,
        100.0 * (proj_total as f64 / cur_total as f64 - 1.0)
    );
}

fn main() {
    let dict = include_str!("../benches/data/dict.txt");
    for (name, src) in [("medium-dict.txt", include_str!("../benches/data/medium-dict.txt")), ("dict.txt", dict)] {
        let mut t: TreeMap<Box<[u8]>, usize> = TreeMap::new();
        let mut keys = Vec::new();
        for (i, w) in src.lines().enumerate() {
            let mut k = w.as_bytes().to_vec();
            k.push(0);
            let k = k.into_boxed_slice();
            if t.try_insert(k.clone(), i).unwrap().is_none() { keys.push(k); }
        }
        report(&format!("{name} words (Box<[u8]>)"), &t);
        keys.sort();
        time_gets(&t, &keys);
    }

    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    for n in [1_000_000usize, 10_000_000] {
        let mut t: TreeMap<[u8; 8], usize> = TreeMap::new();
        let mut keys = Vec::new();
        for i in 0..n {
            let k = rng.random::<u64>().to_be_bytes();
            if t.try_insert(k, i).unwrap().is_none() { keys.push(k); }
        }
        report(&format!("random u64 x{n}"), &t);
        keys.sort();
        time_gets(&t, &keys);
    }

    let mut t: TreeMap<[u8; 8], usize> = TreeMap::new();
    for i in 0..10_000_000u64 {
        let _ = t.try_insert(i.to_be_bytes(), i as usize);
    }
    report("sequential u64 x10M", &t);
    let keys: Vec<[u8; 8]> = (0..10_000_000u64).map(|i| i.to_be_bytes()).collect();
    time_gets(&t, &keys);
    drop(t);

    let mut t: TreeMap<[u8; 16], usize> = TreeMap::new();
    for i in 0..1_000_000usize {
        let _ = t.try_insert(rng.random::<u128>().to_be_bytes(), i);
    }
    report("random 16-byte (uuid-like) x1M", &t);
    drop(t);

    let mut t: TreeMap<[u8; 10], usize> = TreeMap::new();
    for (i, k) in generate_key_fixed_length([3; 10]).enumerate() {
        let _ = t.try_insert(k, i);
    }
    report("fixed [3;10] (all full N4)", &t);
    drop(t);

    let mut t: TreeMap<[u8; 20], usize> = TreeMap::new();
    for (i, k) in generate_key_fixed_length([1; 20]).enumerate() {
        let _ = t.try_insert(k, i);
    }
    report("fixed [1;20] (all binary N4)", &t);
}
