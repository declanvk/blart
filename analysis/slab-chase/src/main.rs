//! Model a Node4-style dependent lookup chain: each hop reads the header
//! (prefix compare), scans the 4 key bytes, then loads the child slot and
//! follows it. Compare 8-byte pointers vs 4-byte slab indices.
use rand::{seq::SliceRandom, SeedableRng};
use std::{hint::black_box, time::Instant};

#[repr(C, align(8))]
#[derive(Clone, Copy)]
struct PtrN4 { num: u16, plen: u32, prefix: [u8; 16], keys: [u8; 4], children: [*const PtrN4; 4] } // 64B

#[repr(C, align(4))]
#[derive(Clone, Copy)]
struct IdxN4 { num: u16, plen: u32, prefix: [u8; 16], keys: [u8; 4], children: [u32; 4] } // 44B

#[repr(C, align(64))]
#[derive(Clone, Copy)]
struct IdxN4Pad { n: IdxN4 } // 64B, 64-aligned: never straddles a line

#[repr(C, align(8))]
#[derive(Clone, Copy)]
struct IdxN4Same { n: IdxN4, _pad: [u8; 20] } // 64B with 8-align: same footprint as ptr, isolates decode cost

const TAG_BITS: u32 = 3;
const CHUNK_SHIFT: u32 = 12; // 4096 nodes per chunk

fn perm(n: usize, seed: u64) -> Vec<usize> {
    // single random cycle through all nodes
    let mut order: Vec<usize> = (0..n).collect();
    order.shuffle(&mut rand::rngs::StdRng::seed_from_u64(seed));
    let mut next = vec![0; n];
    for w in 0..n { next[order[w]] = order[(w + 1) % n]; }
    next
}

fn hdr(i: usize) -> (u16, u32, [u8; 16], [u8; 4]) {
    (4, 3, [i as u8; 16], [1, 2, 3, (i % 251) as u8])
}

macro_rules! hop_body {
    ($node:expr, $acc:ident, $key:ident) => {{
        let n = $node;
        // prefix compare + key search, like a real lookup
        $acc = $acc.wrapping_add(n.prefix[(n.plen as usize) & 15] as u64 + n.num as u64);
        let k = $key as u8;
        let mut slot = 3;
        for j in 0..4 { if n.keys[j] == k { slot = j; } }
        slot
    }};
}

fn run_ptr(n: usize, hops: usize) -> f64 {
    let next = perm(n, 1);
    let mut v: Vec<PtrN4> = (0..n).map(|i| { let (num, plen, prefix, keys) = hdr(i); PtrN4 { num, plen, prefix, keys, children: [std::ptr::null(); 4] } }).collect();
    let base = v.as_ptr();
    for i in 0..n { let c = unsafe { base.add(next[i]) }; v[i].children = [c; 4]; }
    let mut p = base; let mut acc = 0u64; let key = black_box(9usize);
    let t = Instant::now();
    for _ in 0..hops { let s = hop_body!(unsafe { &*p }, acc, key); p = unsafe { (*p).children[s] }; }
    black_box(acc); black_box(p);
    t.elapsed().as_nanos() as f64 / hops as f64
}

/// Like blart today: child pointers carry a type tag in the low 3 bits that must be masked.
fn run_ptr_tagged(n: usize, hops: usize) -> f64 {
    let next = perm(n, 1);
    let mut v: Vec<PtrN4> = (0..n).map(|i| { let (num, plen, prefix, keys) = hdr(i); PtrN4 { num, plen, prefix, keys, children: [std::ptr::null(); 4] } }).collect();
    let base = v.as_ptr();
    for i in 0..n { let c = unsafe { base.add(next[i]) }.map_addr(|a| a | 0b001); v[i].children = [c; 4]; }
    let mut p = base; let mut acc = 0u64; let key = black_box(9usize);
    let t = Instant::now();
    for _ in 0..hops { let s = hop_body!(unsafe { &*p }, acc, key); p = unsafe { (*p).children[s] }.map_addr(|a| a & !0b111); }
    black_box(acc); black_box(p);
    t.elapsed().as_nanos() as f64 / hops as f64
}

fn build_idx<T: Copy>(n: usize, mk: impl Fn(IdxN4) -> T) -> Vec<T> {
    let next = perm(n, 1);
    (0..n).map(|i| { let (num, plen, prefix, keys) = hdr(i);
        let tagged = ((next[i] as u32) << TAG_BITS) | 0; // tag 0 = Node4
        mk(IdxN4 { num, plen, prefix, keys, children: [tagged; 4] }) }).collect()
}

/// Contiguous per-type slab. `bases[tag]` lookup models dispatching by type tag.
fn run_idx<T: Copy>(n: usize, hops: usize, mk: impl Fn(IdxN4) -> T, get: fn(&T) -> &IdxN4, via_table: bool) -> f64 {
    let v = build_idx(n, mk);
    let bases: [*const T; 8] = [v.as_ptr(); 8];
    let bases = black_box(bases);
    let mut cur: u32 = 0; let mut acc = 0u64; let key = black_box(9usize);
    let t = Instant::now();
    for _ in 0..hops {
        let base = if via_table { unsafe { *bases.get_unchecked((cur & 7) as usize) } } else { bases[0] };
        let node = get(unsafe { &*base.add((cur >> TAG_BITS) as usize) });
        let s = hop_body!(node, acc, key);
        cur = node.children[s];
    }
    black_box(acc); black_box(cur);
    t.elapsed().as_nanos() as f64 / hops as f64
}

/// Chunked slab: stable addresses, chunk table lookup adds a dependent load.
fn run_idx_chunked(n: usize, hops: usize) -> f64 {
    let v = build_idx(n, |x| x);
    let chunk = 1usize << CHUNK_SHIFT;
    let mut chunks: Vec<Box<[IdxN4]>> = Vec::new();
    for c in v.chunks(chunk) { chunks.push(c.to_vec().into_boxed_slice()); }
    drop(v);
    let table: Vec<*const IdxN4> = chunks.iter().map(|c| c.as_ptr()).collect();
    let mut cur: u32 = 0; let mut acc = 0u64; let key = black_box(9usize);
    let t = Instant::now();
    for _ in 0..hops {
        let idx = (cur >> TAG_BITS) as usize;
        let node = unsafe { &*(*table.get_unchecked(idx >> CHUNK_SHIFT)).add(idx & (chunk - 1)) };
        let s = hop_body!(node, acc, key);
        cur = node.children[s];
    }
    black_box(acc); black_box(cur);
    t.elapsed().as_nanos() as f64 / hops as f64
}

fn best(f: impl Fn() -> f64) -> f64 { (0..3).map(|_| f()).fold(f64::MAX, f64::min) }

fn main() {
    assert_eq!(std::mem::size_of::<PtrN4>(), 64);
    assert_eq!(std::mem::size_of::<IdxN4>(), 44);
    println!("{:>10} {:>10} | {:>8} {:>8} {:>8} {:>8} {:>8} {:>8} {:>8}", "nodes", "ptr WS", "ptr64", "ptr64tag", "idx64", "idx44", "idx44tbl", "idx64al", "idx44chk");
    for log in [8, 10, 12, 14, 16, 18, 20, 22, 24] {
        let n = 1usize << log;
        let hops = 20_000_000;
        let ws = n * 64;
        let r = [
            best(|| run_ptr(n, hops)),
            best(|| run_ptr_tagged(n, hops)),
            best(|| run_idx(n, hops, |x| IdxN4Same { n: x, _pad: [0; 20] }, |t| &t.n, false)),
            best(|| run_idx(n, hops, |x| x, |t| t, false)),
            best(|| run_idx(n, hops, |x| x, |t| t, true)),
            best(|| run_idx(n, hops, |x| IdxN4Pad { n: x }, |t| &t.n, false)),
            best(|| run_idx_chunked(n, hops)),
        ];
        println!("{:>10} {:>9}K | {:>8.2} {:>8.2} {:>8.2} {:>8.2} {:>8.2} {:>8.2} {:>8.2}", n, ws / 1024, r[0], r[1], r[2], r[3], r[4], r[5], r[6]);
    }
}
