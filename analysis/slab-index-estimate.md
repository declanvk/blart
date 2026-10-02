# Estimate: 32-bit slab indices in place of 64-bit node pointers

Hypothetical design: allocate each node type (including leaves) from its own
slab, and shrink `OpaqueNodePtr` from 64 bits to 32 bits (3 type-tag bits + 29
bits of slab index).

Measured on `main` @ 1b33e91 (24-byte header, `PREFIX_LEN = 16`, no Node32),
Apple M4 Max (128 KiB L1d, 16 MiB L2, 128-byte cache lines).

## Capacity

- 6 node types (Node4/16/32/48/256 + Leaf) need 3 tag bits, leaving 29 bits of
  index, so each slab holds up to 2^29 = 536,870,912 nodes.
- Every inner node has at least 2 children (`src/raw/operations/delete.rs`
  collapses single-child nodes), so `inner nodes <= leaves - 1`. The leaf slab
  is always the binding limit.
- **Max capacity: 2^29 ≈ 537M keys**, whatever the node mix.
- **All-Node4, worst case:** every Node4 has 2 children, so 2^29 leaves need
  2^29 - 1 Node4s, which still fits. Capacity is still ≈ 537M keys.
- Using 1 bit for leaf/inner (with the inner type kept in the node header) would
  give leaves 31 bits (≈ 2.1B).
- Store indices, not byte offsets: a byte offset caps each slab at 4 GiB.

## Memory

Projected node sizes with 4-byte child slots: Node4 64 → 44, Node16 168 → 104,
Node48 664 → 472, Node256 2072 → 1048. Leaves lose 8 bytes from their prev/next
links.

| Dataset | Avg inner depth | Inner bytes/key | Total bytes/key |
|---|---|---|---|
| dict.txt (370K words) | 7.5 | 40.2 → 27.1 (−33%) | 80.2 → 59.1 (−26%) |
| random u64 ×1M | 3.1 | 23.6 → 15.9 (−33%) | 55.6 → 39.9 (−28%) |
| random u64 ×10M | 3.5 | 26.7 → 15.9 (−41%) | 58.7 → 39.9 (−32%) |
| sequential u64 ×10M | 3.0 | 8.1 → 4.1 (−49%) | 40.1 → 28.1 (−30%) |
| all-binary Node4 (depth 20) | 20 | 64 → 44 (−31%) | 112 → 84 (−25%) |

These figures use `size_of`. A slab also avoids malloc's rounding to 16-byte
size classes (e.g. a 24-byte leaf only stays 24 bytes in a slab), so real
savings are slightly larger.

Reproduce with:

```sh
cargo run --release --features testing --example slab_estimate
```

## Cost per hop

A synthetic benchmark that follows a dependent chain of Node4-shaped nodes
(`analysis/slab-chase`, run with `cargo run --release` from that directory).
Each hop does a prefix read and a key scan, then follows a child slot.
Values are ns/hop.

| Working set | ptr + tag mask (today) | idx, 64B slot | idx, 44B slot | 44B, chunked slab |
|---|---|---|---|---|
| L1 (16–64K) | 3.3 | 3.8 (+0.45) | 4.2 (+0.9) | 4.7 (+1.4) |
| L2 (1–4M) | 9.5–10.7 | 9.9–11.2 | 10.8–11.5 | 11.6–12.3 |
| 16M (L2 edge) | 17.1 | 17.4 | **14.1** | 15.2 |
| 64M (ptr) / 44M (idx) | 65.3 | 65.9 | **42.1 (−36%)** | 43.7 |
| 256M–1G (DRAM) | 98–105 | 98–105 | 96–109 (±4%) | 96–111 |

- The cost is extra arithmetic, not an extra memory load. A chunked slab (stable
  addresses during growth) adds one dependent L1 load.
- Power-of-two slot sizes decode about twice as cheaply (shift instead of
  multiply).
- Looking up the slab base by type tag adds about 0.2 ns. The branch on node
  type already exists.
- Once every hop misses to DRAM, smaller nodes don't reduce latency. Unaligned
  44-byte nodes occasionally straddle a cache line (+4% at 1 GB).

## Measured `get` latency on `main`

| Dataset | Random order | Sorted order |
|---|---|---|
| medium-dict.txt (32K) | 66.6 ns | 35.9 ns |
| dict.txt (370K) | 130.3 ns | 43.8 ns |
| random u64 ×1M | 40.8 ns | 17.1 ns |
| random u64 ×10M | 72.0 ns | 37.5 ns |
| sequential u64 ×10M | 31.1 ns | 7.2 ns |

## Estimated impact by operation

| Operation | Hot tree (fits in cache) | Tree near LLC size | Tree far bigger than cache |
|---|---|---|---|
| `get` / `contains` / `entry` lookup | +5–17% (≈ hops × 0.45–0.9 ns). Upper bound +25–50% for tiny shallow lookups like sequential u64 at 7 ns/op. | −10 to −35% | About neutral |
| Iteration / range scans | +0.5–1 ns per element | Gain | Gain if leaves are allocated in key order, else neutral |
| `insert` / `remove` | Probably faster: free-list pop/push is a few ns vs 15–20 ns for macOS malloc/free per node | Same | Same |
| `clone` | Much faster: indices don't depend on where the slab lives, so slabs can be memcpy'd and only the keys/values cloned | | |
| Drop | Much faster: free each slab in one call, though keys/values still need dropping | | |

Lookup estimates are hop count × measured per-hop overhead, not a prototype.
The "near LLC" gain depends heavily on the hardware's cache sizes.

## Design costs

- **Memory isn't returned on delete.** Free slots are only reused by the same
  node type, so a slab stays at its high-water mark until compacted.
- **Growth policy is a tradeoff.** Growing a contiguous `Vec` copies the whole
  slab on reallocation (a long pause at GB scale). Chunked slabs avoid the copy
  at about +0.5 ns/hop. Reserving a large virtual range up front avoids both but
  isn't portable.
- **Internal refactor.** Every raw-layer function that turns a child pointer into
  a node reference needs the arena passed in. Iterators, cursors and `Entry`
  already borrow or own the `TreeMap`, so they reach the slabs that way, with no
  public signature change.
- **Narrow public API break.** The raw round-trip hands an `OpaqueNodePtr` to
  the user: `TreeMap::into_raw`, `into_raw_with_allocator`, `from_raw*`, and the
  crate-root `OpaqueNodePtr` re-export. A root index means nothing without the
  slabs, so these would need to carry them, e.g. via an opaque
  `RawTree { root, slabs, alloc }`. The rest of `raw` is only public behind the
  `_internal` feature.

## Next step

Prototype only a Node4 slab and measure with the existing callgrind and
criterion `dict_get` benches.
