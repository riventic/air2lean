# OS page mappings: the trusted base of allocator proofs (OSM-01)

Allocators are not modelled one by one. `std.heap.PageAllocator`, the arenas, the debug
allocator and user-written allocators are translated from their Zig code and proved from
three OS calls. Only these calls get a trusted model, premise
[OSM-01](premises.md#osm-01):

| Zig 0.16.0 (`lib/std/posix.zig`) | Model (`ZigLean/Os/Mmap.lean`) |
|---|---|
| `mmap(ptr: ?[*]align(page_size_min) u8, length: usize, prot: PROT, flags: MAP, fd: fd_t, offset: u64) MMapError![]align(page_size_min) u8` | `Zig.Os.mmap (target : Os.Target) (hint : Option Ptr) (len : BitVec 64) (prot flags : BitVec 32) (fd : BitVec 32) (offset : BitVec 64) : MemM (Except ErrName Slice)` |
| `munmap(memory: []align(page_size_min) const u8) void` | `Zig.Os.munmap (target : Os.Target) (memory : Slice) : MemM Unit` |
| `mremap(old_address: ?[*]align(page_size_min) u8, old_len: usize, new_len: usize, flags: MREMAP, new_address: ?[*]align(page_size_min) u8) MRemapError![]align(page_size_min) u8` (Linux) | `Zig.Os.mremap (target : Os.Target) (old : Option Ptr) (oldLen newLen : BitVec 64) (flags : BitVec 32) (newAddress : Option Ptr) : MemM (Except ErrName Slice)` |

Under `--allocator-model translated` ([allocator-model.md](allocator-model.md)) the translator
emits these calls for `std.posix.mmap`/`munmap`/`mremap`. `PROT`, `MAP` and `MREMAP` are
`packed struct(u32)`s; the model takes their bits (`Zig.Packed.toBits`). `fd_t` is `i32`.
`mremap` returns a slice (`[0..new_len]`), not a many-pointer. The only error the model
returns is `error.OutOfMemory`; the translator checks that each call site's error set admits it.

## Targets

`Os.Target` fixes the page size (`std.heap.pageSize()`, comptime in Zig 0.16.0 for both
modelled targets) and the flag encodings:

| Target | Page size | `PROT.READ\|WRITE` | `MAP.PRIVATE\|ANONYMOUS` | `mremap` |
|---|---|---|---|---|
| `Os.Target.linux` (x86_64-linux) | 4096 | `3` | `0x22` | yes |
| `Os.Target.macos` (aarch64-macos) | 16384 | `3` | `0x1002` | no (`posix.MREMAP == void`) |

`Os.noFd` is `-1`, `Os.mremapMayMove` is `MREMAP{ .MAYMOVE = true }` (`1`).

## mmap

Only an anonymous, private, read-write mapping is modelled: `prot = READ|WRITE`,
`flags = PRIVATE|ANONYMOUS` in the profile's encoding, `fd = -1`, `offset = 0`. Every other
combination throws `.unspecified` (outside the model). The hint is ignored: without
`MAP.FIXED` the kernel may ignore it. `length = 0` is `EINVAL`, which Zig maps to
`unreachable`: `.illegal`.

Otherwise the call is one allocation attempt, numbered by `Mem.allocs` like every
`std.mem.Allocator` request. The failure decision is the existing allocator one
(`Mem.mapDenied`, equal to `Mem.allocDenied`: `failAt`, `failures`, `maxBytes`, the oracle
`fails`, `budget`; `mapDenied_iff`; the budget counts the live `.heap` bytes plus the
request). A failure returns `error.OutOfMemory` (`ENOMEM`) and changes nothing but the attempt
count. The premise assumes the kernel fails such a mapping with no other `MMapError` member:
the process locks no memory (no `EAGAIN`). A success is a new block of kind `.mapped 0` with exactly `length` zero bytes at the
next page-aligned address; the next block starts above the mapping's last page. Addresses are
fresh: a later mapping never reuses an unmapped range (address reuse is not on `main` yet).

## munmap

A mapping is a block of kind `.mapped lo`: its live bytes are the offsets from `lo` to its
byte count `hi`. `munmap(memory)` must name a page-aligned start inside one live mapping and
`len > 0`; the range ends at `off + alignUp len page` (the kernel rounds the length up), and
the mapping's end counts as `lo + alignUp (hi - lo) page`. Then:

- the whole mapping: the block ends (every later access is `.illegal`);
- a prefix (`off = lo`, ending before the mapping's end): `lo` moves to the range's end; an
  access below it is `.illegal` (`Mem.access` checks `BlockKind.mappedLo`);
- a tail (from `off > lo` to the mapping's end): the bytes end at `off`.

Anything else is `.illegal`: a range in the middle (Zig's `munmap` rejects it too), a range
past the mapping, a misaligned start, a pointer that is not into a live mapping — a double
`munmap`, a heap or stack block, an integer address. The kernel accepts some of these
(unmapping nothing, or pages of another mapping); the model is stricter, so a proof of their
absence is stronger. The removed bytes are recorded as a write for the race check.

## mremap

Only on Linux. `flags` must be `0` or `MAYMOVE` and `new_address` null; `FIXED`/`DONTUNMAP`
are `.unspecified`, as is any call on macOS.
`old_address`/`old_len` must name a whole live mapping, else `.illegal`. Then
(`Os.mremapLive`):

- `new_len = 0` (`EINVAL`): outside the model, `.unspecified` (the allocator wrappers never
  pass it);
- a shrink: in place, the bytes end at `lo + new_len`;
- a growth is an allocation attempt. The failure decision fails it with `error.OutOfMemory`.
  Under `MAYMOVE` it moves to a fresh page-aligned
  block when the oracle `AllocPolicy.os.mremapMoves` says so or when another block lies
  above the mapping; the live bytes are copied and the old block ends. Otherwise it grows in
  place if no other block lies above the mapping, else returns `error.OutOfMemory` (`ENOMEM`).
  The grown bytes up to the old length's page end are undefined (the kernel keeps the stale
  tail of the last page), the rest are zero (`mremapFill`).

## Rules (`ZigLean/Sep/Mmap.lean`, proof-only)

`mapping P p A lo bs` owns the whole live range of a mapping: `bs` at `p = ⟨b, lo⟩`, block
address `A`, with `A` and `lo` page-aligned and `bs` nonempty. The module is not imported by
`ZigLean.lean`; build it with `lake build ZigLean.Sep.Mmap`.

| Theorem | Statement |
|---|---|
| `Triple.mmap` | `emp` before; after, `mmapPost`: a `mapping` of `length` zero bytes at offset 0 with `s.len = length`, or `error.OutOfMemory` and no bytes. For every failure policy. |
| `Triple.munmapWhole` | `mapping p A lo bs` before, `emp` after. |
| `Triple.munmapPrefix` | `mapping p A lo bs` before; after, `mapping (p.add k) A (lo + k) (bs.extract k)` with `k = alignUp len page`. |
| `Triple.munmapTail` | `munmap ⟨p.add k, len⟩` of a page tail: `mapping p A lo (bs.extract 0 k)` after. |
| `Triple.mremapShrink` | `mapping p A lo (bs.extract 0 newLen)` after, the same pointer returned. |
| `Triple.mremapGrow` | `mremapPost`: a `mapping` of `bs ++ mremapFill` at the returned pointer (in place or moved), or `error.OutOfMemory` with the old `mapping`. |
| `munmap_whole_then_illegal` | after a whole `munmap`, every access to the block and a second `munmap` throw `.illegal`. |
| `munmap_prefix_access_illegal`, `munmap_tail_access_illegal` | after a trim, every access that reaches an unmapped byte throws `.illegal`. |
| `Os.munmap_dead`, `access_illegal` | `munmap` of a dead block, and an access below `lo`, past the bytes or into a dead block, throw `.illegal`. |
| `mapDenied_iff` | the failure decision is `Mem.allocDenied`. |

The `MmapExamples` section checks concrete runs with the `linux` target in the
kernel (`decide`): a store into a fresh mapping, use after `munmap`, double `munmap`, and a
middle-range `munmap`.

Runtime regressions of every rule and its negative cases: `tests/roadmap/os-mmap/Check.lean`
(`lake env lean tests/roadmap/os-mmap/Check.lean`).

## Effect on the existing memory model

`BlockKind` has the new kind `.mapped lo`; `Mem.access` and `Mem.heap` exclude offsets below
`BlockKind.mappedLo`, which is 0 for every other kind. Lemmas that build a permission or an
access from a block's offset 0 (`access_of`, `Mem.heap_split`, `alloc_run`, `Triple.alloc`,
the byte-remap frame lemmas) take the fact `blk.kind.mappedLo = 0` (or `≤ off`), discharged
automatically for every non-mapped kind. The lock and word invariants of `ZigLean/Conc`
(`Lock.Inv.blk`, `Word.Ok.blk`) state it for their block.
