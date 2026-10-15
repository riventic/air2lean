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

| Target | Page size | `addrLimit` | `PROT.READ\|WRITE` | `MAP.PRIVATE\|ANONYMOUS` | `mremap` |
|---|---|---|---|---|---|
| `Os.Target.linux` (x86_64-linux) | 4096 | `2^47` | `3` | `0x22` | yes |
| `Os.Target.macos` (aarch64-macos) | 16384 | `0x7FFFFE000000` | `3` | `0x1002` | no (`posix.MREMAP == void`) |

`addrLimit` is the end of the user address space: no mapping ends above it (`Os.Target.fits`).
On x86_64-linux user space ends at `TASK_SIZE_MAX`, a page below `2^47` (4-level paging; with
5-level paging the kernel maps above 47 bits for a hint above `TASK_SIZE_MAX`
(`DEFAULT_MAP_WINDOW`), `2^47` itself included, which the premise assumes no call passes). On
aarch64-macos it ends at `MACH_VM_MAX_ADDRESS` (`0x00007FFFFE000000`, 128 TiB - 32 MiB,
`mach/arm/vm_param.h` of the macOS SDK). Each is at least the kernel's bound, so the bound
excludes no kernel address (the placement's other limits still do: the model never reuses the
unmapped prefix of a partly live mapping, below). Both are far below `2^64 - 2^63`, so adding
an alignment `2^k - 1` (`k < 64`) to an address inside a mapping does not overflow.

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
placement's address for its pages (`Mem.mapAddr`: `Mem.newAddr` of `alignUp length page` bytes
with page alignment, [address-placement.md](address-placement.md)). A proposed address is taken
when it is page-aligned, nonzero, its pages end at or below 2^64 and are clear of every live
block, so a later mapping may reuse an unmapped range, as the kernel does. Otherwise the mapping
goes after every block (`Mem.top`). Either way, a mapping whose pages would end above
`addrLimit` fails with `error.OutOfMemory` (one attempt, no block): the kernel never maps there.
The live range of a block for that check is its live bytes, from its first live offset on
(`Block.clearOf`, `BlockKind.mappedLo`): the unmapped prefix of a mapping that is still partly
live is free address space again, and a later block may be placed there, as the kernel may do
(the `map` path for alignments above a page, proved in `PageAlloc.lean`, unmaps such a prefix).
A thread's stack cut off its mapping by `clone` is such a prefix while the thread runs
(MM-19, [os-threads.md](os-threads.md)); the stack reserves keep every other placement out of it.

## munmap

A mapping is a block of kind `.mapped lo`: its live bytes are the offsets from `lo` to its
byte count `hi`. `munmap(memory)` must name a page-aligned start inside one live mapping and
`len > 0`; the range ends at `off + alignUp len page` (the kernel rounds the length up), and
the mapping's end counts as `lo + alignUp (hi - lo) page`. Then:

- the whole mapping: the block ends (every later access is `.illegal`);
- a prefix (`off = lo`, ending before the mapping's end): `lo` moves to the range's end; an
  access below it is `.illegal` (`Mem.access` checks `BlockKind.mappedLo`), and the released
  range is free address space (`Os.unmapCase_prefix_ge`);
- a tail (from `off > lo` to the mapping's end): the bytes end at `off`.

Anything else is `.illegal`: a range in the middle (Zig's `munmap` rejects it too), a range
past the mapping, a misaligned start, a pointer that is not into a live mapping — a double
`munmap`, a heap or stack block, an integer address. The kernel accepts some of these
(unmapping nothing, or pages of another mapping); the model is stricter, so a proof of their
absence is stronger. The removed bytes are recorded as a write for the race check, and the
atomic locations over them are retired with their messages (`Mem.retire`): bytes that a later
growth in place maps again start without an atomic location, as a new mapping's do.

## mremap

Only on Linux. `flags` must be `0` or `MAYMOVE` and `new_address` null; `FIXED`/`DONTUNMAP`
are `.unspecified`, as is any call on macOS.
`old_address`/`old_len` must name a whole live mapping, else `.illegal`. Then
(`Os.mremapLive`):

- `new_len = 0` (`EINVAL`): outside the model, `.unspecified` (the allocator wrappers never
  pass it);
- a shrink: in place, the bytes end at `lo + new_len`; the cut bytes are recorded as a write and
  the atomic locations over them are retired (`Mem.retire`), as for `munmap`;
- a growth is an allocation attempt. The failure decision fails it with `error.OutOfMemory`.
  There is room in place when the grown pages `[A + lo, A + lo + alignUp new_len page)` end
  at or below `addrLimit` and are clear of every other live block (`Mem.mappingRoom`). Under
  `MAYMOVE` it moves to a new mapping at the placement's address (`Mem.mapAddr`, chosen while
  the old mapping is still mapped) when the oracle `AllocPolicy.os.mremapMoves` says so or
  when there is no room; the live bytes are copied and the old block ends. Otherwise it grows
  in place if there is room, else returns `error.OutOfMemory` (`ENOMEM`). A move whose pages
  would end above `addrLimit` returns `error.OutOfMemory` too.
  The grown bytes up to the old length's page end are undefined (the kernel keeps the stale
  tail of the last page), the rest are zero (`mremapFill`). A growth in place forgets the
  recorded accesses to the grown offsets (`Mem.forgetFrom`): the grown bytes start with no access
  history, as a new mapping's do, so an access from before an earlier unmap of those pages (by
  any thread) races with no access to the new ones.

## Rules (`ZigLean/Sep/Full/Mmap.lean`, proof-only)

The full-state rules of the calls, with block extents (`docs/sep-full-state.md` §Block extents),
proved on `Holds` from the runs of the calls. The module is not imported by `ZigLean.lean`; build
it with `lake build ZigLean.Sep.Full.Mmap`.

| Theorem | Statement |
|---|---|
| `FTotalTriple.mmap'`, `FTotalTriple.mmapC` | `emp` before; after, `fmmapPost`: `length` zero bytes at offset 0 of a new mapping with its full extent and `s.len = length`, whose block address `A` has `A + alignUp length page ≤ addrLimit`, or `error.OutOfMemory` and nothing. For every failure policy. |
| `FTotalTriple.munmapWhole'` | the whole mapping (its bytes and full extent) before, `emp` after. |
| `FTotalTriple.munmapPrefix'`, `FTotalTriple.munmapTail'`, `FTotalTriple.munmapTailR` | the extent and the unmapped pages' bytes before; the kept bytes stay with their owner, and the live start (prefix) or the end (tail) moves. |
| `FTotalTriple.mremapShrink'`, `FTotalTriple.mremapShrinkR` | the extent and the cut bytes before; the same pointer returned. |
| `FTotalTriple.mremapGrow'`, `FTotalTriple.mremapMove'`, `FTotalTriple.mremapMoveC` | growth in place from the extent alone, or a move with every byte of the mapping: the new mapping at the returned pointer, or `error.OutOfMemory` with the old one. |

The facts about runs (`ZigLean/Os/MmapRun.lean`, which no program logic depends on): the runs of
the calls that every rule uses (`Os.mmap_run`, `Os.munmap_run`, `Os.mremap_eq`,
`Os.mremapLive_shrink`, `Os.mremapLive_grow`), the `unmapCase` of a whole mapping, a prefix and
a tail, the page arithmetic and `mapDenied_iff` (the failure decision is `Mem.allocDenied`), and

| Theorem | Statement |
|---|---|
| `Os.munmap_whole_then_illegal` | after a whole `munmap`, every access to the block and a second `munmap` throw `.illegal`. |
| `Os.munmap_prefix_access_illegal`, `Os.munmap_tail_access_illegal` | after a trim, every access that reaches an unmapped byte throws `.illegal`. |
| `Os.munmap_dead`, `access_illegal` | `munmap` of a dead block, and an access below `lo`, past the bytes or into a dead block, throw `.illegal`. |

`tests/roadmap/os-mmap/Check.lean` checks use after `munmap`, a double `munmap` and the `munmap`
of a middle range on concrete runs in the kernel.

The `MmapExamples` section checks concrete runs with the `linux` target in the
kernel (`decide`): a store into a fresh mapping, use after `munmap`, double `munmap`, and a
middle-range `munmap`.

Runtime regressions of every rule and its negative cases: `tests/roadmap/os-mmap/Check.lean`
(`lake env lean tests/roadmap/os-mmap/Check.lean`).

## Full-state rules (`ZigLean/Sep/Full/Mmap.lean`)

Over full-state resources with block extents (`docs/sep-full-state.md` §Block extents), a step
that changes a mapping's size or live start needs the mapping's full extent `bext` and only the
bytes it releases; the bytes that stay live may be anyone's. `FTotalTriple.munmapTail'` and
`munmapPrefix'` (the unmapped pages' bytes) and `mremapShrink'` (the cut bytes) are proved from
the general step `Holds.reblock`; `mremapGrow'` (growth in place without `MAYMOVE`; the new bytes
go to the caller) needs only the authority over the extent with any fraction (`Holds.grow`). A
whole mapping needs every byte of it and uses the block steps of `ZigLean/Sep/Full/Block.lean`:
`FTotalTriple.mmap'` pushes a new live block (`Holds.push`), `munmapWhole'` ends one
(`Holds.free` from its live bytes `[lo, S)` and its extent), and `mremapMove'` (a growth that may
move) ends the old block and pushes the grown copy, or grows in place as `mremapGrow'` with the
old bytes framed and relabelled to the new size (`EUpd.relabel`). No rule lifts a legacy triple.

## Effect on the existing memory model

`BlockKind` has the new kind `.mapped lo`; `Mem.access` and `Mem.heap` exclude offsets below
`BlockKind.mappedLo`, which is 0 for every other kind. Lemmas that build a permission or an
access from a block's offset 0 (`access_of`, `Mem.heap_split`, `alloc_run`, `Triple.alloc`,
the byte-remap frame lemmas) take the fact `blk.kind.mappedLo = 0` (or `≤ off`), discharged
automatically for every non-mapped kind. The lock and word invariants of `ZigLean/Conc`
(`Lock.Inv.blk`, `Word.Ok.blk`) state it for their block.
