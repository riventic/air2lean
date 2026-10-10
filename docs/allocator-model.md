# Allocator model: `std` or `translated`

`air2lean --allocator-model std|translated` (also `--allocator-model=…`, and in
`--diagnostics-json` mode) selects how `std.mem.Allocator` is translated. The default is
`std`: its output is byte-identical to a run without the flag.

| | `std` (default) | `translated` |
|---|---|---|
| `std.mem.Allocator` | the model's `Zig.Allocator` (`Ty.allocator`, no fields) | the ordinary struct `{ptr: *anyopaque, vtable: *const VTable}` |
| `mem.Allocator.alloc`/`free`/`create`/… | built-in `StdModels` rows ([std-models.md](std-models.md)) | translated from their AIR, like user code |
| vtable calls (`a.vtable.alloc(…)`) | not reached | ordinary indirect calls through a function pointer ([generated-code.md](generated-code.md#casts-layout-and-function-pointers)) |
| allocator implementations (`std.heap.*`) | not translated | translated from their AIR |
| trusted boundary | the allocator model (ALC-01…07) | `posix.mmap`/`munmap`/`mremap` only (OSM-01) |

The `translated` mode is the base of the allocator proofs that derive every allocator,
user-written ones included, from the operating system's page mapping instead of from a
hand-written model per allocator. It requires Zig 0.16.0 for the OS boundary.

## The trusted OS boundary

`posix.mmap`, `posix.munmap` and `posix.mremap` are built-in rows of `Air2Lean/StdModels.lean`
that are active only in translated mode. A call is checked against the exact 0.16.0 signature
(`Check.lean`'s `checkOsCall`) and emitted as a call of `ZigLean/Os/Mmap.lean`:

```lean
Zig.Os.mmap   : Target → Option Ptr → BitVec 64 → BitVec 32 → BitVec 32 → BitVec 32 → BitVec 64 → MemM (Except ErrName Slice)
Zig.Os.munmap : Target → Slice → MemM Unit
Zig.Os.mremap : Target → Option Ptr → BitVec 64 → BitVec 64 → BitVec 32 → Option Ptr → MemM (Except ErrName Slice)
```

`Target` (`linux`, `macos`) comes from the profile's target triple; the page size is
`Target.pageSize` (4096, 16384) and every page pointer must have that alignment. The packed
`prot`/`flags` structs are passed as their bits (`Zig.Packed.toBits`) in the OS's own layout.
The model may return only `error.OutOfMemory`; the checker requires every call site's error
set to admit it. `mremap` is Linux-only (`std.posix.MREMAP` is `void` on macOS). The call graph
is cut there, above the syscall (Linux) and libc (macOS) layers, so their inline assembly and
`extern` functions are never translated. A translated AIR file named `posix.mmap` is rejected
as a conflict with the built-in row. The definitions are the page-mapping model of premise
[OSM-01](premises.md#osm-01) ([os-mmap.md](os-mmap.md)); its separation-logic rules are in
`ZigLean/Sep/Mmap.lean`.

## What translated mode admits

Each admission below is limited to `--allocator-model translated`; std mode keeps the
original rejection.

- **`@returnAddress()`** (`ret_addr`, marked unsupported by the exporter) is
  `Zig.returnAddress`: the next value of the explicit oracle `Mem.arbitrary` (query `k` gives
  `arbitrary[k]`, `0` past the end). A theorem over every initial memory therefore covers every
  sequence of return addresses. Allocators only pass the value along. The result must be a
  `usize`.
- **Integer pointer constants** (`@ptrFromInt(c)` at comptime, the exporter's
  `{"unsupported": "int", "off": c}`): a pointer without a block, `⟨none, c⟩`, so every access
  through it is `.illegal`. This is the zero-length allocation sentinel of
  `mem.Allocator.allocBytesWithAlignment` (`alignment.backward(maxInt(usize))`). Only a
  single/many-item, non-volatile, non-sentinel pointer with a nonzero address its alignment
  divides is admitted; every other integer pointer constant is rejected.
- **An `undefined` single/many-item pointer operand** (`std.heap.page_allocator` is
  `.{ .ptr = undefined, .vtable = … }`) is `Zig.undefPtr`: a pointer without a block at an
  arbitrary address from the same oracle. Other `undefined` operands stay rejected.
- **`*anyopaque` casts.** Erasing a pointer to `*anyopaque` is admitted; recovering `*T` from
  `*anyopaque` (an allocator's `ctx`) requires `T` to be provably free of error storage, as
  for a pointer recovered from an integer.
- **`unordered` atomic loads** of integers and pointers (`ZigLean/Conc/AtomicWord.lean`): the
  load reads any message not older than the newest one that happened before it. It neither
  uses nor updates the thread's own read view, so it admits every outcome of a `monotonic`
  load and more. `unordered` stores stay rejected.
- **Pointer-valued atomics** (`PageAllocator`'s address hint) are the thread model's pointer
  atomics, the same in both modes (`ZigLean/Mem/AtomicPtr.lean`, C09): messages keep the
  pointer's bytes and provenance, and a compare-exchange compares identities (`.unspecified`
  when identity and address disagree). A function with an atomic op is concurrent
  (`Zig.ConcM`), and so is every caller, through the vtable included.

Two general fixes reached by the allocator code apply in both modes and change no committed
translation: a function type counts as error-free storage (a vtable of function pointers is a
plain global alias), and a field pointer into a tuple-typed local uses the `Prod` projections
(`snd`, `fst`).

## Exporter requirement

Earlier 0.16.0 exporters wrote `heap.*.vtable` without its initializer and
`mem.Allocator.VTable` as `no_fields` in some files, which the translator rejects
(`global has no initial value`, `inconsistent shared type 'mem.Allocator'`). The current
exporter resolves both (`Compat.ensureNavVal`, `Compat.ensureLayout` in
`zig-patch/air-json/json.zig`, [air-json.md](air-json.md)); the regression fixtures were
exported with it (`provenance.json`).

## Regression and scope

[`tests/roadmap/alloc-translated`](../tests/roadmap/alloc-translated/README.md) translates
`page_allocator` and `FixedBufferAllocator` clients (alloc, free, create, destroy, resize,
reset) for x86_64-linux and aarch64-macos, elaborates them, evaluates the
`FixedBufferAllocator` clients against the native results, and checks the negative cases.

Outside this milestone (the arena milestone), measured on the 0.16.0 `ArenaAllocator` export:

- Header/bytes punning: `Node.allocatedSliceUnsafe`, `beginResize`, `loadBuf`, `reset`, `alloc`,
  `free`, `resize` cast between `*Node` and the buffer bytes (`a pointer cast has unresolved or
  cyclic symbolic storage provenance`).
- `ctx` recovery of the arena state: its type reaches the cyclic `Node` list, so error-freedom
  is not provable (`recovering a symbolic error pointer from an integer or opaque value…`).
- Lock-free atomics: an `unordered` load of the packed `Node.Size` (`endResize`) and pointer
  atomic stores/RMWs in `pushFreeList`/`stealFreeList` stay rejected.

## Removing the hand-written allocator models (plan)

Allocator milestone 1 proves the translated `FixedBufferAllocator` (`tests/roadmap/alloc-fba`,
`FBA.allocSpec`, `FBA.fallocSpec`) and the translated `PageAllocator`
(`tests/roadmap/alloc-translated`: `free`/`resize`/`remap` on x86_64-linux and aarch64-macos,
`alloc` on x86_64-linux for every alignment, partial correctness) against the generic
specification ([alloc-spec.md](alloc-spec.md), [alloc-page.md](alloc-page.md)), from their Zig
code down to `posix.mmap`/`munmap`/`mremap` (OSM-01). The `std` mode still carries the
hand-written models below. They are not removed in milestone 1; each step removes one only after
the translated mode covers every claim that rests on it, so no theorem disappears without a
translated replacement or a register entry (`ROADMAP.md`, `docs/remaining-acceptance.md`).

| Legacy model | Where | Premise | Users |
|---|---|---|---|
| L1 fixed buffer: `OwnedPolicy.fixedBuffer`, `OwnedAlloc.used`/`starts` | `ZigLean/Mem/Owned.lean`, `ZigLean/Sep/Owned.lean` | ALC-07 | `tests/roadmap/allocator-identity`, `ZigLean/Witnesses/Sep.lean` §Owned |
| L2 arena and identities: `OwnedPolicy.arena`, `AllocRef.owned`, `BlockKind.owned`, `Mem.allocators` | `ZigLean/Mem/Owned.lean`, `ZigLean/Sep/ArenaClient.lean` | ALC-07 | `tests/roadmap/allocator-identity`, `tests/roadmap/address-reuse/Check.lean` |
| L3 remap/realloc policy variants: `AllocPolicy.byteRemap` (`ByteRemapMode.fail`/`inPlace`/`move`), sentinel realloc | `ZigLean/Mem/Alloc.lean`, `ZigLean/Sep/RawAlloc.lean`, `ZigLean/Sep/Remap.lean`, `ZigLean/Sep/SentinelRealloc.lean` | ALC-03, ALC-05 | `tests/roadmap/resize-remap`, `tests/roadmap/sentinel-realloc`, `tests/roadmap/architecture-audit/models` |
| L4 the std allocator: `Zig.Allocator`, `rawAlloc`/`rawFree`, the `mem.Allocator.*` rows of `Air2Lean/StdModels.lean`, `BlockKind.heap` | `ZigLean/Mem/Alloc.lean`, `ZigLean/Sep/Alloc.lean`, `ZigLean/Sep/Sentinel.lean` | ALC-01, ALC-02, ALC-04, ALC-06, ALC-09 | every std-mode proof that allocates (`Proofs/Lists`, `Proofs/Slices`, …), `tests/roadmap/allocation-policy` |

Steps, one PR each, in this order:

1. **FBA client port** (prerequisite of L1). Lift the client proofs that use the fixed-buffer
   model onto `FBA.fallocSpec` through the generated wrappers (`ZigLean/Sep/Full/Wrappers.lean`).
   Blocker: `tame` does not see through the `StateT.run (match …)` that `gen_norm` leaves in the
   generated wrappers (one matcher per generated `match`); it needs a `StateT`-level `Tame` rule
   or a split-then-renormalize step. Then delete `OwnedPolicy.fixedBuffer`, `OwnedAlloc.used`,
   `OwnedAlloc.starts`, their `Owned.lean`/`Sep/Owned.lean` cases and the fixed-buffer cases of
   `tests/roadmap/allocator-identity`; narrow ALC-07 to the arena.
2. **Translated `ArenaAllocator`** (prerequisite of L2), the arena milestone: the three blockers
   listed under "Regression and scope" (header/bytes punning, the cyclic `Node` type behind
   `ctx`, the lock-free atomics). Then delete `OwnedPolicy`, `OwnedAlloc`, `AllocRef.owned`,
   `BlockKind.owned`, `Mem.allocators`, `ZigLean/Sep/ArenaClient.lean` and ALC-07; rewrite the
   owned-allocator cases of `tests/roadmap/address-reuse/Check.lean` over the translated arena.
3. **Client contract over `FAllocSpec`** (prerequisite of L3 and L4). A function that takes a
   `std.mem.Allocator` is proved for every allocator that satisfies `FAllocSpec` (in place of
   ALC-09, "the caller's allocator behaves as the std model"); `FAllocSpec.toLegacy` already
   gives the legacy-logic wrappers. Re-prove the std-mode allocation corpora (`Proofs/Lists`,
   `Proofs/Slices`, sentinel and realloc fixtures) in translated mode against it, and make
   `--allocator-model translated` the default for every Zig version whose `posix.zig` is
   reviewed (0.16.0 now; 0.17.0 after its review of the three `posix` rows).
4. **Remap and realloc behaviour from code** (L3). With step 3, `resize`/`remap`/`realloc`
   behaviour comes from the translated allocator (`PageAllocator`'s `mremap`, the fixed buffer's
   last-allocation growth), so delete `AllocPolicy.byteRemap`, `ByteRemapMode`, the byte remap
   and sentinel realloc models and ALC-03/ALC-05; port `tests/roadmap/resize-remap` and
   `tests/roadmap/sentinel-realloc` to translated mode.
5. **The std allocator** (L4). Delete `Zig.Allocator`, `rawAlloc`/`rawFree`, the
   `mem.Allocator.*` std-model rows, `--allocator-model std` for allocators and ALC-01, ALC-02,
   ALC-04, ALC-06, ALC-09. The failure decision (`failAt`, `failures`, `maxBytes`, the oracle
   `fails`, `budget`, `Mem.allocs`) stays only as the OS-level decision of `mmap`/`mremap`
   (`Mem.mapDenied`, OSM-01); `tests/roadmap/allocation-policy` moves to it.

Each step regenerates the premise index, coverage and the theorem inventory, and records the
removed CI steps and the translated replacements in the register.
