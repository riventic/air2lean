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
