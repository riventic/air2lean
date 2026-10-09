# Allocator identity, arenas and fixed buffers (M01)

`ZigLean/Mem/Owned.lean` adds allocators with an identity to the heap model. Allocator `a`
is `Mem.allocators[a]` (an `OwnedAlloc`: policy, liveness, fixed-buffer `end_index`). The
kind of a block records its owner: `.heap` is the model's `std.mem.Allocator`
(`ZigLean/Mem/Alloc.lean`, unchanged), `.owned a` is allocator `a`. `AllocRef` (`.std` or
`.owned a`) gives the `std.mem.Allocator` calls (`create`, `destroy`, `alloc`, `free`,
`remap`) for either.

Owned blocks get fresh model addresses by default. The opt-in address-reuse policy (M05,
[address-reuse.md](address-reuse.md)) may give a new owned block the address of a freed or reset
one; block ids, and so every ownership and liveness check, are unaffected.

## Semantics

The policies follow the Zig 0.16.0 sources `lib/std/heap/ArenaAllocator.zig` and
`lib/std/heap/FixedBufferAllocator.zig`.

| Operation | Model |
| --- | --- |
| `ArenaAllocator.init(child)` | `Arena.init`: a new id; no block. |
| arena `alloc` | a new `.owned a` block; one attempt of `Mem.allocPolicy`/`failAt` (every arena request may fail; Zig asks the child only for a new node). |
| arena `free` | the block must be a whole live `.owned a` block, else `.illegal`; its lifetime ends. Zig gives the bytes back only for the last allocation; the arena model has no capacity, so nothing else changes. |
| `arena.reset(mode)` | `Owned.reset`: every `.owned a` block dies, no other block changes. The boolean result (a capacity hint for the retaining modes) is not modelled. |
| `arena.deinit()` | `Arena.deinit`: reset, then the arena is dead; later use throws `.illegal`. |
| `FixedBufferAllocator.init(buf)` | `FixedBuffer.init base cap`: `end_index = 0`. |
| fixed-buffer `alloc` | Zig's `alignPointerOffset` from `base + end_index`; `none` (`OutOfMemory`) if it does not fit, without a policy decision. |
| fixed-buffer `free` | ownership check as for arenas; `end_index -= len` exactly when the block is the last allocation (`isLastAllocation`), else no bytes come back. |
| fixed-buffer `reset()` | `Owned.reset`: every block dies, `end_index = 0`. |
| `remap` | ownership check first; same or smaller length succeeds in place (a fixed buffer gives the tail back for its last allocation); growth fails. |

A free, destroy or remap through allocator `r` of a block of another kind throws `.illegal`
(`AllocRef.free_foreign`, `destroy_foreign`, `remap_foreign` in `ZigLean/Sep/Owned.lean`):
an arena's block through `std.mem.Allocator` or another arena, a `std.mem.Allocator` block
through an arena, a stack or global block through any allocator. The existing
`Allocator.free`/`destroy` already required `.heap`; `AllocRef.remap .std` adds the check that
the failing default `Allocator.remap` omits.

## Theorems

* `Mem.heap_resetOwned`: after a reset of `a` the heap is the old heap without exactly the
  cells of `a`'s blocks (`Heap.dropOwned`). `Mem.resetOwned_own`/`_other` and
  `Mem.resetOwned_access_own`/`_other` state the invalidation and the frame separately;
  `Owned.reset_spec` and `Arena.deinit_spec` give the runs and keep `Mem.Seq`.
* `ZigLean/Sep/ArenaClient.lean`: a request-scoped arena server. Each request copies its
  fields into the arena (`dupe`), reads them back for a checksum and resets the arena on both
  outcomes; a session opens one arena and deinitializes it. `session_spec`: for every memory
  with `Mem.Seq`, every failure policy and every request list, the run returns one outcome per
  request (its checksum or `error.OutOfMemory`), never throws, and leaves the initial heap
  without the session arena's blocks; `session_restores`: the initial heap exactly when no
  block already claims the new id.

## Limits

* The translator does not route `std.heap.ArenaAllocator`/`FixedBufferAllocator` calls:
  translated programs still use one `std.mem.Allocator` and their `heap.*` calls stay
  rejected. A generated `Allocator` value carries no identity, so this model is for
  hand-written clients and specifications until the vtable is modelled.
* Owned blocks get fresh model addresses, not addresses inside the fixed buffer or the arena's
  nodes; address-sensitive programs are M05.
* Growing remap of the last allocation fails in the model; Zig grows it in place when it fits
  (M02).
* `reset`/`deinit` record no race-check access; Zig's are not thread-safe either, and the
  theorems assume `Mem.Seq` (one thread).
* Custom allocators with other policies are not modelled; E01 external contracts remain the
  route for them.

Checks: `bash tests/roadmap/allocator-identity/check.sh` builds the modules, prints the
axioms of the acceptance theorems (rejecting `sorryAx`) and runs the executable regressions
(cross-allocator frees, double free, reset frame, deinit, fixed-buffer LIFO and a session
with policy failures).
