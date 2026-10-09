# `std.heap.PageAllocator` against `AllocSpec` (phase P4b): findings

Status: the translated `PageAllocator` (Zig 0.16.0, x86_64-linux and aarch64-macos, from
`posix.mmap`/`munmap`/`mremap` only, premise [OSM-01](premises.md#osm-01)) does **not** satisfy
`AllocSpec` ([alloc-spec.md](alloc-spec.md)) as it is stated, in any logic and for any invariant
that holds at program start. This is a limit of the specification's logic, not a bug of the
allocator or of the OS model: the native program is fine. This page records the obstructions,
their kernel-checked evidence, two upstream Zig bugs, the native comparison, and what a fix needs.

## The obstructions

`AllocSpec` states each vtable entry as a `Triple` (or `TotalTriple`). A triple quantifies over
every sequential memory whose heap (`Mem.heap`, the live bytes) splits into the precondition's
part and a frame. Everything in `Mem` outside the live bytes is unconstrained.

| | what the allocator reads | why no assertion constrains it | evidence |
|---|---|---|---|
| O3 | the atomic location of `addr_hint` (`@atomicLoad(.unordered)`, `@cmpxchgStrong`) | atomic locations are `Mem.atomics`, not heap cells; a location of another size at the same bytes makes `locIdx` throw `.unspecified` | `not_allocSpec_at_start`, `alloc_no_triple_at_start` |
| O1 | `@intFromPtr(addr_hint)` after the hinted mapping was unmapped, and the `@ptrFromInt` alignment check of the derived hint | a dead block's address is not in the heap; a memory with the same heap and the block's metadata missing gives `.illegal` (a misaligned block, `.panic`, is not mechanised) | `alloc_no_triple_after_free` |
| O2 | the size of the mapping, in `free` (`munmap(ptr[0..alignForward(len)])`) and `resize`/`remap` (tail `munmap`, `mremap` of the whole mapping) | `granted I p k bs = region p (2^k) bs ∗ I.tok p n k` hides the block of the region; when `len` is a page multiple the mapping has no tail for the token to own, so no token pins the mapping's size: with a larger mapping whose extra pages are in the frame, `free` is a legal prefix `munmap` that changes the frame's cells | argument below (not mechanised) |

The theorems are in `tests/roadmap/alloc-translated/PageObstruction.lean` (checked by
`check.sh`, axioms `propext`, `Classical.choice`, `Quot.sound`):

* `not_allocSpec_at_start : ∀ L c I, (∃ split of mem0's heap with I.own) → ¬ AllocSpec L vt c I`
  — the analogue of `Static.not_allocSpec`. `vt` is assembled from the translated entry
  functions (not read from the generated vtable global); `alloc` (a `ConcM` function: it reaches
  sync ops at the atomics) is the scheduler's run of one thread (fuel 16, oracle `0`).
* `alloc_no_triple_at_start`: `odd` has `mem0`'s heap and a 4-byte atomic location at
  `addr_hint`; `alloc(1, align 1)` from it throws `.unspecified` (`decide +kernel`).
* `alloc_no_triple_after_free`: `hinted` is the state after `alloc` then `free` (the `#guard`s
  check that the real run reaches this shape and that `alloc` succeeds from it); `hintedLost` has
  the same heap and no block 6; `alloc` from it throws `.illegal`. Both have no atomic location,
  so O1 holds independently of O3.

O2 in detail: let `m` be `mem0` plus an 8 KiB mapping (block 6), the precondition own the first
4 KiB as `region` with a token on the empty heap, the frame own the second 4 KiB. `free(⟨p, 4096⟩)`
computes `munmap(p[0..4096])`, which `unmapCase` admits as a prefix trim; the block's kind becomes
`.mapped 4096`, so the frame's cells change and no post-heap `hQ ∪ hF` exists. A token that owns
memory outside the mapping does not help; one that requires cells beyond the grant does not
hold after a real whole-page `alloc`.

## Upstream Zig bugs (both `ReleaseSafe` panics, native on x86_64-linux and aarch64-macos)

* `PageAllocator.map`: `page_aligned_len + max_drop_len` overflows for
  `n = maxInt(usize) - pageSize() - 2` with an alignment of `2 * pageSize()`; the guard
  `n >= maxInt(usize) - page_size` does not cover the alignment. `rawAlloc` panics
  "integer overflow" instead of returning `null`.
* `PageAllocator.realloc`: `mem.alignForward(usize, new_len, page_size)` overflows for
  `new_len > maxInt(usize) - (page_size - 1)`; `resize(s, maxInt(usize))` panics.

`AllocSpec.alloc` (every `len > 0`, `k < 64`) and `resize`/`remap` (every `n > 0`) are therefore
also unsatisfiable at those sizes; a fixed spec needs the bounds as preconditions (`alignedAlloc`
passes any comptime alignment, so the `alloc` overflow is reachable through the wrappers, and
`resize` passes any length). Not filed upstream (needs the user).

## Native comparison (stock Zig 0.16.0, `ReleaseSafe`)

| | aarch64-macos (16 KiB pages) | x86_64-linux (4 KiB pages, Docker `linux/amd64`) | model |
|---|---|---|---|
| `page_resize(10,20)`, `(10,5000)`, `(8192,10)`, `(10,20000)` | 1 1 1 0 | 1 0 1 0 | same per target (`Eval.lean`; the Linux guards stop at `(8192,10)`) |
| `remap` 10→5000, 8192→10, 10→20000 | 1 1 0 | 1 1 1 (`mremap` may move) | — (no translated client) |
| aligned alloc of 64 KiB / 1 MiB alignment, `resize` | aligned, `false` | aligned, `false` | — |
| `page_sum(0,10,10000)`, `page_create(7)` | 0 10 10000, 7 | same | same |

P2's claim holds natively: on x86_64-linux `resize` never calls `mremap` (stacks grow down and a
`resize` may not move), so `page_resize(10, 5000)` is `false`. `expected.txt` was the macOS run
only; `check.sh` now picks `expected-linux.txt` on 4 KiB-page hosts (the output depends on the
page size only), and CI runs the comparison. `native.zig` prints the first three `page_resize`
cases; the `(10,20000)`, `remap` and aligned-alloc rows are from one-off native runs.

## What a fix needs

1. **Block metadata in `granted` (O2, proof-only, P3 modules).** Give the token the region's
   block: e.g. an allocator field `blk : Ptr → Nat → Nat → Nat → Nat → BlockKind → Prop` and
   `granted I p k bs := (∃ A S K, ⌜I.blk p n k A S K⌝ ∗ regionIn p A S K (2^k) bs) ∗ I.tok p n k`.
   The page allocator's `blk` says `K = .mapped p.off`, `S = p.off + alignUp n P`, `P ∣ A`; its
   token owns the tail `regionIn (p.add n) A S K 1 tail`. The wrapper proofs need
   `regionIn`-preserving versions of `memsetUndef`, `storeItem` and `memcpy`.
2. **Memory beyond the heap (O1, O3, core).** Assertions must be able to constrain atomic
   locations and dead blocks' metadata, and frames must keep them: either per-location ownership
   of atomics plus persistent block metadata in the heap model, or an allocator specification in
   the concurrent logic (`ZigLean/Conc/Logic.lean`), whose protocol invariant is a predicate on
   the whole `Mem` (the page allocator is a concurrent object: `addr_hint` is shared by every
   thread). The second also gives the thread-safety statement the first lacks.
3. **Size bounds (upstream bugs).** Preconditions `len + 2^k ≤ 2^64 - P` for `alloc` and
   `n + P - 1 < 2^64` for `resize`/`remap`, or an upstream fix.

Until then `resize`, `remap` and `free` (plain `MemM`, no atomics or hint) can be proved against
a spec with fix 1, and `alloc` only from memories with a known hint block and well-formed atomics.
