# `std.heap.PageAllocator` against `AllocSpec` (phase P4b): findings

Status: the translated `PageAllocator` (Zig 0.16.0, x86_64-linux and aarch64-macos, from
`posix.mmap`/`munmap`/`mremap` only, premise [OSM-01](premises.md#osm-01)) does **not** satisfy
`AllocSpec` ([alloc-spec.md](alloc-spec.md)) as it is stated, in any sound logic and for any invariant
that holds at program start. This is a limit of the specification's logic, not a bug of the
allocator or of the OS model: the native program is fine. This page records the obstructions,
their kernel-checked evidence, two upstream Zig bugs, the native comparison, and the status with
the full-state logic: the whole vtable is proved against `FAllocSpec` for every alignment
(`alloc` partial, `free`/`resize`/`remap` total). O5, the model's unbounded addresses, is fixed
in the OS model: no mapping ends above the target's user address space.

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

* `not_allocSpec_at_start : ∀ L c I, (∃ split of mem0's heap with I.own) → I.fits 1 0 → ¬ AllocSpec L vt c I`
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

## Status with the full-state logic (`codex/alloc-p4b-page`)

The full-state separation logic (`ZigLean/Sep/Full`, [sep-full-state.md](sep-full-state.md))
restates the specification as `FAllocSpec` (`ZigLean/Sep/Full/AllocSpec.lean`): the same entries,
pre- and postconditions, over assertions that can own atomic layouts (`apts`, O3) and keep block
knowledge after `free` (`known`, O1).

| | status | where |
|---|---|---|
| O2 | fixed: the page allocator's token owns the rest of the grant's last page and pins the mapping (`.mapped p.off`, `S = p.off + alignUp n P`) | `PageSpec.tok` |
| `free`, `resize`, `remap` | proved: `free_spec`, `resize_spec`, `remap_spec` are the `FAllocSpec FLogic.total` fields for every allocator state `own`, from the generated code and OSM-01 only; x86_64-linux and aarch64-macos (no `mremap`: `remap` stays in place) | `tests/roadmap/alloc-translated/PageSpec.lean`, `PageSpecMacos.lean` |
| size bounds | `fits n k := n + 2^k + P ≤ 2^64`; the token keeps `n + P ≤ 2^64` | `PageSpec.legacy` |
| O1, O3 | resolved: the allocator state owns the hint word (`aptsE`) and knows its target's page-aligned address (`known`) | `PageAlloc.own` |
| O4 | fixed in the memory model: an ambiguous `@ptrFromInt` gives a pointer without provenance | below |
| `alloc` | proved for every alignment (`k < 64`, `fits`), partial correctness: `PageAlloc.fallocSpec` is the whole `FAllocSpec FLogic.partial` for x86_64-linux | `tests/roadmap/alloc-translated/PageAlloc.lean` |
| O5 | fixed in the OS model (OSM-01): `mmap` fails with `ENOMEM` above `Os.Target.addrLimit` | below |

### O4: an ambiguous `@ptrFromInt` (fixed)

`alloc` turns the derived hint address back into a pointer (`@ptrFromInt`, `Zig.ptrFromAddr`)
before it passes it to `mmap`. Both modelled targets grow the stack down, so the address is
`((@intFromPtr(hint) -% page_aligned_len) & ~(alignment - 1)) -% max_drop_len`, below the last
mapping. Under the default `.strict` provenance mode, `ptrFromAddr` used to throw `.unspecified`
when two or more blocks' ranges `[addr, addr + size]` contained the address (dead blocks count).
No precondition could rule this out: the covering blocks belong to the frame or are dead, and
`Mem.Seq` (and `FSeq`) allows such layouts (M05 address reuse, any placement oracle that allows
adjacent blocks).

The fix is in the memory model (`ZigLean/Mem/Basic.lean`, approved by the user): an ambiguous
recovery returns the provenance-free pointer `⟨none, n⟩`. `ptrAddr` of it is still `n`, and every
access through it is `.illegal` ([address-reuse.md](address-reuse.md)). This is a conservative
over-approximation; natively the hint goes only to `mmap`, which may ignore it.
`PageObstruction.alloc_hintedAmb` is the regression: from `hinted` plus one dead 8-byte block
that ends at the derived address 4096 (where global block 0 starts), `alloc(1, align 1)` now
returns a mapping.

### `alloc`

`PageAlloc.lean` proves `alloc` from the generated code. The allocator state `own` is the hint
word as a pointer-valued atomic points-to (`aptsE`) and, for a non-null hint, `known b A` of its
block with `A + off` page-aligned. `alloc` reads the hint (`FTriple.atomicLoadUnorderedEnc`),
takes its address (`FTriple.ptrAddr`: the hinted mapping may be unmapped), passes the page check
of the derived address, recovers a pointer (`FTriple.ptrFromAddr`), maps `alignUp len P` bytes
(`TotalTriple.mmap`), and publishes the new mapping with a `cmpxchg` that succeeds
(`FTriple.cmpxchgPtr`) and a `known` taken from owning it. The grant is the whole mapping
(`PageSpec.regrant`).

`alloc` is a concurrent function. The vtable entry is its call in the caller's thread, each
atomic op's oracle choice `0` (`Sched.soloRun`; `CTriple`, `ZigLean/Sep/Full/Conc.lean`).
`alloc_threadFree` shows it stops only at the two oracle picks, so the one-thread scheduler run
is the same reading (`alloc_run`, `Sched.run_eq_seqRun`). The scheduler's run itself is not an
`FAllocSpec` entry: it runs as thread `0` from any memory and ends the thread
(`checkJoinedByChild`), which fails in an `FSeq` memory with another current thread or an
unjoined child, whatever the allocator does.

### O5: alignments above a page (fixed)

For `2^k > P`, `map` asks for `2^k - P` extra bytes, and `std.mem.alignPointer` adds
`2^k - 1` to the mapping's address with an overflow check. The model's addresses are unbounded:
`Mem.nextAddr` is a `Nat`, and `mmap` places a mapping at the next page address however high.
From `mem0` with `nextAddr = 2^64 - 4096`, `alloc(1, align 8192)` maps two pages there, the check
overflows, `alignPointer` returns `null` and `map` panics (`PageAlloc.alloc_high`, kernel-checked).
So no invariant that such a memory satisfies admitted `k ≥ 13`, and `ainv.fits` required
`k ≤ 12`. Natively the kernel never maps that high.

The fix is in the OS model (OSM-01, user-approved): an `mmap` or `mremap` growth whose mapping
would end above the target's user address space (`Os.Target.addrLimit`: `2^47` on x86_64-linux,
`MACH_VM_MAX_ADDRESS = 0x7FFFFE000000` on aarch64-macos) fails with `ENOMEM`, and
`TotalTriple.mmap` gives the bound `A + alignUp len P ≤ addrLimit` ([os-mmap.md](os-mmap.md)).
With it `alignPointer`'s check `A + 2^k - 1 < 2^64` always passes (`PageAlloc.alignPointer_gen`):
the aligned pointer is `drop A (2^k) = alignUp A 2^k - A` bytes in. `map` unmaps those bytes
(`TotalTriple.munmapPrefix`, `PageAlloc.munmap_drop`) and the pages above the granted ones
(`TotalTriple.munmapTail`, `PageAlloc.munmap_rest`), and `ainv` is `PageSpec.inv own` with the
unrestricted `fits`. `PageAlloc.alloc_high` is now the regression: from the same memory the
`mmap` fails and `alloc` returns `null`. `PageAlloc.alloc_top` runs the prefix `munmap` at the
end of the address space.

### Negative check

`tests/roadmap/alloc-translated/mutant.sh` deletes the tail `munmap` from the translated
`realloc` (a shrink that leaks the cut pages but runs without an error) and rechecks
`PageSpec.lean`, which then fails. The size-pinning token is what rejects it.
