# `std.heap.PageAllocator` against `AllocSpec` (phase P4b): findings

Status: the translated `PageAllocator` (Zig 0.17.1 and 0.16.0: one proof text over both
versions' translations, `tests/roadmap/alloc-translated/check.sh`; x86_64-linux and aarch64-macos, from
`posix.mmap`/`munmap`/`mremap` only, premise [OSM-01](premises.md#osm-01)) does **not** satisfy
`AllocSpec` ([alloc-spec.md](alloc-spec.md)) as it is stated, in any sound logic and for any invariant
that holds at program start. This is a limit of the specification's logic, not a bug of the
allocator or of the OS model: the native program is fine. This page records the obstructions,
their kernel-checked evidence, two upstream Zig bugs, the native comparison, and the status with
the full-state logic: the whole vtable is proved against `FAllocSpec` on x86_64-linux and
aarch64-macos (`free`/`resize`/`remap` total; `alloc` partial, for alignments up to a page: the
two open points are below, "Open: total correctness of `alloc`" and "O5"). O5, the model's unbounded fallback address, is
fixed in the OS model: no mapping ends above the target's user address space.

## The obstructions

`AllocSpec` states each vtable entry as a `Triple` (or `TotalTriple`). A triple quantifies over
every sequential memory whose heap (`Mem.heap`, the live bytes) splits into the precondition's
part and a frame. Everything in `Mem` outside the live bytes is unconstrained.

| | what the allocator reads | why no assertion constrains it | evidence |
|---|---|---|---|
| O3 | the atomic location of `addr_hint` (`@atomicLoad(.unordered)`, `@cmpxchgStrong`) | atomic locations are `Mem.atomics`, not heap cells; a location of another size at the same bytes made `locIdx` throw `.unspecified`. Resolved in the model: an overlapping location whose accesses all happened before is retired (`retireAt`); only racing mixed sizes are `.unspecified` | `alloc_odd` (regression: no error) |
| O1 | `@intFromPtr(addr_hint)` after the hinted mapping was unmapped, and the `@ptrFromInt` alignment check of the derived hint | a dead block's address is not in the heap; a memory with the same heap and the block's metadata missing gives `.illegal` (a misaligned block, `.panic`, is not mechanised) | `hinted_heap`, `alloc_hintedLost`, `alloc_hinted` |
| O2 | the size of the mapping, in `free` (`munmap(ptr[0..alignForward(len)])`) and `resize`/`remap` (tail `munmap`, `mremap` of the whole mapping) | `granted I p k bs = region p (2^k) bs ∗ I.tok p n k` hides the block of the region; when `len` is a page multiple the mapping has no tail for the token to own, so no token pins the mapping's size: with a larger mapping whose extra pages are in the frame, `free` is a legal prefix `munmap` that changes the frame's cells | argument below (not mechanised) |

The theorems are in `tests/roadmap/alloc-translated/PageObstruction.lean` (checked by
`check.sh`, axioms `propext`, `Classical.choice`, `Quot.sound`):

* `vt` is assembled from the translated entry functions (not read from the generated vtable
  global); `alloc` (a `ConcM` function: it reaches sync ops at the atomics) is the scheduler's run
  of one thread (fuel 16, oracle `0`).
* O3 is resolved in the model (regression `alloc_odd`): `odd` has `mem0`'s heap and a 4-byte
  atomic location at `addr_hint`. `alloc(1, align 1)` from it used to throw `.unspecified`
  (`not_allocSpec_at_start`, `alloc_no_triple_at_start`). The mixed-size policy now retires a
  location whose accesses all happened before (`retireAt`, `docs/weak-cas.md`), so it succeeds.
* O1: `hinted` is the state after `alloc` then `free` (the `#guard`s
  check that the real run reaches this shape and that `alloc` succeeds from it); `hintedLost` has
  the same heap and no block 6; `alloc` from it throws `.illegal`. Both have no atomic location,
  so O1 holds independently of O3.

The former `alloc_no_triple_after_free` theorem stated that, for every sound heap-only `Logic L`,
every context `c`, return address `ra`, precondition `P` and postcondition `Q`, if `hinted.heap`
splits disjointly as `hP ∪ hF` with `P hP`, then `¬ L.T P (vt.alloc c 1 0 ra) Q`. Its argument was exactly
the checked counterexample above: `hintedLost` has the same live heap and is sequential, but the
allocation gives `.illegal`, which a sound triple excludes. The theorem about the legacy
judgment is retired with that judgment's clients. The memory equality and both allocation
outcomes remain kernel-checked in `PageObstruction.lean`; the executable guards connecting
`hinted` to the real translated `alloc`/`free` run are retained. The replacement specification
is `FAllocSpec`: `PageAlloc.own` keeps
the missing address as `known`, so the bad memory does not satisfy its precondition.

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

## Native comparison (stock Zig 0.16.0 and 0.17.1, `ReleaseSafe`: the same output)

| | aarch64-macos (16 KiB pages) | x86_64-linux (4 KiB pages, Docker `linux/amd64`) | model |
|---|---|---|---|
| `page_resize(10,20)`, `(10,5000)`, `(8192,10)`, `(10,20000)` | 1 1 1 0 | 1 0 1 0 | same per target (`Eval.lean`; the Linux guards stop at `(8192,10)`) |
| `remap` 10→5000, 8192→10, 10→20000 | 1 1 0 | 1 1 1 (`mremap` may move) | — (one-off runs; the compared `remap`/`realloc` calls are below) |
| aligned alloc of 64 KiB / 1 MiB alignment, `resize` | aligned, `false` | aligned, `false` | — |
| `page_sum(0,10,10000)`, `page_create(7)` | 0 10 10000, 7 | same | same |

P2's claim holds natively: on x86_64-linux `resize` never calls `mremap` (stacks grow down and a
`resize` may not move), so `page_resize(10, 5000)` is `false`. `expected.txt` was the macOS run
only; `check.sh` now picks `expected-linux.txt` on 4 KiB-page hosts (the output depends on the
page size only), and CI runs the comparison. `native.zig` prints the first three `page_resize`
cases; the `(10,20000)`, `remap` and aligned-alloc rows are from one-off native runs.

### Growth by `remap` and `realloc` (M02)

The proved paths and their native comparison. Every row holds for Zig 0.16.0 and 0.17.1 (both
versions' proofs, model lines and native runs); the model's lines
(`Eval.lean` `growLinux`, `growMacos`) and the native run's lines are compared with the same
file per target (`expected-linux.txt`, `expected.txt`;
[the fixture's README](../tests/roadmap/alloc-translated/README.md) has the calls and words).
The native x86_64-linux run is on a Linux 6.6 kernel, not under Rosetta: Rosetta aborts on the
`2^47`-byte `mremap`.

| Path | Proved | Compared with the native run |
|---|---|---|
| `resize` within the page, a shrink (tail `munmap`), a growth past the page that fails | `PageSpec.resize_spec`, `PageSpecMacos.resize_spec` | both targets (`page_resize`) |
| `remap` grows in place (x86_64-linux: `mremap` with the pages behind free) | `PageSpec.remap_spec` (`FTotalTriple.mremapMove'`) | x86_64-linux: `page_grow`, in place, old bytes kept |
| `remap` moves (x86_64-linux: `mremap` under `MAYMOVE`, no room in place) | `PageSpec.remap_spec` | x86_64-linux: `page_grow_blocked`, moved, old bytes kept, the neighbour unchanged; the old address faults (`page_grow_stale`) |
| `remap` fails, the old block unchanged | `PageSpec.remap_spec`, `PageSpecMacos.remap_spec` | x86_64-linux: a `2^47`-byte growth; aarch64-macos: every growth past the page |
| `remap` shrinks | `PageSpec.remap_spec` (`mremapShrinkR`), `PageSpecMacos.remap_spec` (`munmapTailR`) | both targets |
| `realloc` (the `mem.Allocator` wrapper: `remap`, else a new block, copy, free) | the wrapper for every allocator that meets the contract: `realloc_spec`, `reallocAdvanced_spec` (`AllocFba/Wrappers.lean`, `Interfaces/SentinelSpec.lean`, [alloc-spec.md](alloc-spec.md)); the instance of the wrapper in `page.zig`'s translation has no theorem of its own | both targets; the copying path natively on aarch64-macos only (on x86_64-linux `mremap` moves instead; the model runs that path with a denied `mremap`) |

Not compared natively: a kernel that moves a mapping although there is room in place and a
`mremap` that fails for lack of memory (the model's oracles `mremapMoves` and the failure
decision; no native run forces them) and alignments above a page. The model's lines are run
with an 8 MiB main-thread stack reserve (`Eval.stackBytes`, premise STK-02): with the fresh
placement alone, a stack block of 0.17.1's `realloc` wrapper lies right behind the mapping, and
the model's `mremap` moves the block where the kernel, whose stack is elsewhere, grows it in place.
Both are outcomes the proofs cover; the reserve gives the native layout.

## Status with the full-state logic (`codex/alloc-p4b-page`)

The full-state separation logic (`ZigLean/Sep/Full`, [sep-full-state.md](sep-full-state.md))
restates the specification as `FAllocSpec` (`ZigLean/Sep/Full/AllocSpec.lean`): the same entries,
pre- and postconditions, over assertions that can own atomic layouts (`apts`, O3) and keep block
knowledge after `free` (`known`, O1).

| | status | where |
|---|---|---|
| O2 | fixed: the page allocator's token owns the rest of the grant's last page and pins the mapping (`.mapped p.off`, `S = p.off + alignUp n P`); with block extents it also holds the mapping's extent authority with the fraction that the grant's share leaves (`PageTok.ptok`), and the claim on the mapping from the grant's end on (byte-range claims) | `PageTok.lean` |
| `free`, `resize`, `remap` | proved: `free_spec`, `resize_spec`, `remap_spec` are the `FAllocSpec FLogic.total` fields for every allocator state `own`, from the generated code and OSM-01 only; x86_64-linux and aarch64-macos (no `mremap`: `remap` stays in place) | `tests/roadmap/alloc-translated/PageSpec.lean`, `PageSpecMacos.lean` |
| block extents | each entry collects the mapping's whole extent (the token's authority and the grant's share, `EUpd.unlend`), runs the full-state OS rules on it (`FTotalTriple.munmapWhole'`, `munmapTailR`, `mremapShrinkR`, `mremapMove'`, `ZigLean/Sep/Full/Mmap.lean`) and lends half of the new extent to the new grant. `PageSpec.inv_legacy` (the legacy reading of the invariant, for the removed wrapper contracts) is gone: a legacy grant has no extent share | `tests/roadmap/alloc-translated/PageSpec.lean`, `ZigLean/Sep/Full/Mmap.lean` |
| size bounds | `fits n k := n + 2^k + P ≤ 2^64`; the token keeps `n + P ≤ 2^64` | `PageSpec.legacy` |
| O1, O3 | resolved: the allocator state owns the hint word (`aptsE`) and knows its target's page-aligned address (`known`); one state for every page size | `PageTok.hown` (`PageAlloc.own`, `PageAllocMacos.own`) |
| O4 | fixed in the memory model: an ambiguous `@ptrFromInt` gives a pointer without provenance | below |
| `alloc` | proved for alignments up to a page (`ainv.fits`: `k ≤ 12` on x86_64-linux, `k ≤ 14` on aarch64-macos), partial correctness: `PageAlloc.fallocSpec` and `PageAllocMacos.fallocSpec` are the whole `FAllocSpec FLogic.partial`, each with its creation triple from the start memory's null hint word | `tests/roadmap/alloc-translated/PageAlloc.lean`, `PageAllocMacos.lean` |
| `alloc`, total | open: no judgment of the framework states it | below |
| O5 | fixed in the OS model (OSM-01): `mmap` fails with `ENOMEM` above `Os.Target.addrLimit`; the proof of `alloc` for alignments above a page is open | below |

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

`PageAlloc.lean` (x86_64-linux) and `PageAllocMacos.lean` (aarch64-macos, where `posix.mmap` and
`munmap` are libc's, the same `Os.mmap`/`Os.munmap` of OSM-01 at `Os.Target.macos`) prove
`alloc` from the generated code, with one proof text each: the invariant and `fsym`. The
allocator state is the same on both targets, `PageTok.hown P` for the page size `P`: the hint
word as a pointer-valued atomic points-to (`aptsE`) and, for a non-null hint, `known b A` of its
block with `A + off` page-aligned. `alloc` reads the hint (`FTriple.atomicLoadUnorderedEnc`),
takes its address (`FTriple.ptrAddr`: the hinted mapping may be unmapped), passes the page check
of the derived address, recovers a pointer (`FTriple.ptrFromAddr`), maps `alignUp len P` bytes
(`FTotalTriple.mmap'`, which gives the new mapping's full extent), and publishes the new
mapping with a `cmpxchg` that succeeds (`FTriple.cmpxchgPtr`) and a `known` taken from owning
it (`known_of_region`). `fsym` walks the generated code (`alloc_ct`); the caller gets the first
`len` bytes with the token.

`alloc` is a concurrent function. The vtable entry is its call in the caller's thread, each
atomic op's oracle choice `0` (`Sched.soloRun`; `CTriple`, `ZigLean/Sep/Full/Conc.lean`).
`alloc_threadFree` shows it stops only at the two oracle picks, so the one-thread scheduler run
is the same reading (`alloc_run`, `Sched.run_eq_seqRun`). The scheduler's run itself is not an
`FAllocSpec` entry: it runs as thread `0` from any memory and ends the thread
(`checkJoinedByChild`), which fails in an `FSeq` memory with another current thread or an
unjoined child, whatever the allocator does.

### Open: total correctness of `alloc`

`free`, `resize` and `remap` are `FTotalTriple`s. `alloc` is not, and no proof inside the
current framework can make it one:

* `alloc` is a `ConcM` function (its two atomic ops stop at an oracle pick). The framework's
  judgment for a `ConcM` call is `CTriple`, which is partial correctness by definition: a run
  tree that is `leaf none` (no result at this depth) satisfies `CTriple.Run`
  (`ZigLean/Sep/Full/Conc.lean`). There is no total judgment for a `ConcM` call.
* The vtable entry is the `MemM` program `Sched.soloRun 16 (heap_PageAllocator_alloc …)`. Its
  total statement `FTotalTriple (ainv.own ⋆ ainv.fee φ) (vt.alloc c len k ra) (ainv.allocPost
  len.toNat k φ)` is well-formed, but `fsym` has no rule and no backend for the in-thread
  reading: it stops with `fsym: no rule for the command Sched.soloRun 16
  (heap_PageAllocator_alloc c len { bits := BitVec.ofNat 6 k } ra)`. No library equation moves
  `soloRun` through a bind: the depth left for the rest of a bind is the depth at which the
  first part's run ended, so `soloRun n (x >>= f)` is not a `MemM` bind of `soloRun n x`.
* The atomic rules of the hint word (`FTTriple.atomicLoadUnorderedEnc`, `FTTriple.cmpxchgPtr`,
  `ZigLean/Sep/Full/AtomicPtr.lean`) are partial too: they are proved by `FTTriple.of_step`,
  which leaves the run without a result unconstrained.

What a proof needs is a decision on the framework (a total reading of a `ConcM` call with the
depth as a resource, and `fsym`'s walk of it), then the two atomic rules as total rules; the
invariant and the statement above stay as they are. Engine ledger row `conc-call-total`.

### O5: alignments above a page (fixed in the model; the proof is open)

For `2^k > P`, `map` asks for `2^k - P` extra bytes, and `std.mem.alignPointer` adds
`2^k - 1` to the mapping's address with an overflow check. A placement proposal is taken only
if the mapping's pages end at or below 2^64 (`Mem.placeOk`), and then the check cannot overflow.
But the fallback address after every block (`Mem.top`, when the proposal is not valid) is a
`Nat` without a bound. From a memory whose last block ends just below `2^64 - 4096`,
`alloc(1, align 8192)` maps two pages at `2^64 - 4096`, the check overflows, `alignPointer`
returned `null` and `map` panicked (`PageAlloc.alloc_high`, kernel-checked before the fix).
So no invariant that such a memory satisfies admitted `k ≥ 13`, and `ainv.fits` required
`k ≤ 12`. Natively the kernel never maps that high.

The fix is in the OS model (OSM-01, user-approved): an `mmap` or `mremap` move or growth whose
mapping would end above the target's user address space (`Os.Target.addrLimit`: `2^47` on
x86_64-linux, `MACH_VM_MAX_ADDRESS = 0x7FFFFE000000` on aarch64-macos), at a proposed address or
at the fallback `Mem.top`, fails with `ENOMEM`, and `TotalTriple.mmap` gives the bound
`A + alignUp len P ≤ addrLimit` ([os-mmap.md](os-mmap.md)). With it `alignPointer`'s check
`A + 2^k - 1 < 2^64` always passes: the aligned pointer is `alignUp A 2^k - A` bytes in, and
`map` unmaps those bytes and the pages above the granted ones.

**The proof for `k` above the page's is open.** A hand-walked proof over the legacy judgment
covered every alignment (`PageAlloc.alignPointer_gen`, `munmap_drop`, `munmap_rest`,
`TotalTriple.munmapPrefix`/`munmapTail`); it was removed when `alloc` moved to the invariant and
`fsym` (2026-10-12), and since then `ainv.fits` again requires `k ≤ 12` (`k ≤ 14` on
aarch64-macos). With the unrestricted `fits` of `PageSpec.inv`, `fsym` stops in the branch that
unmaps the pages above the granted ones: at the default heartbeat limit in the rule
`FTTotalTriple.ptrProject_elem_of` on `ptrProject (a.ptr.elem 1 …) fun x => x.elem 1 (… &&&
~~~4095#64)`, and with fifteen times the limit one step later, in `FTotalTriple.munmapTailR` on
that tail's `munmap`. The offsets there are terms in a symbolic `2 ^ k`, which the arithmetic
solver does not decide. The rule for the bytes before the aligned address,
`FTotalTriple.munmapPrefix'` (`ZigLean/Sep/Full/Mmap.lean`), is not a step rule of `fsym` and is
stated over `bytesAt`; only the tail has a region form (`munmapTailR`). Engine ledger row
`page-alloc-large-align`.

`PageAlloc.alloc_high` is now the regression: from the same memory the
`mmap` fails and `alloc` returns `null`. `PageAlloc.alloc_top` runs the prefix `munmap` on a
mapping that a placement proposal puts three pages below `2^47`, `PageAlloc.alloc_edge` the tail
`munmap` on an aligned mapping that ends exactly at `2^47`. Still open: the model never
places a later mapping into the unmapped prefix while the rest is live, which the kernel may do
([os-mmap.md](os-mmap.md)).

### Negative check

`tests/roadmap/alloc-translated/mutant.sh` deletes the tail `munmap` from the translated
`realloc` (a shrink that leaks the cut pages but runs without an error) and rechecks
`PageSpec.lean`, which then fails. The size-pinning token is what rejects it.
