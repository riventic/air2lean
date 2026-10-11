# The translated `ArenaAllocator` (allocator milestone 2)

Status: translation, executable checks, kernel-checked obstructions and a mutant are done.
`free`, `resize` and `remap` of the stock arena (x86_64-linux, aarch64-macos) and of the patched
one are proved against `FAllocSpec` over an invariant whose tokens are ghost tokens of the arena's
current epoch that name their regions (O-A), with live-block disjointness for O-F. The invariant,
its lemmas and the proof tactics are one shared layer (`AllocArena/Core.lean`), elaborated against
each module. **The stock arena does not satisfy `FAllocSpec`'s
`alloc` field for any child** (O-E, O-B below): its node sizes grow without bound, so every child
eventually refuses a request or the arena's own size arithmetic overflows. A patch that fixes
this ([upstream draft](upstream/arena-oob-gep.md), `upstream/arena-fix.patch`) is translated from
real AIR and runs as natively; its `alloc` and `reset` are not proved yet (§What is proved).
Fixture: [`tests/roadmap/alloc-arena`](../tests/roadmap/alloc-arena/README.md). The plan and the
earlier milestone: [alloc-spec.md](alloc-spec.md), [allocator-model.md](allocator-model.md),
[alloc-page.md](alloc-page.md).

`std.heap.ArenaAllocator` is translated from its own AIR (Zig 0.16.0), its child allocator
included: an ordinary indirect call through `child_allocator.vtable`. As with the page allocator,
only `posix.mmap`/`munmap`/`mremap` are trusted (OSM-01), and there is no model of the arena.

## Versions

| Zig | `lib/std/heap` | status |
|---|---|---|
| 0.16.0 | `ArenaAllocator.zig`: lock-free (`used_list`/`free_list` atomics, `end_index` bumped by `@atomicRmw .Add`, `Node.Size` packed with a `resizing` bit) | translated (x86_64-linux, aarch64-macos); patched (`upstream/arena-fix.patch`): x86_64-linux |
| 0.17.0 | the same implementation (only the tests differ) | same code; translated mode needs the 0.16.0 OS boundary rows |
| 0.15.2 | `arena_allocator.zig`: the older single-threaded arena (`SinglyLinkedList` of `BufNode`s, `state.end_index`) | not translated: `@fieldParentPtr` over the cyclic list (parent recovery), and translated mode is 0.16.0-only |

## Translation

Three admissions, all under `--allocator-model translated` only (std mode is unchanged and
rejects the same AIR):

* **Pointer casts over a cyclic error-free type graph.** `Node.allocatedSliceUnsafe`,
  `beginResize`, `loadBuf`, `reset`, `alloc`, `free` and `resize` cast between `*Node` and its
  bytes, and `Node` points to itself (`next: ?*Node`). The strict capability scan rejects every
  cycle. `translatedErrorCapability` (`Air2Lean/Check.lean`) falls back to the bounded closed-graph
  proof that global aliases already use (`closedErrorFreeAliasGraph`): no type reachable from the
  pointee is an error set or error union. A cycle that reaches an error union stays rejected
  (`test_cli.py`).
* **`*anyopaque` fields.** The arena state contains `child_allocator.ptr: *anyopaque`, so the
  recovery of `*ArenaAllocator` from `ctx` met an opaque type. In that fallback a `*anyopaque`
  edge is not followed: an opaque pointee is no typed storage, and every recovery of a typed
  pointer from it is itself a checked cast (`fromOpaque`).
* **`unordered` loads of packed structs.** `endResize` asserts on
  `@atomicLoad(Size, &node.size, .unordered)`. `Zig.atomicLoadUnorderedAsC`
  (`ZigLean/Conc/AtomicWord.lean`) is the integer `unordered` load, decoded with the packed
  struct's `Packed` instance as for the other typed atomics. Other non-integer, non-pointer
  pointees stay rejected.

The pointer atomics (`stealFreeList`'s `.Xchg`, `pushFreeList`'s weak `cmpxchg`, `tryPushNode`'s
strong one, the acquire load of `used_list`) were already in the subset (C09). `alloc` calls its
child, and the child dispatch includes `ArenaAllocator.alloc` itself (same function type), so
the generated `alloc` and its loops are one `partial_fixpoint` group.

On the one-thread schedule the translated clients equal the native run
(`Eval.lean`, `expected.txt`): allocation, a request larger than the child buffer, resize in
place and growth past the node, `reset(.retain_capacity)` and `reset(.free_all)` with
`queryCapacity`, and an arena over `page_allocator`.

## Specification and obstructions

The goal is `FAllocSpec FLogic.partial vt ctx I` for the arena's four entries, for every child
that satisfies `FAllocSpec`, read in one thread (`Sched.soloRun`, `CTriple`, as for the page
allocator), with `reset` specified separately. Concurrency follows the D2 premises: the theorem is
about one thread; thread-safety of the arena (which needs a thread-safe child) and the spawn
policy are explicit premises of any concurrent client theorem, not consequences of this one.
`FAllocSpec` is not weakened. The following obstructions stand between the code and that
statement. O-A and O-F are resolved for every entry; O-E and O-B rule out `alloc` for the stock
arena and any child, so the full statement is the goal for the patched arena, and the stock
arena's `free`, `resize`, `remap` (and `reset`) are proved where they hold.

**O-A: a foreign or stale `free` on an empty arena panics** (kernel-checked:
`ArenaObstruction.foreign_free_panics`; natively `panic: attempt to use null value`).
`free` and `resize` start with `loadFirstNode().?`. An arena without a node (fresh, or after
`reset(.free_all)`) panics for every slice. So `own ⋆ granted p k bs` must be unsatisfiable there:
the token must record that this arena issued a region in its current generation.
**Resolved by ghost state** ([sep-full-state.md](sep-full-state.md) §Ghost state): `own` holds the
authority `gauth γ e M` of an epoch ledger of named grants (`M`: grant id ↦ region, empty without
a first node), and the token of the slice at `p` of `n` bytes is `∃ i, gfrag γ e i (p, n)`. A
token of the current epoch names a grant of `M` (`gfrag_mem`), so the arena has a node
(`ArenaSpec.free_pre`). Because the token names its region, a `free`, `resize` or `remap` of a
slice that this arena did not grant in its current epoch has no token: it is a permission
violation, not a case the proof covers. `reset` will bump the epoch (`Upd.bump`): tokens the
client kept become stale, and a stale token belongs to the invariant of an older epoch, whose
`own` no longer exists.

**O-E: after a failed `alloc`, `free` and `resize` form an out-of-bounds pointer**
(kernel-checked: `ArenaObstruction.oob_free_illegal`; from real runs: `arena_oom_free` in
`Eval.lean`; [upstream draft](upstream/arena-oob-gep.md)). A request that does not fit leaves the
first node's `end_index` past its buffer. If the child then fails, `alloc` returns `null` with that
node still first. `free`/`resize` compute `buf_ptr + cur_end_index`, which is
`getelementptr inbounds` natively, and branch on its comparison: undefined behaviour in LLVM,
illegal behaviour in Zig. With the in-bounds projection rule of the memory model (MM-3,
`Zig.ptrProject`) the translated code is `.illegal` there. `arena_oom_free` reaches that state by
the arena's own code over a 256-byte `FixedBufferAllocator`: an allocation that fits, one of 4096
bytes that the child refuses, then the `free` of the first; the translated run is `.illegal`
(natively the undefined behaviour has no visible effect). `arena_oob_free` builds the same state
by hand for the kernel-checked theorem (the kernel does not evaluate `alloc`, a `partial_fixpoint`
group).

**O-E is reachable for every child.** A bound on the child does not help: the arena's requests
are not bounded by its own `fits`. A new node has size `alignForward(1.5 · (prev_size + 24 +
alignment + n + 16), 2)` and the in-place growth asks for `24 + aligned_index + n`, where
`prev_size` is the first node's buffer length; nodes are not shrunk before `reset`. Repeated
`alloc(1)` therefore asks for ever larger nodes: the in-place growth asks for the current size
plus the request, and a new node is at least 1.5 times the previous buffer. A child that accepts every
request up to a bound `B` eventually gets one above `B` and may refuse it (O-E); a child that
accepts every request eventually makes the arena's overflow-checked size arithmetic panic (O-B).
So for every child, an invariant that holds after `init` and is kept by `alloc` (for a `fits` that
admits some request) reaches a state in which `FAllocSpec`'s `alloc` (a panic) or `free` (an
illegal projection of an outstanding grant) fails. `FAllocSpec` cannot be weakened to avoid this
(no premise per triple, no budget). The kernel-checked form of this refutation
(`not_fallocSpec_arena`) is not written yet; the argument above and `arena_oom_free` are the
evidence. The fix is in the arena: the patch gives the reservation back when the request does
not fit and makes the overflowing sizes fail instead of panicking.

**O-F: deciding a foreign slice needs live-block disjointness.** `free` and `resize` compare
`buf_ptr + end_index` with `memory.ptr + memory.len` by address (`Zig.ptrEqAddr`, MM-1). For
a slice in another block, equal addresses would make `free` give back bytes of the node that the
caller does not own. **Resolved by stage 3** of [sep-full-state.md](sep-full-state.md): live
blocks have disjoint address ranges in every `Mem.FSeq` memory (`Mem.LiveDisjoint`), and
`Holds.apart` turns ownership of a byte in each of two blocks into disjoint ranges. A slice of
another block never matches; a slice of the node's block that ends at `buf_ptr + end_index` lies
past the header, which `own` holds (`ArenaSpec.region_apart`). No premise per triple.

**O-B: unbounded node growth overflows.** A new node has size
`alignForward(big + big / 2, 2)` with `big = prev_size + @sizeOf(Node) + alignment + n + 16`,
and the in-place growth asks for `@sizeOf(Node) + aligned_index + n`, all overflow-checked: a
panic, not a `null`. Node sizes grow geometrically (O-E), so the stock arena reaches these panics
over a child that grants every request. The patch computes these sizes with checks that fail the
request instead. A bound on the child's grants is no premise of the arena theorem: it would not
make O-E unreachable (above), and `docs/premises.md` lists none.

**O-C: the child's `fits`.** The arena asks its child for sizes that depend on its state
(`prev_size`, the bumped `end_index`), not only on the request, at alignment `@alignOf(Node) = 8`.
A child specification covers only requests within `CI.fits`; with the patch, a request outside
the child's `fits` must be one that the arena's own `alloc` contract allows to fail.

**O-D: one thread.** The atomic rules (`ZigLean/Sep/Full/Atomic.lean`, `AtomicPtr.lean`,
`AtomicRules.lean`) read an atomic op with the oracle's choice `0`, as one thread does. A
multi-threaded specification of the lock-free code (the `resizing` bit as a lock, the stolen
free list) is not attempted.

## What is proved and checked

* `ArenaSpec.free_spec`, `resize_spec`, `remap_spec` (`tests/roadmap/alloc-arena/ArenaSpec.lean`;
  `ArenaSpecMacos.lean` for aarch64-macos, `ArenaSpecFixed.lean` for the patched arena):
  the arena's translated `free`, `resize` and `remap` meet `FAllocSpec`'s
  fields, e.g. `FLogic.partial.T (I.own ⋆ I.granted s.ptr k bs) (Sched.soloRun fuel free) (fun _ =>
  I.own)` with `I = inv CI γ e ctx`, for every child invariant `CI`, epoch `e` and depth `fuel`,
  from the generated code only. The invariant (`own`): the arena struct with `used_list`/`free_list`
  as pointer-valued atomic words, the epoch ledger's authority `gauth γ e M` (`M`: the grants of
  this epoch; empty without a first node), the first node (header words: `size` and `end_index` as
  integer atomic words, `next`; the child's token; the unused tail of its buffer), the other used
  nodes and the free list as `next`-linked chains, the child's `own`, and `Junk` (bytes that frees
  of earlier allocations leaked back). The token of a grant names it: `∃ i, gfrag γ e i (p, n)`.
  * `free`: on a match the slice's bytes rejoin the tail and `end_index` moves back
    (`FTriple.cmpxchgHit`); otherwise they become junk. Either way the grant is retired
    (`Upd.retire`).
  * `resize`: a slice that is not the first node's last one only shrinks (cut bytes to junk); the
    last one moves `end_index` back (cut bytes rejoin the tail) or into the tail when it has room
    (`Node.loadBuf` reads the `size` word: `FTriple.atomicLoadAs`; clearing the `resizing` bit of an
    even size is the size: `toInt_ofBits`). A successful resize re-points the grant at the new
    length (`Upd.reassign`). `remap` is `resize` and returns `memory.ptr`.
  * Axioms: `propext`, `Classical.choice`, `Quot.sound`.
* **O-E is a stated limit of the stock arena**: the invariant keeps `end_index` within the first
  node's buffer (`OV.Facts`: `24 + ei ≤ sz`), which a failed `alloc` breaks; the stock arena has no
  `alloc` proof (O-E above).
* `ArenaObstruction.foreign_free_panics` (O-A) and `ArenaObstruction.oob_free_illegal` (O-E),
  from the generated code and `mem0 .fresh`, by kernel evaluation; `arena_oom_free` (`Eval.lean`)
  shows O-E from real runs.
* **One proof, every module.** Each generated module has its own `Tgt` and its own copies of the
  std types, so no generated term of one module is a term of another. The specification is
  therefore one shared layer, generic over the module (`AllocArena/Core.lean`: the invariant, the
  ownership and run lemmas, and the proof tactics `arena_free`, `arena_resize`, `arena_remap`,
  `arena_loadBuf`), and each module states the theorems and proves them with these tactics,
  elaborated against its code (VST-style). The patched `free` and `resize` add a bounds check
  (`arena_free_checked`, `arena_resize_checked`: the invariant keeps `end_index` within the buffer,
  so the check passes).
* The patched arena (`upstream/arena-fix.patch`) is translated from its AIR
  (`air/0.16.0/arena-fixed-linux`, `AllocArena/ArenaFixedLinux.lean`) and equals its native run
  (`expected-fixed.txt`), `check.sh` builds that native run. `arena_fit` is the regression of an
  earlier draft of the patch, which looped forever when a request fit a node whose buffer was
  shorter than the request's reservation.
* `mutant.sh`: an `alloc` whose fast path reserves nothing (the `end_index` bump adds `0`) hands
  out the same bytes twice; `Eval.lean` rejects it at `arena_three` (331 instead of 321: the third
  allocation gets the second one's bytes; two allocations do not show it, the first comes from a
  new node).
* Library rules the entries need (each its own commit): **indirect calls through a read-only
  vtable** (`ZigLean/Sep/Full/Dispatch.lean`, generic over the interface): `callIndirect` is the
  generated chain that tests the loaded function pointer against the program's candidates
  (folded by `rfl` lemmas), `CTriple.callIndirect`/`tableCall` read it by the selected arm,
  `vtR` holds a vtable's entries read-only; for `std.mem.Allocator`, `CAllocSpec.dispatch`: the
  dispatch through a vtable meets the specification of the implementation it selects. The
  named-grant ledger
  (`ZigLean/Sep/Full/Ghost.lean`: `Upd.issue`/`retire`/`reassign`/`bump`, `gfrag_mem`);
  `FTriple.atomicLoadPtr`, `FTriple.cmpxchgHit`, `FTriple.atomicLoadAs`
  (`ZigLean/Sep/Full/AtomicRules.lean`); the `CTriple` step rules `pureStep`, `facts`, `preM`,
  `readStep`, `upd`; and **fixpoint induction for `CTriple`** (`ZigLean/Sep/Full/Conc.lean`): the
  in-thread reading of a chain's least upper bound is an element's (`Sched.soloTree_sup`), so
  `CTriple P · Q` is admissible (`CTriple.admissible`, `_fun`, `_run`) and `partial_fixpoint`'s
  generated `fixpoint_induct` reads a recursive group such as `alloc`'s; `CTriple.loop` is the
  invariant rule for `Zig.loop` (partial correctness, no measure).

Not proved yet, in order:

* The patched arena's `alloc`: fixpoint induction over the `alloc` group with the library rules
  above, the child's `FAllocSpec` through the closed vtable dispatch of the generated code (the
  call site tests the loaded function pointer against every allocator function of the program;
  with the child's vtable read-only, as `Dispatch.vtR`, it selects the child's entry),
  `Upd.issue` under a fresh id for each grant, `defer pushFreeList`. The child's specification
  enters as `CAllocSpec (CVTable.dispatch tables fns) cctx CI` (`Full/Dispatch.lean`).
* `reset` (stock and patched): the precondition gives back every byte of every node (`Covers`);
  `Upd.bump` revokes the outstanding tokens. It walks both lists (`Zig.loop`, `CTriple.loop`) and
  calls the child's `free`/`resize`/`alloc`.
* `not_fallocSpec_arena`: the kernel-checked refutation of O-E above (a concrete child, e.g. the
  256-byte `FixedBufferAllocator` of `arena_oom_free`), which needs the stock `alloc`'s run on
  concrete states (the `partial_fixpoint` group's equations, or `Unroll`-style cut loops).

## Legacy models

The hand-written arena model (`.owned a` blocks, `ZigLean/Sep/ArenaClient.lean`, ALC-07) stays
until the translated arena's specification replaces it ([allocator-model.md](allocator-model.md),
removal plan step 2). In that specification a use after a retaining reset is a permission
violation twice over: `reset` takes back every byte of every node (`Covers`, as for the
`FixedBufferAllocator`'s `reset_spec`), and its epoch bump makes every kept token stale. A `free`
on an arena without a node is a permission violation: there is no token of the current epoch for
it.
