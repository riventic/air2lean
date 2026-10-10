# The translated `ArenaAllocator` (allocator milestone 2)

Status: translation, executable checks, kernel-checked obstructions and a mutant are done. The
specification is not proved (obstructions O-A to O-F below). Fixture:
[`tests/roadmap/alloc-arena`](../tests/roadmap/alloc-arena/README.md). The plan and the earlier
milestone: [alloc-spec.md](alloc-spec.md), [allocator-model.md](allocator-model.md),
[alloc-page.md](alloc-page.md).

`std.heap.ArenaAllocator` is translated from its own AIR (Zig 0.16.0), its child allocator
included: an ordinary indirect call through `child_allocator.vtable`. As with the page allocator,
only `posix.mmap`/`munmap`/`mremap` are trusted (OSM-01), and there is no model of the arena.

## Versions

| Zig | `lib/std/heap` | status |
|---|---|---|
| 0.16.0 | `ArenaAllocator.zig`: lock-free (`used_list`/`free_list` atomics, `end_index` bumped by `@atomicRmw .Add`, `Node.Size` packed with a `resizing` bit) | translated (x86_64-linux, aarch64-macos) |
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
statement.

**O-A: a foreign or stale `free` on an empty arena panics** (kernel-checked:
`ArenaObstruction.foreign_free_panics`; natively `panic: attempt to use null value`).
`free` and `resize` start with `loadFirstNode().?`. An arena without a node (fresh, or after
`reset(.free_all)`) panics for every slice. An invariant that holds for an empty arena must
therefore make `own ⋆ granted p k bs` unsatisfiable there: the token must record that this
arena issued the region in its current generation. Full-state resources have owned bytes and
duplicable block knowledge only (`ZigLean/Sep/Full/Res.lean`), so a token cannot be revoked by a
reset. This needs ghost state: an authoritative node set in `own` and a fragment per region in
`tok`. Without it, the entries are specified for an arena that has a node (`used_list = some N`).
There any slice is harmless: a region of another block never matches the first node's end (the
pointer comparison sees the block), and a region of the node's block that ends at `end_index`
cannot start inside the header, which `own` holds.

**O-E: after a failed `alloc`, `free` and `resize` form an out-of-bounds pointer**
(kernel-checked: `ArenaObstruction.oob_free_illegal`; [upstream draft](upstream/arena-oob-gep.md)).
A request that does not fit leaves the first
node's `end_index` past its buffer. If the child then fails, `alloc` returns `null` with that
node still first. `free`/`resize` compute `buf_ptr + cur_end_index`, which is
`getelementptr inbounds` natively, and branch on its comparison: undefined behaviour in LLVM,
illegal behaviour in Zig. With the in-bounds projection rule of the memory model (MM-3,
`Zig.ptrProject`) the translated code is `.illegal` there. `arena_oob_free` builds that state by hand (a node with `end_index` past its 64 bytes) because the
kernel does not evaluate the translated `alloc`, which is a `partial_fixpoint` group: the child
dispatch includes `ArenaAllocator.alloc` itself. So no invariant that admits the state
that a failed `alloc` leaves satisfies `FAllocSpec`. The specification can hold only for states
in which the first node's `end_index` is within its buffer. That is every state that a
successful `alloc` returns to, but `alloc` cannot keep it after an out-of-memory failure.

**O-F: deciding a foreign slice needs live-block disjointness.** `free` and `resize` compare
`buf_ptr + end_index` with `memory.ptr + memory.len` by address (`Zig.ptrEqAddr`, MM-1). For
a slice in another block, equal addresses would make `free` give back bytes of the node that the
caller does not own. Zig rules this out: live objects have disjoint storage, and the placement
oracle places every block clear of the live ones. But the triple's memory invariant `Mem.FSeq`
does not carry that (`Mem.LiveDisjoint` and `Holds.apart` exist; adding them to `FSeq` is
stage 3 of [sep-full-state.md](sep-full-state.md)). With it, a slice that ends at the node's
end lies in the node's block, past its header (which `own` holds). So `free` and `resize` are
specifiable for an arena with a node, with `tok = emp`.

**O-B: unbounded node growth overflows.** A new node has size
`alignForward(big + big / 2, 2)` with `big = prev_size + @sizeOf(Node) + alignment + n + 16`,
and the in-place growth asks for `@sizeOf(Node) + aligned_index + n`, all overflow-checked.
Node sizes come from the child, and `FAllocSpec` does not bound what a child grants, so a child
that grants every request lets the arena reach a node size where these sums overflow and panic.
A bound on the child's grants (as the OS boundary gives the page allocator, O5) is a premise.

**O-C: the child's `fits`.** The arena asks its child for sizes that depend on its state
(`prev_size`, the bumped `end_index`), not only on the request. A child specification covers only
requests within `CI.fits`, so the premise is that the child admits every size up to its bound,
at alignment `@alignOf(Node) = 8`.

**O-D: one thread.** The atomic rules (`ZigLean/Sep/Full/Atomic.lean`, `AtomicPtr.lean`,
`AtomicRules.lean`) read an atomic op with the oracle's choice `0`, as one thread does. A
multi-threaded specification of the lock-free code (the `resizing` bit as a lock, the stolen
free list) is not attempted.

## What is proved and checked

* `ArenaObstruction.foreign_free_panics` (O-A) and `ArenaObstruction.oob_free_illegal` (O-E),
  from the generated code and `mem0 .fresh`, by kernel evaluation.
* `mutant.sh`: an `alloc` whose fast path reserves nothing (the `end_index` bump adds `0`) hands
  out the same bytes twice; `Eval.lean` rejects it (`arena_two`: 22 instead of 21). This is an
  executable rejection, not a failed proof: there is no `alloc` proof yet.
* The atomic rules the entries need beyond the earlier ones (`ZigLean/Sep/Full/AtomicRules.lean`):
  `FTriple.atomicLoadPtr` (an atomic load of an owned pointer word, any order) and
  `FTriple.cmpxchgHit` (a strong 64-bit `cmpxchg` that finds the expected value).

The fixture is ported to the hardened memory model (`codex/alloc-milestone1`: placement,
in-bounds projections, `checkAlign`, pointer equality by address). Not yet proved: `free`,
`resize` and `remap` for an arena with a node (need O-F's stage 3), and `alloc` and `reset`. These
also need rules that do not exist yet: `CTriple` rules for the generated loops (`Zig.loop`), and an
equation-based reading of the `partial_fixpoint` group.

## Legacy models

The hand-written arena model (`.owned a` blocks, `ZigLean/Sep/ArenaClient.lean`, ALC-07) stays
until the translated arena's specification replaces it ([allocator-model.md](allocator-model.md),
removal plan step 2). In that specification a use after a retaining reset is a permission
violation: `reset` takes back every byte of every node (`Covers`, as for the
`FixedBufferAllocator`'s `reset_spec`), so the caller keeps no region of the arena. A foreign
free is one only with ghost tokens (O-A); without them a foreign slice must be harmless, which
it is for an arena that has a node.
