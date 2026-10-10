# The translated `ArenaAllocator` (allocator milestone 2)

Status: translation, executable checks, kernel-checked obstructions and a mutant are done.
`free` is proved against `FAllocSpec` (`ArenaSpec.free_spec`) over an invariant whose tokens are
ghost tokens of the arena's current epoch, which closes O-A; O-F is closed by live-block
disjointness in the memory invariant. `resize`, `remap`, `alloc` and `reset` are not proved yet
(§What is proved). Fixture:
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
`reset(.free_all)`) panics for every slice. So `own ⋆ granted p k bs` must be unsatisfiable there:
the token must record that this arena issued a region in its current generation.
**Resolved by ghost state** ([sep-full-state.md](sep-full-state.md) §Ghost state): `own` holds the
authority `gauth γ e n` of an epoch ledger (`n` grants of epoch `e` outstanding, `n = 0` without a
first node), and the token is `gfrag γ e`. A token of the current epoch shows `n ≥ 1`
(`gfrag_count`), so the arena has a node (`ArenaSpec.free_pre`). `reset` will bump the epoch
(`Upd.bump`): tokens the client kept become stale, and a stale token belongs to the invariant of an
older epoch, whose `own` no longer exists. A foreign slice has no token of the current epoch.

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
caller does not own. **Resolved by stage 3** of [sep-full-state.md](sep-full-state.md): live
blocks have disjoint address ranges in every `Mem.FSeq` memory (`Mem.LiveDisjoint`), and
`Holds.apart` turns ownership of a byte in each of two blocks into disjoint ranges. A slice of
another block never matches; a slice of the node's block that ends at `buf_ptr + end_index` lies
past the header, which `own` holds (`ArenaSpec.region_apart`). No premise per triple.

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

* `ArenaSpec.free_spec` (`tests/roadmap/alloc-arena/ArenaSpec.lean`): the translated `free`
  (x86_64-linux) meets `FAllocSpec`'s `free` field, `FLogic.partial.T (I.own ⋆ I.granted s.ptr k bs)
  (Sched.soloRun fuel free) (fun _ => I.own)` with `I = inv CI γ e ctx`, for every child invariant
  `CI`, epoch `e` and depth `fuel`, from the generated code only. The invariant (`own`): the arena
  struct with `used_list`/`free_list` as pointer-valued atomic words, the epoch ledger's authority,
  the first node (header words, the child's token, the unused tail of its buffer), the other used
  nodes and the free list as `next`-linked chains, the child's `own`, and `Junk` (bytes that frees
  of earlier allocations leaked back). On a match the slice's bytes rejoin the tail and
  `end_index` moves back (`FTriple.cmpxchgHit`); otherwise they become junk. Either way the token
  is retired (`Upd.retire`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.
* **O-E is a stated limit, not a premise per triple**: the invariant keeps `end_index` within the
  first node's buffer (`FirstNode`: `24 + ei ≤ sz`). A successful `alloc` returns to such a state;
  a failed one leaves `end_index` past the buffer, so the reachable states covered end at the first
  failed `alloc`.
* `ArenaObstruction.foreign_free_panics` (O-A) and `ArenaObstruction.oob_free_illegal` (O-E),
  from the generated code and `mem0 .fresh`, by kernel evaluation.
* `mutant.sh`: an `alloc` whose fast path reserves nothing (the `end_index` bump adds `0`) hands
  out the same bytes twice; `Eval.lean` rejects it (`arena_two`: 22 instead of 21).
* The atomic rules the entries need beyond the earlier ones (`ZigLean/Sep/Full/AtomicRules.lean`):
  `FTriple.atomicLoadPtr` and `FTriple.cmpxchgHit`.

Not proved yet, in order:

* `resize` and `remap` (`remap` is `resize` and returns `memory.ptr`). The no-match and shrink paths
  follow `free` (the cut bytes go to the tail or to `Junk`, the token stays). The growth path reads
  the node's `size` word through `Node.loadBuf` (`atomicLoadAs` of the packed `Node.Size`, then
  `toInt`); it needs the `size` word as an integer `apts` in `Header` (it is `aptsE` now) and the
  bit-level fact that clearing the `resizing` bit of an even size is the size.
* `alloc`: `CTriple` rules for the generated loops (`Zig.loop`), an equation-based reading of the
  `partial_fixpoint` group (the child dispatch includes `ArenaAllocator.alloc`), the child's
  `FAllocSpec` with the bounded-child premise of O-B/O-C, and `Upd.issue` for each grant.
* `reset`: the precondition gives back every byte of every node (`Covers`); `Upd.bump` revokes the
  outstanding tokens.

## Legacy models

The hand-written arena model (`.owned a` blocks, `ZigLean/Sep/ArenaClient.lean`, ALC-07) stays
until the translated arena's specification replaces it ([allocator-model.md](allocator-model.md),
removal plan step 2). In that specification a use after a retaining reset is a permission
violation twice over: `reset` takes back every byte of every node (`Covers`, as for the
`FixedBufferAllocator`'s `reset_spec`), and its epoch bump makes every kept token stale. A foreign
free is a permission violation: there is no token of the current epoch for it.
