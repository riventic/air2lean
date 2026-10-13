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
  bytes, and `Node` points to itself (`next: ?*Node`). The capability scan of a cast's pointee
  (`castErrorCapability`, `Air2Lean/Check.lean`; every allocator model) counts reachable error
  storage, so a type met again on the path adds nothing. Where that scan does not finish (the
  `*anyopaque` fields below), it falls back to the bounded closed-graph proof that global aliases
  already use (`closedErrorFreeAliasGraph`): no type reachable from the pointee is an error set or
  error union. A cyclic cast that reaches an error union stays rejected (`test_cli.py`).
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
a first node), and the token of the slice at `p` of `n` bytes is `∃ i, gfrag γ e i (p, n, q, A, K, φ)`
(with the lent fraction `q`, the cells' address and kind labels `A`, `K` and the fee `φ`,
[sep-full-state.md](sep-full-state.md) §The fee of a grant). A
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
by hand (`oob_free_illegal`); `not_fallocSpec_arena` below reaches it by the arena's own `alloc`.

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
(no premise per triple, no budget). **Kernel-checked** (`ArenaObstruction.not_fallocSpec_arena`)
for the child of `arena_oom_free`: for every invariant `I` with `CAllocSpec vt arena I` whose `fits`
admits 8 and 4096 bytes, `I.own` does not hold, with any frame, in the memory right after
`init`: its `alloc` and `free` triples compose into a triple of the client `alloc(8)`, `alloc(4096)`, `free`
(`client_ct`), whose run from that memory the kernel computes to `.illegal` (`client_illegal`,
`unroll_solo` cutting the arena's `partial_fixpoint` group; the memory is `Mem.FSeq` by
`decide`). The fix is in the arena: the patch gives the reservation back when the request does
not fit and makes the overflowing sizes fail instead of panicking.

**O-F: deciding a foreign slice needs live-block disjointness.** `free` and `resize` compare
`buf_ptr + end_index` with `memory.ptr + memory.len` by address (`Zig.ptrEqAddr`, MM-1). For
a slice in another block, equal addresses would make `free` give back bytes of the node that the
caller does not own. **Resolved by stage 3** of [sep-full-state.md](sep-full-state.md): live
blocks have disjoint address ranges in every `Mem.FSeq` memory (`Mem.LiveDisjoint`), and
`Holds.apart` turns ownership of a byte in each of two blocks into disjoint ranges. A slice of
another block never matches; a slice of the node's block that ends at `buf_ptr + end_index` lies
past the header, which `own` holds (`Core.lo_of`). The comparison needs no bytes of the slice:
the slice's block reaches its end by the grant's extent share (`Core.last_dec`), so the refined
`resize` (the client gives no bytes for a growth) decides it too. No premise per triple.
`last_dec` compares only bytes known to be live: the first node's last byte before
`buf + end_index` lies past its own `next` word, and the slice's last byte lies past the `next`
word of the node it was granted from (`GrantOk`: a grant starts past its node's header), both
owned by the arena. A memory model in which the low part of a block is not live (a thread's
stack mapping below its stack pointer, MM-19) needs exactly that.

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

**O-G: in-place growth of a node with outstanding grants.** The patched `alloc` grows its first
node in place through the child (`child_allocator.rawResize(node, …)`) while clients hold grants
inside it. `FAllocSpec.resize` needs the region's bytes, which the arena does not own, and frame
cells record their block's size. With `page_allocator` as the child, `mremap` growth in place
changes the size that the clients' cells record. So the arena's `FAllocSpec.alloc` fails for
every invariant, although natively nothing is wrong. Resolution (approved; the model, the Full
layer, the FixedBufferAllocator, the page allocator and the arena's `free`/`resize`/`remap` are
done): size-free cells and extent resources, and a stronger `FAllocSpec` whose grants carry a
share of their block's extent ([sep-full-state.md](sep-full-state.md) §Block extents, with
phases). The patched `alloc` proof waits for the remaining phases.

**O-H: the address space ended at `2^64` in the model (found in step 7; fixed in the model).**
`alloc`'s fast path computes `alignedIndex(buf.ptr, end_index, alignment)`: `addr +% end_index`
(wrapping), then `Alignment.forward`, whose `x + (alignment - 1)` is overflow-checked
(`Zig.add false`: `.overflow`, a panic). The old memory model let a block end exactly at `2^64`
(`Mem.placeOk`: `A + size ≤ 2^64`; the fallback `alignUp m.top align` was not bounded at all), and
nothing in `Mem.FSeq` or the arena's invariant bounded a node's address. Scenario: a
`FixedBufferAllocator` child whose buffer global is placed so that a node's buffer ends at `2^64`
(placement `σ` of `mem0 σ`); allocations of alignment `1` leave `end_index = buf.len - 3`; then
`alloc(1, alignment 8)` passes the patched reservation check (`1 + 7 ≤ buf.len`) and
`alignedIndex` adds `7` to `2^64 - 3`: overflow, a panic. So `FAllocSpec.alloc` failed for every
arena invariant in such memories, stock or patched. Natively the state does not exist (user
addresses end below `2^47`/`2^48`).

Fix (coordinator decision 2026-10-12: in the model, one mechanism for every block kind, not an
`FAllocSpec` premise): the placement carries the end of the user address space,
`Placement.addrLimit` (at most `2^63` for every placement, `2^47` by default; SEM-07). `Mem.placeOk`
takes a proposal only if the block ends at or below it, and `Mem.roomFor` checks the fallback
after `Mem.top` against it. An allocation without room fails as for an exhausted address space:
`rawAlloc` returns null, `mmap`/`mremap` fail with `ENOMEM` (OSM-01, `Os.Target.addrLimit`), and
`alloc` throws `.stackOverflow` (STK-01; partial triples read it as non-termination). Every primitive keeps the live blocks below `2^63`
(`Mem.LiveBounded`, proved per primitive with `Mem.LiveDisjoint` in `LDMono`, part of `Tame`), so
the full-state invariant `Mem.FSeq` (its third part is now `Mem.LiveLayout`, both properties)
gives every node `addr + end_index + 2^k - 1 < 2^64` for `k < 64`. It is a consequence of the
model, not a premise of a triple. Kernel-checked regression (`ArenaObstruction.lean`):
`aligned_index_overflows` (the old state panics), `memTop_unbounded` (that state is outside
`Mem.FSeq`), `node_buf_low` and `aligned_index_ok` (a placement proposing `2^64 - 64` for
`node_buf` no longer gets it, and `alignedIndex` on the memory it does get succeeds).

**O1: two nodes of one child block need not be disjoint (found in step 8 (reset); library fix in
progress).** `reset` gives the nodes back to the child one by one, and the child's `free` needs
each node's whole region. But nothing in `own` said that two used nodes in one child block are
disjoint: with a `FixedBufferAllocator` child, nodes `[x, x+64)` and `[x+32, x+96)` of one buffer
were consistent with the invariant, because the old nodes' bytes are held by clients and
`FAllocSpec` related nothing between a new child grant and the outstanding ones. Coordinator
decision O1 (2026-10-12): **byte-range claims** next to the extent shares
([sep-full-state.md](sep-full-state.md) §Byte-range claims). A grant will carry the exclusive
claim on its bytes, tagged with the allocator's tag; two claims of one active world on one byte
make the ghost state invalid. Done: the library (`ZigLean/Sep/Full/Claims.lean`: `bclaim`,
`bcrcpt`, `pclaim`, split/join, `Holds.bclaim_disjoint`, `FTriple.mintClaim`) and the kernel-checked
regressions `tests/roadmap/sep-full/ClaimsCX.lean` (`overlap_invalid`; `arena_nodes_disjoint`: the
O1 scenario is impossible); `FAllocInv.granted` carries the claim (a client still gets exclusive
bytes, now also the claim: `FAllocSpec` is not weakened); in `resize` the claims follow the bytes
(`I.relBytes`, `I.newBytes`; [sep-full-state.md](sep-full-state.md) §Byte-range claims), so that
the arena can grow a node with grants in place (O-G); the FBA and page allocators are re-proved by
`fsym` with claims in their invariants.

The arena's claims (`AllocArena/Core.lean`). The child gives each node with its claim tagged
`CI.tag`. A used node keeps the claim on its header and lends the claim on its buffer as the
arena's claim of epoch `e` when the node is pushed (`EUpd.plendC`, `push_cls`), keeping the receipt
(`NodeCl`). The first node holds the lent claim on its unused tail (`TailCl`). `alloc` carves a
grant's claim from it and drops the padding's claim. `free` or a shrink of the first node's last
grant joins the claim back (`tailCl_join`). A growth carves the new bytes' claim from the tail. Any
other `free` or shrink drops the released claim. A node grown in place gets the child's claim on
the new bytes and lends it into the tail (`grow_cls`). A free-list node holds its whole claim
(`FreeCl`). Next: `reset`, which revokes the receipts (`EUpd.prevokeC`) and gives the child back
the claim on each whole node.

**O-D: one thread.** The atomic rules (`ZigLean/Sep/Full/Atomic.lean`, `AtomicPtr.lean`,
`AtomicRules.lean`) read an atomic op with the oracle's choice `0`, as one thread does. A
multi-threaded specification of the lock-free code (the `resizing` bit as a lock, the stolen
free list) is not attempted.

## What is proved and checked

* `ArenaSpec.free_spec`, `resize_spec`, `remap_spec` (`tests/roadmap/alloc-arena/ArenaSpec.lean`;
  `ArenaSpecMacos.lean` for aarch64-macos, `ArenaSpecFixed.lean` for the patched arena):
  the arena's translated `free`, `resize` and `remap` meet `FAllocSpec`'s
  fields, e.g. `FLogic.partial.T (I.own ⋆ I.granted s.ptr k bs) (Sched.soloRun fuel free) (fun _ =>
  I.own)` with `I = inv CI γ e ctx`, for every child `CI`, epoch `e` and depth `fuel`,
  from the generated code only. **The child** (`Core.Child`) is the child allocator's invariant
  together with its identity: the context pointer `cctx` and the vtable `vtp` with its entries
  `fns`, which `alloc` and `reset` call. The invariant (`own`): the arena struct, whose first 16
  bytes are the child allocator `(cctx, vtp)` (`Child.bytes`, the `std.mem.Allocator` encoding),
  the child's vtable as persistent knowledge (`vtR vtp fns`), `used_list`/`free_list`
  as pointer-valued atomic words, the epoch ledger's authority `gauthP γ e M CI.tag` (`M`: the
  grants of this epoch, each with its lent fraction; empty without a first node; the ledger's
  parent is the child's tag), the first node (header words: `size` and `end_index` as integer
  atomic words, `next`; the child's token with the fraction `qn` it lent; the part `qh` of the
  node's extent share that the arena keeps; the unused tail of its buffer), the other used nodes
  and the free list as `next`-linked chains (each with its token and kept share), the child's
  `own`, the junk as an exact heap `JunkAt jh` (bytes that frees of earlier allocations, shrinks
  and `alloc`'s padding leaked back), one receipt per grant together with the grant's fee
  (`LedgerRcpts`, `ledgerRcpt`; the receipt at any bound) and the pool of shares that frees gave back
  (`Pool`). The ledger, its receipts and the fee are the generic reset ledger
  (`ZigLean/Sep/Full/ResetLedger.lean`, [sep-full-state.md](sep-full-state.md) §The fee of a
  grant); the arena is an instance of it (`Core.ledger`). The fee is
  `epFee γ e φ = epTok γ e φ ⋆ ⟪0 < φ⟫`, a nonzero part of the epoch token
  ([sep-full-state.md](sep-full-state.md) §The fee of a grant). The token of a
  grant names it with its fraction, its cells' labels and its fee: `∃ i, gfrag γ e i (p, n, q, A, K, φ)`;
  every grant lies in the block of a used node with that node's labels (`GrantOk`; the used nodes
  after the first are an explicit list of node records, `NodeV`); the grant's share is tagged with
  the epoch (`FAllocInv.tag = some (γ, e)`), so a reset can revoke it.
  * **Block extents** ([sep-full-state.md](sep-full-state.md) §Block extents). A cell no longer
    records its block's size, so the node's size comes from its extent share: the child's grant
    carries `pshare N qn (N.off + sz) CI.tag` (the stronger `FAllocSpec`), and the arena keeps a
    part of it. The share is true while its tag is active, which the child's state witnesses
    (`FAllocInv.act`, an obligation of every allocator invariant: automatic for an untagged child,
    and for an arena from its own ledger and its child's `act`, so an arena over an arena works
    the same way). O-F (the slice ends at `buf + end_index` only if it lies in the first node)
    uses the slice's and the node's extent shares and `Mem.LiveDisjoint.addr_ne` (two live blocks
    share no byte address): `last_dec`. A last grant carries the first node's labels
    (`last_labels`: `GrantOk` and the owned headers of two nodes in one block), so bytes that
    rejoin the node's tail are relabeled as the node's (`EUpd.relabel`: a cell's size is a label,
    its kind counts up to `BlockKind.norm`), and the new bytes of a growth carry the grant's.
  * `free`: on a match the slice's bytes rejoin the tail and `end_index` moves back
    (`FTriple.cmpxchgHit`); otherwise they become junk. Either way the grant's share goes back
    against its receipt into the pool (`EUpd.returnTw`: weakened to the receipt's bound first),
    the grant is retired (`Upd.retire`) and its fee goes back to the client: `ledger_return`.
  * `grant_return`: the same as a `free` of a grant that is not the last one, as a ghost update
    (no code runs): the grant's bytes become junk and the client gets the fee back. With every
    grant back, the client holds the whole epoch token `epTok γ e 1` again, and next to it the
    arena's state has no grant (`own_epTok_empty`, from `gauth_epTok_whole`: each grant's fee is a
    nonzero part of that token). A client with an outstanding grant cannot hold it
    (`granted_epTok_false`).
  * `resize` meets the refined field (`FAllocSpec.resize`: the token, a part `q'` of the grant's
    share, and only the bytes `[n, len)` a shrink releases): a slice that is not the first node's
    last one only shrinks (released bytes to junk); the last one moves `end_index` back (released
    bytes rejoin the tail) or into the tail when it has room (`Node.loadBuf` reads the `size` word:
    `FTriple.atomicLoadAs`; clearing the `resizing` bit of an even size is the size:
    `toInt_ofBits`), handing the client the new bytes. A successful resize re-points the grant at
    the new length (`Upd.reassign`); a shrink weakens the bound of the client's part of the share
    (`ledger_shrink`); a growth takes back the part `q'` the client gives against a split of the
    grant's receipt, joins it into the node's kept share, lends it again at the new end and joins
    the receipts at the lower bound (`ledger_regrow_rcpt`: `brcpt_split`, `EUpd.returnTw`,
    `EUpd.lendT`, `EUpd.rjoin`; `ledger_regrow`). The arena needs no `q' = q` for a shrink (it never
    shrinks a block itself). `remap` is the whole-region `resize` (`resize_granted_ct`,
    `FAllocInv.resize_granted_of`) and returns `memory.ptr`.
  * **Coverage of the nodes' buffers** (for `reset`, which must give each node's whole region to
    the child's `free`): `OV.Facts` keeps `OV.Cov`, every byte of every used node's buffer is in
    the junk's heap `jh`, in a grant of `M`, or in the first node's unused tail (`OV.Avail`). Each
    update keeps it (`OV.avail_shrink`, `OV.avail_step`, `OV.Cov.step`): a `free` or shrink moves
    the released bytes to the junk (`junk_grew`, from `junkAt_absorbR`) or back to the tail, a
    growth and `alloc` carve them out of the tail, the padding and an old first node's tail join
    the junk (`JunkTook`), a node grown in place extends the tail. With no outstanding grant a
    reset turns each buffer's junk back into a region (`EUpd.junkRegion`).
  * **Fraction accounting per block** (for `reset`, which must give each node's whole share
    `qn` back to the child): the arena's variables name the grant map's bound `mN` and the pool's
    pieces (`Pool t pn pf`), and `OV.Facts` keeps, for every block `b`, `ndLent b nodes =
    poolOn b + grantsOn b` (the used nodes' lent parts `Σ (qn - qh)` are the pool's and the
    grants' fractions on `b`; several nodes may share a block, e.g. a `FixedBufferAllocator`'s
    buffer), `qh ≤ qn` per used node, and `qh = qn` on the free list. `free` moves the grant's
    fraction to the pool (`acct_free`), `resize` keeps the sums (`acct_repoint`; a growth
    restores `qh`).
  * **The ends of `alloc`** (resource updates, not yet used by a proof of the code):
    `alloc_carve_upd` (a grant from the first node's tail: padding to junk, half the node's kept
    share lent at the grant's end, `Upd.issue` at `mN`, accounting), `push_node_upd` (a node from
    the child or the free list becomes the first node; the old one joins the used nodes, its tail
    leaks), `grow_node_upd` (O-G: the child grew the first node in place through the refined
    `resize` from the token and the kept part `qh`, no bytes; the new bytes join the tail, the
    node's regions take the new labels).
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
  ownership and run lemmas, the resource updates that end each branch (`free_last_upd`,
  `free_other_upd`, `resize_shrink_upd`, `resize_grow_upd`, `resize_other_upd`,
  `resize_false_of`), and the proof tactics `arena_free`, `arena_resize`, `arena_remap`,
  `arena_loadBuf`, which walk the generated code), and each module's file states the theorems with one command
  (`arena_spec_statements`, `checked` for the patched arena) and proves them with these tactics,
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
  `vtR` is persistent knowledge of a `const` vtable's entries (below); for `std.mem.Allocator`,
  `CAllocSpec.dispatch`: the
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

**The child's vtable is knowledge, not ownership** (`codex/const-global-know`,
[sep-full-state.md](sep-full-state.md) §Const globals). `own` holds the child's vtable as
`vtR vtp fns.toList`: persistent knowledge of the `const` global's entries
(`ZigLean/Sep/Full/Const.lean`), duplicable (`vtR_dup`) and read without being consumed
(`vtR_load`, `vtR_project`). So a client that holds the arena and another allocator with the same
child vtable (or the child itself through its own handle) frames both in; the exclusive form
`up (vtOwn …)` cannot be held twice (`ConstKnow.vtOwn_twice`). The model fact behind it: a `const`
global is never written (`Mem.accessW`) or freed (`Zig.free` of one is `.illegal`, a model
correction). No arena, FBA or page statement mentioned `vtR`. `vtR` changed type (it was an
`Assn` under `up`, it is now an `FAssn`): the old exclusive predicate and its rules are `vtOwn`,
`vtOwn_load`, `vtOwn_project` with unchanged statements, so a client written against
`up (vtR …)` switches to `up (vtOwn …)` or to the persistent `vtR` (`vtR_intro`); the arena's
`own` holds the persistent `vtR CI.vtp CI.fns.toList` of its child (`Core.Child`).

Not proved yet, in order:

* The patched arena's `alloc` (after O-G's resolution, [sep-full-state.md](sep-full-state.md)
  §Block extents): fixpoint induction over the `alloc` group with the library rules
  above (`stealFreeList`: `FTriple.atomicXchgPtrW`; `pushFreeList`: `FTriple.cmpxchgWeakPtrW`;
  `endResize`'s assert: `FTriple.atomicLoadUnorderedAsW`). A new node's header comes from the child as a plain region (`up`, any atomic layout); the
  atomic rules apply to it once its tag constraints are dropped (`FTriple.untag`, `wpts_of_up`;
  atomic tags are constraints, [sep-full-state.md](sep-full-state.md) §Atomic tags are
  constraints), so the invariant's header words can be any owned words (`wpts`), and the RMW rules
  exist (`FTriple.atomicRmwW`, `atomicRmwAsW`, `atomicStoreAsW`); the child's `FAllocSpec` through the closed vtable dispatch of the generated code (the
  call site tests the loaded function pointer against every allocator function of the program;
  with the child's vtable as persistent knowledge, `vtR`, it selects the child's entry),
  `Upd.issue` under a fresh id for each grant, `defer pushFreeList`. The child's specification
  enters as `CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv`
  (`Full/Dispatch.lean`), for the child `CI : Core.Child` that the invariant names.
* `reset` (stock and patched): `{own e ⋆ epTok γ e 1} reset {own (e + 1) ⋆ epTok γ (e + 1) 1}`.
  **Ghost part done** (`AllocArena/Reset.lean`, `reset_release`): from `own e ⋆ epTok γ e 1` to
  `Released`: the ledger at epoch `e + 1` with no grant and that epoch's whole token, the child
  with the reservoir, junk, and both lists as lists of whole nodes (`FreeList`: header, whole
  buffer, the child's token, the whole share `qn` and the whole claim). The used nodes are
  pairwise disjoint because the arena holds each one's whole claim after `cls_revoke`
  (`freeCl_pairwise`), which the junk conversion of each buffer needs (`chainH_junk`). Open: the
  walk of the code. It does plain loads and stores of words the invariant owns as atomic words
  (`end_index = 0`, the list heads, `arena.state = .init`) and a typed load and store across the
  struct's region and its two atomic words. These need library rules that keep a word's atomic
  layout constraint under a plain access (the model's `Res.writeAt`/`Holds.write` keep it); the
  rules are in the engine lane's queue.
  **The child's fee** (coordinator decision 2026-10-13): the arena pays its child's fee for each
  node, so `own` keeps a reservoir of it, `Child.cown = CI.own ⋆ ∃ φc > 0, CI.fee φc`. The arena's
  creator supplies the reservoir; it is the arena's share of its child's fee. A node's fee is
  half of the reservoir (`FAllocInv.fee_half`, from the obligation `FAllocInv.fee_add` that every
  allocator's fee is fractional), and the child's `free` of a node refunds into it
  (`FAllocInv.fee_join`). This matters for the retaining modes, which call the child's `alloc`
  before they free the old node. For a child without a fee the reservoir is `emp`.
  The whole epoch token shows that no grant is outstanding (`own_epTok_empty`), so every byte of
  every node is junk or the first node's tail (`OV.Cov`) and turns back into a region
  (`EUpd.junkRegion`); `Upd.bump` mints the next epoch's token (the old one is dropped,
  `EUpd.dropEp`), the receipts and claims revert to the nodes (`reset_shares`, `cls_revoke`). It
  walks both lists (`Zig.loop`, `CTriple.loop`) and calls the child's `free`/`resize`/`alloc`. The
  bytes cannot be left out: revocation withdraws only ghost state, and **no**
  `{I.own} reset(.free_all) {I'.own ⋆ I'.fee φ}` holds next to `FAllocSpec`s `I`, `I'` with `I.own`
  true after `init` (kernel-checked, `ArenaObstruction.not_reset_own`: an `alloc(8)`, `reset`,
  `alloc(8)` client would hold two separate grants that the run puts at one byte of the child's
  buffer). The client gives its grants back without tracking the grant map: by `free` or by the
  ghost `grant_return`, each of which refunds the grant's fee; a client that keeps a grant cannot
  call `reset` (`granted_epTok_false`), and a leaked grant blocks `reset` for good.

## Legacy models

The hand-written arena model (`.owned a` blocks, `ZigLean/Sep/ArenaClient.lean`, ALC-07) stays
until the translated arena's specification replaces it ([allocator-model.md](allocator-model.md),
removal plan step 2). In that specification a use after a retaining reset is a permission
violation twice over: `reset` takes back every byte of every node (`Covers`, as for the
`FixedBufferAllocator`'s `reset_spec`), and its epoch bump makes every kept token stale. A `free`
on an arena without a node is a permission violation: there is no token of the current epoch for
it.
