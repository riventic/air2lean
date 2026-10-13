# Separation logic over the full state

Status: proof-only modules in `ZigLean/Sep/Full/`: the prototype (`Res`, `Triple`, `Atomic`)
and migration stages 1 and 2 (`Logic`, `AllocSpec`, `Tame`, see §Migration). `ZigLean.lean` does
not import them, and no existing rule changes. CI builds them (`Full-state separation logic`). The
axioms are `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, `admit` or
`native_decide`.

## The problem

`Assn := Heap → Prop`, and `Mem.heap` holds only the live bytes. `Triple` quantifies over every
`Mem.Seq` memory whose live bytes split into the precondition's part and a frame, so nothing
outside the live bytes can be constrained or kept. The P4b PageAllocator work
(`docs/alloc-page.md`, `tests/roadmap/alloc-translated/PageObstruction.lean` on
`codex/alloc-translated-p4-page`) proved that this rules out real programs:

| | what the program reads | why no `Assn` can constrain it |
|---|---|---|
| O3 | the atomic layout under `addr_hint` (`locIdx` throws `.unspecified` for a location of another size) | `Mem.atomics` is outside the heap |
| O1 | `@intFromPtr` of the hint after its mapping was unmapped (`ptrAddr` needs the dead block's metadata) | dead blocks are outside the heap |
| O2 | the size of the mapping behind a granted region | `granted` hid the block (fixed on `codex/alloc-translated-p4-fba`: `tok p n k A S K`) |

The FixedBufferAllocator proof on `codex/alloc-translated-p4-fba` ran into the same gaps. It
calls `@intFromPtr(buffer.ptr + end_index)` when every buffer byte is lent out, so its proof keeps
a "pin" byte to know the block. Its generated `@memcpy` overlap checks also need the address
ranges of distinct live blocks to be disjoint, which `Mem.Seq` does not provide (today this is a
placement premise).

These gaps are not specific to allocators. Any program that uses atomics on ordinary memory, or
keeps integer or pointer handles to freed memory, has the same problem.

## The design: full-state resources

A resource (`Res`, in `ZigLean/Sep/Full/Res.lean`) has two parts.

1. **Owned bytes with a constraint on their atomic layout.** `heap : FHeap` maps each location
   to an `FCell`, which is the legacy `Cell` plus `atom : Option (Nat × Nat)`, a **tag
   constraint** (§Atomic tags are constraints): `some (o, len)` says that the atomic location
   covering the byte (`tagOf (shapes m)`) is `(o, len)` or that there is none; `none` says nothing.
   * The frame rule keeps the frame's constraints true.
   * A precondition can require the layout that an atomic op leaves. The atomic points-to is
     `apts p v`: the 8 bytes at the 8-aligned `p` hold `v`, and their constraint is `(p.off, 8)`.
   * An atomic op on owned bytes, whatever their layout, creates or reuses a location over those
     bytes only, and may retire locations over them (`retireAt`); retiring only removes
     locations, so every frame constraint stays true. The rules take any owned word
     (`wpts`, any constraint) and leave an `apts`.
2. **Persistent block knowledge.** `know : Know` is a set of pairs `(b, A)`. The assertion
   `known b A` means "block `b` exists and has address `A`".
   * Block ids are never reused, and a block's address never changes. `free` flips `live`; on P2,
     `munmap` trims `kind` and `mremap` grows `bytes`. So the fact stays true in every later
     memory (`KMono`), including after `free`.
   * It is knowledge, not ownership. It is duplicable (`known_dup`), owns no bytes, and composes
     by union.
   * It is not droppable by entailment (`emp` has no knowledge). Instead the triple rule
     `FTriple.drop` forgets it, which keeps `emp` an exact unit.

A memory holds `r` with frame `rF` (`Holds`) when two things are true:

* `r.heap ∪ rF.heap` matches `m` (`FMatch`): its cells are exactly `m`'s live bytes, each byte
  meets its tag constraint (`TagSat`), and the two heaps are disjoint;
* both knowledge sets are true in `m`, i.e. contained in `Mem.kn m` (every block, live or dead,
  with its address).

The memory invariant is `Mem.FSeq := Mem.Seq ∧ ShapesWF (shapes m) ∧ Mem.LiveDisjoint m`: every
atomic location has a byte, no two overlap, and no two live blocks share an address (stage 3,
below). `locIdx` only creates a location where none overlaps (after retiring the overlapping
ones), and every new block is placed clear of the live ones (`Mem.ofGlobals_liveDisjoint` for the
start), so every reachable memory satisfies this.

`FTriple P c Q` (in `ZigLean/Sep/Full/Triple.lean`) is `Triple` with `Holds` in place of the heap
split and `FSeq` in place of `Seq`.

```
FTriple P c Q := ∀ m r rF, Holds m r rF → P r → m.FSeq →
  match (c.run m).run with
  | none => True | some (.error e) => e = .stackOverflow
  | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq
```

A stack overflow (`.stackOverflow`: an exhausted stack budget, or a stack block without room in
the address space) counts like a run with no result (premise STK-01); every other error is
excluded.

### Why tags on bytes, and not a separate `↦ₐ` resource

An atomic location is a property of particular bytes. A separate atomic resource disjoint from
the bytes would need an extra exclusion invariant: plain ownership and atomic ownership of
overlapping bytes must not coexist, and mixed sizes must be ruled out. Putting the tag on the
byte gets this for free:

* disjointness of byte ownership is disjointness of layout ownership;
* `apts` is just "owned bytes with a uniform constraint";
* plain loads and stores ignore tags, so every legacy rule still applies.

`apts` is the derived `↦ₐ`. It also frames like bytes.

### Atomic tags are constraints (semantic decision, alloc M2)

The first version read the tags exactly: `Holds` required `m.fheap = r.heap ∪ rF.heap`, tags
included. That is unsound for an atomic op on bytes owned as plain bytes (`up`, any layout), which
the arena needs (a node's header comes from its child allocator as a plain region and is then
accessed atomically). A location may cover owned bytes **and frame bytes**: a 16-byte (`u128`)
location, or any location over memory that was split between owners after it was used. An atomic
op on the owned bytes retires that location (`retireAt`: memory reused for another object, which
the model allows when every access to the old location happened before), so the frame's bytes
lose their tag, and no resource holds the new memory with the same frame. Kernel-checked:
`tests/roadmap/sep-full/ExactTags.lean`, `no_plain_atomic_triple` (against a copy of the old
`Holds`).

So a tag is a constraint. `some t`: the location over the byte is `t` or none; `none`: no
constraint (`TagSat`). Then:

* **Retire keeps the frame.** `retireAt` removes locations and never touches a block's bytes; a
  removed location leaves its bytes without a location, which meets every constraint
  (`TagSat.mono`). The new location covers only the op's own bytes. So `holds_after` holds for
  any constraint on the word, and the frame's cell values are unchanged (the op writes only the
  owned bytes; a load writes nothing).
* **Every read is the bytes.** In one thread the op reads the newest message of its location,
  which has the block's bytes in every case: an existing location of the op's shape gets a new
  message when the bytes differ or a plain write happened since (`locIdx`); a new location and a
  location that replaces retired ones start with the bytes. So a rule's value comes from the
  owned bytes whatever the layout (`locIdx_post`: `lastBytes = curBytes`), and the rules that
  read (`atomicLoad`, `atomicLoadAs`, `atomicLoadPtr`, `atomicLoadUnorderedEnc`, the `cmpxchg`
  rules, RMW) need no exact tag. `locIdx_noErr_single`: in one thread `locIdx` never throws.
* **What the constraint still says.** `apts`'s constraint `(p.off, 8)` keeps the shape of the
  layout over the word (`apts_layout`, O3: a memory with a 4-byte location at the hint holds
  no `apts` there), which a concurrent protocol needs (racing mixed sizes are `.unspecified`).
* **Plain bytes.** Constraints can be dropped (`Res.untag`, `FTriple.untag`), so an atomic rule
  applies to bytes owned as `up` (`wpts_of_up`); afterwards they are an `apts`
  (`plain_atomic_triple`).

No theorem statement changed: the rules with `apts` preconditions are corollaries of the general
ones (`FTriple.atomicLoadW`, `atomicStoreW`, `cmpxchgHitW`, `atomicLoadAsW`), and `FAllocSpec`,
`AllocSpec` and the allocator specifications are unchanged.

### Why knowledge, and not owning the dead block

A dead block has no bytes to own, and its address must stay readable by anyone who has seen it:
the allocator, the client that freed it, and other threads. That is exactly persistent,
duplicable knowledge. Owning a byte of block `b` gives `known b A` (`FTriple.know_intro`).
`@intFromPtr` of a pointer into `b`, live or dead, needs only `known b A` (`FTriple.ptrAddr`).
This also removes FBA's pin byte: the allocator invariant keeps `known buf A`.

### Alternatives considered

* **State `AllocSpec` in the concurrent logic** (`ZigLean/Conc/Logic.lean`, where `Proto.inv` is a
  predicate on the whole `Mem`). A whole-memory invariant can constrain atomics and dead blocks,
  and it suits a process-shared allocator. The drawback is that it has no frame: every client
  proof would have to be a `Proto`. This is not a replacement for full-state resources but a
  layer on top of them (see the concurrency section). Recommended for the thread-safety
  statement only.
* **A stronger `Mem.Seq`**, saying every stored pointer's block exists. This rules out
  `hintedLost`, but it gives no address facts, so the hint and alignment arithmetic still cannot
  be proved. It also says nothing about the atomic layout (O3).
* **Making all atomics plain in sequential runs.** This is unsound for the model: `locIdx` really
  throws on mixed sizes.

## Prototype theorems

| module | theorem | content |
|---|---|---|
| `Res` | `sep_comm`, `sep_assoc`, `sep_emp`, `sep_lift`, `known_dup`, `up_sep`/`sep_up`, `up_lift`, `up_emp` | the algebra: `up` embeds legacy `Assn` (any tags, no knowledge) and is a ∗-homomorphism |
| `Triple` | `FTriple.frame`, `conseq`, `bind`, `ret`, `ex`, `lift`, `drop`, `of_pure_run` | structural rules |
| `Triple` | `FTriple.ofTriple` | **lifting**: `Triple P c Q → Tame c → FTriple (up P) c (up ∘ Q)` |
| `Triple` | `Tame.load`, `store`, `loadBytes`, `storeBytes`, `alloc`, `free`, `ptrAddr`, `pure'`, `bind` | the plain primitives keep the layout and every block's address |
| `Triple` | `FTriple.know_intro`, `FTriple.ptrAddr`, `ptrAddr_none`, `ptrFromAddr_run`, `FTriple.ptrFromAddr` | knowledge from ownership; `@intFromPtr` of live or freed pointers; `@ptrFromInt` changes nothing and never fails (an ambiguous address gives a pointer without provenance: O4 fix, `docs/address-reuse.md`) |
| `Disjoint` | `Mem.LiveDisjoint`, `LDMono.set`/`push`/`grow`, `Mem.newAddr_addrFree` | live blocks have disjoint address ranges (`Block.clearOf`); every block update of the memory model keeps it |
| `Triple` | `Holds.apart`, `FTriple.apart` | owned bytes of two different blocks lie in disjoint address ranges (`LiveDisjoint` is part of `FSeq`) |
| `Ghost` | `Upd.alloc`/`issue`/`retire`/`reassign`/`bump`, `gfrag_mem`, `FTriple.upd`/`upd_post`/`mem`, `Upd.frame` | epoch ledgers of named grants (§Ghost state): frame-preserving updates; a token of the current epoch names a grant the authority records |
| `Atomic` | `locIdx_post`, `locIdx_noErr_single`, `holds_after`, `FTriple.untag` | `locIdx` in one thread, any layout: no error, the new location only over the bytes, overlapping ones retired, newest message = the bytes; the frame's constraints stay true |
| `Atomic` | `FTriple.atomicLoad` | `{apts p v} atomicLoadAt 0 ord 8 p {w. ⟪w = v⟫ ⋆ apts p v}`, any order |
| `Atomic` | `FTriple.atomicStore` | `{apts p v} atomicStoreAt 0 ord 8 p w {apts p w}`, any order |
| `AtomicPtr` | `FTriple.atomicLoadUnorderedEnc`, `FTriple.cmpxchgPtr` | pointer-valued `aptsE`: the `unordered` load reads the value; a strong `cmpxchg` with the held value succeeds |
| `Seq` | `Sched.run_solo`, `Sched.run_eq_seqRun`, `ThreadFreeC.*` | a one-thread scheduler run of a `ThreadFree` concurrent function is its sequential reading |
| `Conc` | `CTriple.bind`, `liftMem`, `pick_bind`, `step`, `know_intro`, `forget`, `conc_norm` | full-state triples for a concurrent function called in one thread (`Sched.soloRun`, oracle `0`) |
| `Atomic` | `apts_layout` | **O3**: a memory that holds a word as `apts` has no atomic location of another offset or size over it (`docs/alloc-page.md`'s `odd` memory holds no `apts` of the hint) |

The prototype toy allocator (`Full/Toy.lean`: the shape of `PageAllocator.map`'s hint protocol,
with the hint as a `u64` and the last mapping in a plain slot) is retired with the hand-written
allocator model (D2). The protocol is proved on the translated `PageAllocator` against
`FAllocSpec` (`tests/roadmap/alloc-translated/PageAlloc.lean`): its invariant owns the hint as a
pointer-valued `aptsE` (O3) and, for a non-null hint, only the knowledge `known b A` of its
block's address (O1), so `free` keeps it and the next `alloc` reads the dangling pointer's
address. The obstruction memories `odd` and `hintedLost`, with the same heap as a good memory,
differ from it in the resources a precondition can see (`PageObstruction.lean`). The toy's block
rules (`FTriple.alloc'`, `free'`, `allocC`) moved to `Full/Block`, and `apts_layout` to `Full/Atomic`.

## Soundness

* **Frame rule.** The frame `rF` is in the definition, so `FTriple.frame` holds for every program.
  It now covers the frame's tags and knowledge. It is non-trivial for primitives because each
  primitive rule must re-establish `Holds m' r' rF` for an arbitrary `rF`:
  * the frame's bytes are unchanged;
  * their constraints stay true, because a new location covers only owned bytes and a retired
    one leaves its bytes without a location (`holds_after`, `locIdx_post`'s tag statement);
  * the frame's knowledge stays true (`KMono`: blocks are only pushed or replaced with the same
    address).
* **Lifting.** `FTriple.ofTriple` uses the legacy triple on the erased heaps. `Tame` gives
  `shapes m' = shapes m`, so the frame's constraints hold in `m'` as in `m`; `KMono` gives the frame's
  knowledge. This is the only place where the old logic's guarantee ("live frame bytes
  unchanged") must be extended.
* **Knowledge.** A `Holds` memory contains every fact in `r.know`. `KMono` holds for every
  primitive:
  * alloc pushes a block (`KMono.push`);
  * free, store and `munmap` replace a block with one at the same address (`KMono.set`);
  * loads, atomics and `ptrFromAddr` do not change the blocks.

  `known b A` cannot be forged: `FTriple` quantifies over every `Holds` memory, and a false fact
  is in no `Mem.kn`.
* **Layout.** `ShapesWF` is part of `FSeq`, and every atomic rule re-establishes it
  (`locIdx_post`). `tagOf` is the first location covering a byte. Under `ShapesWF` it is the only
  one (`tagOf_of_mem`), so a constraint over owned bytes bounds what `locIdx` finds.
* **Adequacy.** A client proof starts from a memory that holds its precondition (the start
  memory, `Full/Init`: `Mem.init_fseq` and the program-start adequacy theorems). A
  full triple quantifies over fewer memories than `Triple (up P)`: exactly those whose full state
  fits. This is intended, since it is what makes the allocator's `alloc` specifiable.

### Address placement (`codex/fix-address-placement`)

* Placement chooses an address once, at allocation (`Mem.place`, `placeOk`), and never changes
  it. So `known b A` and `KMono` are unchanged by the fix.
* A dead block's address may later be reused by a live block. `known b A` says nothing about
  uniqueness, so `ptrFromAddr` (which may return either block) and `ptrEqAddr` comparisons of a
  dangling pointer stay unconstrained. This is sound and matches the native behaviour.
* `placeOk`/`addrFree` keep live blocks pairwise disjoint (`Mem.LiveDisjoint`, in the sense of
  `Block.clearOf`, so a block of size 0 constrains nothing). `FSeq := Seq ∧ ShapesWF ∧
  LiveDisjoint` (stage 3, done). `Holds.apart` turns ownership of bytes in each of two blocks
  into the order of their owned ranges (below), and the rule
  `FTriple.apart : FTriple (⟪disjoint⟫ ⋆ P) c Q → FTriple P c Q` (side condition shaped as
  `know_intro`'s) adds that fact to a precondition. This replaces per-client placement premises
  (the generated `@memcpy` overlap checks, the arena's foreign-slice comparison O-F).
* `Tame` includes `LDMono` (the step keeps `LiveDisjoint`). For the primitives:
  * `alloc` and `mmap` push a block at `Mem.newAddr`, which is clear of every live block
    (`Mem.newAddr_addrFree`: `placeOk` checks it, and the fallback `Mem.top` is past every block);
  * stores, atomics, `free`, `munmap` and an `mremap` shrink keep each block's address and do not
    grow it (`LDMono.set`);
  * an `mremap` growth in place grows only into a range that `Mem.mappingRoom` checked
    (`LDMono.grow`; the mapping is live from `lo ≤ size`, which `mremap`'s length check gives);
  * a moving `mremap` ends the old block and pushes the new one at `Mem.newAddr`
    (`LDMono.set_dead_push`).

## Block extents (alloc M2 O-G)

Status: design approved by the coordinator (2026-10-11), phases below. Phase 2 (the model and the
Full layer) is in the code, and the FixedBufferAllocator, the page allocator (Linux and macOS)
and the arena's `free`/`resize`/`remap` (stock Linux and macOS, patched) are re-proved against the
stronger `FAllocSpec`; the arena's `alloc` and `reset` follow, see the table. It replaces "frame cells carry their block's size".

**As implemented (phase 2).**

* Extents live in the ghost state (`Ghost.extent : BlockId → ECell`, `Res.lean`): per block,
  authority claims `auth (S, K)` (exclusive, exact) and nonnegative fractional shares at lower
  bounds `sh k` (`Frac`). `Ghost.Ok` requires at most one authority claim and at most the whole
  fraction; `Holds.ghost : GOk m r.gh rF.gh` adds `ExtTrue m`: an authority claim names a live
  block of that size and kind, a share at `k` a live block of at least `k` bytes, both with a live
  byte (`mappedLo < size`). `bext b S K` is the authority holding the whole fraction (`bauth b S K
  1`); `bshare b q k` is a share. Shrinking or ending a block needs `bext` (so the frame holds no
  share); growth keeps every share true.
* `FMatch` compares `Cell.norm` (size `0`, `.mapped lo` as `.mapped 0`). In-bounds facts come from
  ownership: `Holds.block` (an owned byte `x` gives a live block of more than `x` bytes, with
  `mappedLo ≤ x`). Rules that need exact cells read them off `Res.fix m` (`FTriple.of_fix`,
  `Holds.fix`, `Holds.congrF`).
* `Holds.apart` / `FTriple.apart`: owned bytes `x`, `y` of `b` and `x'`, `y'` of `b'` give
  `A + x < A' + y' ∨ A' + x' < A + y` (no cell sizes; the first and last owned bytes give the
  owned ranges). A block occupies only its live bytes (`Block.clearOf` from `mappedLo` on), so a
  block may lie below an OS mapping's first live offset (a thread's stack, MM-19); the earlier
  form `A + x < A' ∨ A' + x' < A` (byte before the other block's start) is false there
  (`tests/roadmap/stack-region/ThreadStack.lean`, `old_apart_false`).
* **The bridge** is one theorem, `FTriple.ofTriple` (`FTotalTriple.ofTotal`): precondition
  `upE P E` (the legacy `P` with the full extents `E`), `P`'s bytes in blocks `B`, `P` size-free
  outside `E` (`SizeFree E P`), `E`-cells recording `E`, and either every block of `B` pinned by `E`
  (pinned assertions) or `Keeps` (the program keeps every live block outside `E`). The post
  (`upPost`) owns the full extents of the blocks it has bytes of that were pinned or that `P` had
  no bytes of (new blocks). `FTriple.ofTriple_up` is the size-free case (`E` empty, `Keeps`).
* **Extent updates** (`ZigLean/Sep/Full/Extent.lean`): `EUpd P P'` is a frame-preserving update
  in a memory (it may change extent claims, unlike `Upd`); `FTriple.eupd`/`eupd_post` (and the
  `FTotalTriple`, `CTriple` versions), `EUpd.frame`. Rules: `EUpd.lend` (`bauth b S K (q₁+q₂)` to
  `bauth b S K q₁ ⋆ bshare b q₂ k`, `k ≤ S`), `EUpd.unlend` (back, from any bound),
  `bshare_split` (split/join at one bound), `EUpd.join` (two shares to one at the higher bound:
  the share there certifies it, so an allocator takes a grant's lower-bound share back into its
  own), `EUpd.weaken`; facts `Holds.bshare`, `Holds.bauth`. All are instances of `EUpd.ext1`
  (`ECell.Step`).
* **`FAllocSpec` carries the extent share** (stronger contract): `granted p k bs` is
  `∃ A S K q, up (regionIn …) ⋆ (I.tok p n k A S K q ⋆ pshare p q (p.off + n))`, so a client
  holding a grant knows that the block has at least `p.off + n` bytes, and `free`/`resize`/`remap`
  get the share back. The token sees the fraction `q`: an allocator that must collect its whole
  extent (`munmap`) knows that `free` returns exactly what it lent. `AllocInv.toFull` and the
  `up_granted` family are gone (a legacy `granted` has no share).
* **Native rules for generated code** (`ZigLean/Sep/Full/Ops.lean`): `ptrAddr`, `checkAlign`,
  `ptrEqAddr` and `ptrProject` as total full-state rules that read the memory through providers
  (`AddrOf`: knowledge or an owned cell; `Reaches`: an owned byte or an extent share), and the
  lifted `load`/`store` of `pts`. The FixedBufferAllocator is proved with them
  (`FBA.fallocSpec`): its invariant holds a share of the buffer block's extent at the buffer's
  end instead of a pin byte; a grant gets half of it, `free`/`resize` join it back.
* **Pinned allocators** (`ZigLean/Sep/Full/Pinned.lean`, removed with byte-range claims): a
  route that turned legacy total triples of an allocator whose token pins its grant's block into
  `FAllocSpec` fields. A legacy grant has no claim, so the route cannot build a grant
  (§Byte-range claims); the page allocator is proved natively by `fsym` (`PageSpec.lean`).
  `CTriple.step_bext` (legacy steps on a pinned block) stays.
* **Epoch-tagged shares** (step 3b, §Epoch-tagged shares below). `ECell` also holds tagged
  shares `tsh γ e k` and receipts `rc γ e k`. Validity and truth read the ledgers
  (3b: `Ghost.ep g γ e`, since 3c `Ghost.ls g γ e p`: ledger `γ` is at epoch `e`): in 3b, `ECell.TagOk` bounded the counted fraction
  `ECell.wsum` (the untagged fraction plus, per tag, `tagWt`: the larger of tagged shares and
  receipts while the epoch is current, the receipts once it is past, nothing otherwise) by `1`,
  and forbids tags of a future epoch; `ECell.Req` is a live claim (an untagged share, a tagged
  share of a current epoch, a receipt of a current or past epoch), and only live claims must be
  true (`ECell.TrueIn`, `ExtTrue m g` over the whole ghost state). `Ghost.Fin` bounds the ledger
  names that tags use, so `Upd.alloc` takes a name no tag uses. `Upd` keeps the extent claims
  and every true claim true (`Ghost.valid_led_change`); `Upd.bump` turns the old epoch's tagged
  shares dormant and keeps its receipts live. `full_excl`: the full extent leaves the frame only
  dormant claims on the block (`ECell.Dormant`), which is what the bridge and every shrink need.
  Updates of one block's claims are `ECell.StepE` (under every ledger status that contains the
  resource's ledgers, `EUpd.ext1L`); the untagged rules are `ECell.Step`. New rules:
  `EUpd.lendT`, `EUpd.returnT`, `EUpd.revoke` (with the parent tag of §Nested tags below).
  `FAllocInv.tag` (default `none`) tags `granted`'s share (`pshare … I.tag`); the
  FixedBufferAllocator and the page allocator keep `none` and are unchanged.
* **Nested tags** (step 3c, §Nested tags below): a ledger records a parent tag (`gauthP γ e M p`;
  `gauth γ e M` is the ledger without parent). Validity and truth read the ledger statuses
  (`Ghost.ls g γ e p`): a tag is active (`Act`) while its ledger is at its epoch under an active
  parent, future (`Fut`) when its ledger is at an earlier epoch or its parent is future. The
  3b counting (`ECell.wsum`, `tagWt`) became the balanced tree of worlds (`ECell.BalAt`, `Bal`,
  `mass`, `cwt`); `Ghost.valid_led_change` is the one lemma behind `Upd.alloc p` and `Upd.bump`.
  `bshare_split`, `EUpd.join`, `EUpd.weaken` hold for every tag (`ECell.StepT`, `EUpd.ext1T`);
  `Holds.bshare` takes the tag's activity in the resource (automatic for an untagged share;
  `Holds.bshareT` is gone). Regression: `tests/roadmap/sep-full/NestedTags.lean`.
* **Allocators with tagged grants** (step 4, the arena's `free`/`resize`/`remap`, coordinator
  decisions 2026-10-11):
  * A ledger's grant records the lent fraction (`GRegion := Ptr × Nat × Frac`): the arena's token
    is `gfrag γ e i (p, n, q)`, so `free` and `resize` return the share against exactly the
    receipt the arena keeps for grant `i` (one per grant id, `Rcpts`; returned shares go to a
    pool until the node goes back to the child).
  * `FAllocInv.act`: an allocator's `own` witnesses that the tag of its grants' shares is active
    (`Act`). It is a field with the default proof `Act.root`, so every untagged invariant (the
    FixedBufferAllocator, the page allocator) has it unchanged; the arena proves it
    from its ledger (`act_gauthP`, parent `CI.tag`) and its child's `act`. An allocator that holds
    a child's grants reads their bounds with it (`FAllocInv.act_within`, `Holds.pshareW`), with
    no hypothesis on the child.
  * General pieces in the library: `Within X P` with the `within` tactic (find a part of a
    separating conjunction; `Holds.bshareW`, `Owns.within` in the arena), `EUpd.ex`/`exAll`/
    `lift`/`withFact`, `EUpd.pweaken` (a grant share's bound), `pshare_iff`, `EUpd.relabel` (a
    region's cells with another size label and a kind of the same normal form: labels carry no
    information), `Mem.LiveDisjoint.addr_ne` (two live blocks share no byte address), `Junk` (one
    definition for every allocator), `sepN` (an indexed separating conjunction).
* **Native OS mapping rules** (step 5, `ZigLean/Sep/Full/Mmap.lean`): one general step
  `Holds.reblock` (a block's extent changes under its `bext`; the resource gives up exactly the
  bytes that stop being live and gets those that become live; frame bytes keep their normalized
  cells), `Holds.trim`, and the rules `FTotalTriple.munmapTail'`, `munmapPrefix'` (the live start
  moves: a kind of the same normal form), `mremapShrink'` (each from `bext` and the released bytes
  only) and `mremapGrow'` (growth in place without `MAYMOVE`, `LDMono.grow` from
  `Mem.mappingRoom`; the new bytes go to the caller). Growth needs only the authority with any
  fraction (`Holds.grow`: every share stays true when a block only grows), so an allocator whose
  grants hold shares of a block (the page allocator's token keeps `bauth (1 - q)`) grows it in
  place without collecting them. A whole mapping (`mmap`, a whole `munmap`, a
  growth that may move) needs every byte and lifts with the pinned bridge (the page allocator).
* Blocks (`Full/Block`): `FTriple.alloc'` returns the new block's `bext`; `FTriple.free'` takes it.
* Removed: `FAllocSpec.ofTotal`, `FLogic.legacy`, `LegacyTokens`, `FAllocSpec.toLegacy` and
  `ZigLean/Sep/Full/Wrappers.lean`. They read every legacy assertion as `up P`, which is unsound
  here (`tests/roadmap/sep-full/BlockExtentsCX.lean`, `no_cell_size`).

### The problem (O-G)

A cell records its block's address, size and kind (`Cell`, `Mem.heap`), and `Holds` matches
the frame's cells exactly. So every change of a block's size or of a mapping's live start
(`mremap` growth or shrink in place, `munmap` of a page prefix or tail, a heap or fixed-buffer
remap in place) changes the cells of every owner of a byte of that block. An owner of a part of
a block can then not resize the block without the other parts, although the change touches no
byte they own.

The translated `ArenaAllocator` shows that this is not only a proof gap. Its `alloc` grows its
first node in place through the child (`child_allocator.rawResize(node, …)`) while clients hold
grants inside that node:

* `FAllocSpec.resize` needs `I.own ⋆ I.granted p k bs`, the region's bytes included, and the
  arena does not own its clients' bytes. So no proof from the child's `FAllocSpec` exists.
* With `page_allocator` as the child, the step is a real violation of the arena's
  `FAllocSpec.alloc`. Take a client that holds an 8-byte grant in the first node and calls
  `alloc(5000)`. `PageAllocator.resize` grows the mapping in place (`mremap` without
  `MAYMOVE`, `Mem.mremapGrown`). The client's cells, part of the frame, record the old size, so
  no `Holds m' r' rF` exists. This holds for every arena invariant. Natively nothing is wrong: an
  object's bytes do not depend on the size of the mapping around them.

Weakening "≤" (a frame cell's size at most the block's) works for growth but not for a shrink
that releases only the tail: the prefix's cells would record more than the new size. That is
why the size leaves the cells.

### The design: size-free cells and extent resources (RustBelt/Iris split)

1. **Cells carry no block size and no mapping start.** `FMatch` compares cells after
   normalizing them (`Cell.norm`: size `0`, `.mapped lo` as `.mapped 0`). A cell still records
   the byte, the block's address (which never changes) and the kind's constructor, which never
   changes (`constGlobal` rules out writes). Owning a cell still gives what an access needs: the
   cell is in `Mem.heap`, so the block is live, the offset is below the size and at or above
   `lo` (`Mem.access`, `Mem.inBounds` up to one past the owned bytes).
2. **`bext b S K`: the exclusive extent of a live block.** This is a new component
   `ext : BlockId → Option (Nat × BlockKind)` of `Res`, disjoint between `r` and `rF`, and exact
   in `Holds`: `m.blocks[b]` is live with size `S` and kind `K` (`lo` included). Only its owner
   changes a block's size, start or liveness. Like a byte, it splits and joins by
   disjointness.
3. **`bsize b S`: persistent size knowledge** for blocks whose size never changes (`stack`,
   `global`, `constGlobal`). It joins `know`: it is duplicable and stays true in every later
   memory. The audit found that `.heap` blocks (`remapByteBuffer`, `Mem.afterByteRemap`) and
   `.owned` blocks (`ownedRemapBytes`) also resize, so for them, as for `.mapped`, only `bext`
   pins the size.
4. **What needs what.**
   * Load, store and atomic ops: the bytes. Unchanged.
   * `ptrProject` within or one past the owned bytes: the bytes. A pointer up to a bound that
     the caller does not own bytes to, such as the arena's `buf + end_index` when clients hold
     the end of the node, needs `bext` or `bsize`.
   * `free`, `munmap` of the whole block, and `mremap` that moves: `bext` (or `bsize` for
     non-resizable kinds) plus every byte of the block.
   * Shrink in place and `munmap` of a tail or prefix: `bext` plus the released bytes only.
   * Growth in place: `bext` and no existing bytes. The new bytes go to the caller.
   * `Holds.apart`: owned bytes of two live blocks lie at disjoint addresses. Disjointness of
     whole blocks needs both extents; the arena's O-F needs only the owned bytes and one past.
5. **Frame preservation** (the soundness obligation, per primitive): a step changes a block's
   size, start or liveness only with its `bext` (or `bsize` plus all its bytes) in the
   precondition. Frame cells keep their normalized cells: a released byte is the caller's, and a
   grown byte is new. Frame extents are untouched. Frame knowledge stays true (`bsize` only for
   kinds that never resize). Every rule that reads a size reads it from `bext`, from `bsize` or
   from an owned cell, never from a frame cell.

### `FAllocSpec` refined (a stronger contract)

**As implemented (step 7a; coordinator decision 2026-10-11).** One `resize` field, both
directions (`ZigLean/Sep/Full/AllocSpec.lean`): the precondition is `I.own ⋆ (I.held p len k A S
K q q' ⋆ I.relBytes p A S K n len tl)`, where `I.held` is the token and a part `q'` of the grant's
extent share at the grant's end, and `I.relBytes` the bytes `tl` that a shrink releases (`[n, len)`,
with their claim, §Byte-range claims; nothing for a growth). The client keeps the bytes it keeps. On success (`rresizePost`) the token
is at `n` (same address; size and kind labels within the kind's normal form), the share at the
new end, and a growth hands over the new bytes `[len, n)` (`newBytes`); on failure the
precondition comes back.

* **A growth takes any part of the share** (`q' ≤ q`): every other part stays true when the block
  only grows (`Holds.grow`), so an arena that lent most of its node's share to its clients grows
  the node with the part it kept (O-G).
* **A shrink takes the whole share** (`q' = q`), for the same reason as `munmap` needs `bext`: an
  allocator may shrink the block itself (the page allocator's tail `munmap`), and a share held
  elsewhere would then claim the old end. Kernel-checked regression
  (`tests/roadmap/sep-full/ShrinkCX.lean`): a mapping of two pages, the tail page's bytes and half
  the authority in the resource, the first page and a share of the other half at bound `8192` in
  the frame (`EUpd.lend`); the tail `munmap` succeeds and leaves `4096` bytes, so no resource holds
  next to that frame (`frame_breaks`), and no `FTriple` from half the authority exists, whatever the
  postcondition (`no_partial_shrink`). With the whole extent the rule holds
  (`FTotalTriple.munmapTail'`).
* `FAllocSpec.resize_granted`: the old whole-region contract is a corollary (the client splits off
  the released bytes, relabels the kept ones to the new token's labels, `EUpd.relabel`, and joins
  the new bytes); `FLogic.eupdPost` (an `EUpd` of the postcondition) is a field of the logic for it.
* `remap` keeps the whole region (it may move).
* **Receipts of a grant whose holder gives back only a part** (the arena as a child, step 7a):
  general rules in `Extent.lean`. `EUpd.rweaken` lowers a receipt's bound (it claims less and
  gives back a share at the lower bound; any ledger status), `EUpd.rjoin` joins two receipts of
  one tag at the lower bound (`rweaken`, `brcpt_split`), and `EUpd.returnTw` gives a tagged share
  back against a receipt at any bound (the share is weakened to it first). So an allocator keeps
  one receipt per grant at some bound: a growth by a part `q'` splits the receipt, re-lends `q'`
  at the new end and joins the two again. A grant's bound lives in its tagged share, not in the
  receipt; the allocator's own share of the block (an arena's `qh`, at the node's end) restores
  the bound when the pieces join (`EUpd.join` takes the higher bound).
* **The token remembers the cells' labels.** A growth hands out new bytes with the labels `A`, `K`
  that the client names, and the client gives no byte to read them from, so a token must pin them:
  the FixedBufferAllocator's and the page allocator's tokens do (pure facts; the mapping's
  authority), and an arena's ledger records them (`GRegion` carries `A`, `K`; the arena's
  invariant ties every grant to a node of its block with those labels).
* **Instances.** The arena's `resize` (stock x86_64-linux and aarch64-macos, patched) meets the
  refined field (`tests/roadmap/alloc-arena`, `AllocArena/Core.lean`); `remap` uses the
  whole-region form (`FAllocInv.resize_granted_of`, a per-triple corollary). The
  FixedBufferAllocator and the page allocator are re-proved natively on `codex/sep-auto` (`fsym`).

The design below is the original plan.


`resize` and `remap` keep their postconditions. `resize`'s precondition becomes `I.own ⋆
I.tok p bs.size k A S K` plus `up (regionIn (p.add n) …)` of the released bytes `[n, len)` when
`n ≤ len`, and nothing of the region when it grows. Zig's `resize` is in place and keeps the
contents, so the bytes a caller keeps are its own throughout. `remap` may move, so its
precondition keeps the whole region (the in-place branch is not split off; the code decides
inside). The old `resize` field follows as a corollary (frame the kept bytes). Tokens that pin
an extent carry `bext` (page allocator: the mapping's `bext`, replacing the tail-ownership pin
of O2) or `bsize` (fixed buffer in a global: the buffer's `bsize`, replacing the pin byte).

### The bridge from the legacy layer

The legacy layer (`ZigLean/Sep`: `Cell`, `bytesAt`, `Triple`, ~95k lines of dependents) keeps its
semantics. `FTriple.ofTriple` and `FTotalTriple.ofTotal` change their side conditions:

* **Size-free assertions** (`SizeFree P`: invariant under changing the sizes and `lo`s of the
  cells, for example `region p a bs := ∃ A S K, …` and `granted`): a legacy triple of a
  program that changes no existing block's extent (`Tame` plus extent-preserving) lifts as
  today. The proof instantiates the legacy triple at the memory's actual sizes.
* **Pinned assertions** (`up P ⋆ bext …`, where every block of `P`'s cells has its extent in
  the precondition, for example `Sep/Mmap.lean`'s `mapping`): a legacy triple lifts, and it may
  change those extents (`mremap`, `munmap`). The post receives the new extents of those blocks,
  and the extents of blocks the step creates.
* If a legacy triple fits neither form, the lift is not available. Report it then; do not
  rewrite the legacy layer for it.

### Epoch-tagged shares (step 3b, coordinator decision 2026-10-11)

An arena's `reset` bumps its ledger's epoch (§Ghost state) and takes its nodes back; with
`.free_all` it frees them to its child, which needs the node's whole share back. But the clients
of the old epoch still hold shares lent off the node's share, and a stale share cannot come back.
So a share can carry an epoch tag, `bshare b q k (tag : Option (LedgerId × Epoch))` (step 3b; step 3c,
§Nested tags, makes the tags a tree):

* **Untagged shares** behave exactly as before. `FAllocInv.tag` (default `none`) is the tag of
  the shares in `granted`; the FixedBufferAllocator and the page allocator keep `none`, so their
  statements and their clients are unchanged. An arena's invariant family `I e` uses
  `some (γ, e)`.
* **A tagged share `(γ, e)` counts and is true only while ledger `γ` is at epoch `e`** (its
  authority `gauth γ e _` exists) and its parent tag is active (§Nested tags): validity and truth
  read the ledgers. Its fraction is booked
  twice: the client's tagged share and the lender's **receipt** (`EUpd.lendT`: an untagged share
  becomes a tagged share and a receipt of the same fraction). Per tag, validity counts
  `max(tagged, receipts)` while the epoch is current, the receipts once it is stale, and nothing
  while the ledger has no authority. A tagged share given back during its epoch cancels its
  receipt (`EUpd.returnT`). After `Upd.bump`, the receipts of the old epoch turn back into
  shares tagged with the ledger's parent, untagged for a root ledger (`EUpd.revoke`): the ledger authority revokes every share of a past epoch at
  once, whatever the clients kept (the cancellable-invariant pattern). Every rule is general (the
  ghost library), none is arena-specific.
* `bext` (the whole fraction) still leaves the frame no counted claim, so shrinking and freeing
  keep every frame true; claims of a tag whose ledger has no authority, or of a future epoch, are
  dormant.
* `Ghost.Fin` also bounds the tags' ledger names, so `Upd.alloc` picks a name no tag uses.

### Nested tags (step 3c, coordinator decisions 2026-10-11)

An arena whose child is an arena gets node shares that are already tagged by the outer arena's
ledger; the shares it lends must die with either epoch. One mechanism covers both levels, a tree
of tags:

* **The parent link lives in the ledger authority** (`GCell.auth` is keyed by `(e, M, p)`;
  `gauthP γ e M p`; `gauth γ e M := gauthP γ e M none` keeps every existing user). `Upd.alloc p`
  creates a ledger with parent `p` at a name no frame uses, no tag uses and no ledger names as its
  parent (`Ghost.Fin` bounds parent names too); `Upd.bump` keeps the parent.
* **Active is recursive** over the parent chain (`Act`, an inductive predicate: a cycle is never
  active). **Future** (`Fut`) is recursive too: a tag whose ledger is at an earlier epoch, or whose
  ledger's parent is future. No future tag has a claim (`ECell.FutZ`), so a bump that makes a tag
  current activates an empty subtree.
* **Lending always records its source**: the source of a lend under ledger `γ` is `γ`'s parent
  tag (`none`: an untagged share). `EUpd.lendT`: `gauthP γ e M p ⋆ bshare b q k p` to `gauthP γ e
  M p ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e)`; `EUpd.returnT` cancels back to the
  `p`-tagged share; `EUpd.revoke` (`e < e'`) turns a stale receipt into a `p`-tagged share. The
  3b rules are the case `p = none`. The source is not a separate field of the receipt: a lend from
  a tag that is not on the chain of `(γ, e)` would let the lent share outlive its source, so the
  source must be the parent, which the ledger already fixes.
* **Accounting** (`ECell.BalAt`): the shares tagged `w` form the world `w` (`tg c w`; the root is
  `none`), a receipt of `(γ, e)` lies in the world of `γ`'s parent. A child's weight in its parent's
  world (`cwt`) is the larger of its receipts and its own world's budget `β γ e` while it is
  current, its receipts once it is past. `Bal`: some budgets make the root's fraction at most `1`
  and every active world's fraction at most its budget, below every bound. So a child's weight
  counts inside its source's budget and the root sums the whole tree. The form is downward closed
  (dropping claims or ledgers keeps the same budgets valid), and `bext` still leaves the frame only
  dormant claims (`ECell.dormant_of_auth1`, by induction on `Act`: every active world of the frame
  weighs nothing).
* **One lemma for every status change** (`Ghost.valid_led_change`): a change of the ledgers keeps
  validity and truth when the tags it makes active or future lie in a claim-free set `Z` closed
  under children, and every other child keeps a status as live as before. `Upd.bump` uses the
  future tags as `Z` (a bump turns the old epoch and its whole subtree dormant at once);
  `Upd.alloc` adds the new name.
* **A tagged share's bound needs its tag's activity** (`Holds.bshare`, argument `Act r.gh.ls t`):
  the ledgers of the whole chain must be in the resource. An arena owns its child allocator
  (`CI.own`), so an arena over an arena holds the outer ledger's authority; the arena proof
  (step 4) needs `CI.own` to witness `Act CI.tag` (trivial for `none`): `FAllocInv.act`.
* FBA and the page allocator (tag `none`) keep their statements; their checks pass unchanged.
* Regression `tests/roadmap/sep-full/NestedTags.lean`: `nested_reset` goes from `bext` through
  an outer grant, an inner ledger under it and an inner grant, to `bext` again after the outer
  reset, with the inner ledger, share and receipt still held; `inner_dead`: the inner tag is
  inactive in every memory that holds the result.

### Phases (one commit and one agent phase each, estimated)

| | phase | content | estimate |
|---|---|---|---|
| 1 | design | this section | done |
| 2 | model | `Res.ext`, `bsize` in `know`, normalized `FMatch`, `Holds`; re-prove `Res`, `Triple`, `Atomic`, `AtomicPtr`, `AtomicRules`, `Disjoint`, `Ghost`, `Seq`, `Tame`, `Toy`, `Conc`, `Dispatch`; the two bridges | 1–2 phases |
| 3 | OS rules | native full-state `munmap` prefix/tail, `mremap` grow in place (`bext` only) and shrink (`bext` + tail); `mmap`, whole `munmap` and move through the pinned bridge | done |
| 4 | spec | refined `FAllocSpec.resize`, old form as a corollary, `toLegacy` and wrappers adjusted | ½ phase |
| 5 | re-proofs | FBA (`resize` from the token; `bsize` of the buffer; no pin byte), `PageSpec` linux+macOS (token = `bext` + tail), arena `free`/`resize`/`remap` (O-F from the slice's bytes and the node's extent share) | done |
| 6 | arena `alloc` | patched arena for every `CAllocSpec` child (dispatch through `CVTable.dispatch` + `vtR`; `fits` per O-C); page child instance; O-G regression (`8`-byte grant, then `alloc(5000)`) | 2–3 phases |
| 7 | the rest | `reset` (stock and patched); the `Unroll` fix-group cut and `not_fallocSpec_arena` done | 1 phase |

The general atomic rules the arena's `alloc` needs are done independently
(`AtomicRules.lean`: `atomicXchgPtrW`, `cmpxchgWeakPtrW`, `atomicLoadUnorderedW`/`AsW`) and carry
over to phase 2 unchanged in statement.

### Const globals (persistent knowledge, 2026-10-12)

A `const` global (a vtable, a string literal, any `const` data) is read-only static storage. Before
this change the only way to read one was to own its bytes (`up (ptsR …)`), exclusively, so a
second user of the same global could not be framed in: two allocators with the same vtable (an
arena's child, the `std.mem.Allocator` clients M01–M04) could not both hold it (kernel-checked:
`ConstKnow.vtOwn_twice`).

* **Model fact.** A write to a `.constGlobal` block throws `.illegal` (`Mem.accessW`: stores,
  atomic stores, RMW, `cmpxchg`); every other step that changes a block is reached only after a
  kind check (`munmap`/`mremap`: `.mapped`; byte remap: `.heap`; owned remap and reset: `.owned`;
  an atomic write's message: its `accessW`; each primitive's `KMono` proof checks it) except
  `Zig.free`, which ended any live block at offset 0. **Model correction**: `Zig.free` of a `const`
  global throws `.illegal` (native code cannot free static storage; no generated `free` reaches
  one: it frees stack slots, and `rawFree`/`ownedFree` check the kind first). The legacy free
  lemmas got the side condition (`free_run_core`, `free_run`, `Triple.free`, `TTriple.free`,
  `free_whole`, `FTriple.free'`: `K ≠ .constGlobal`, by `decide` for a concrete kind;
  `free_noErr`: `blk.kind ≠ .constGlobal`). So a live `const` global keeps its bytes, address and
  life in every later memory.
* **Knowledge.** `Know` is a set of facts `KFact`: `.addr b A` (as before, `known b A`) and
  `.cbyte b o c`, true in `m` when block `b` is a live `const` global whose byte `o` is `c`
  (`Mem.kn`). `KMono` (every primitive's `Tame`/`Keeps` step) keeps both: `KMono.set` takes
  `blk.kind ≠ .constGlobal`, which each primitive gets from the model's guards above.
* **Assertions** (`ZigLean/Sep/Full/Const.lean`): `cbytesAt p A bs` (the live `const` global at
  `p`, block address `A`, holds `bs`) and the typed `cpts p a v` (`ptsR` as knowledge). Both are
  `Persistent` (no bytes, no ghost state): `Persistent.dup` (`P ⊢ P ⋆ P`), `Persistent.drop`
  (forgotten by an update), `Persistent.absorb`, `cbytesAt_part`.
* **Introduction**, once: from owned `const` bytes (`cbytesAt_intro`: the owner keeps the bytes
  and hands out the knowledge), or from the memory itself (`Holds.addKnow`; the initial memory's
  `const` globals: `Mem.ofGlobals_kn`).
* **Reading**: the provider `ConstAt` and `FTotalTriple.load_const`; for `fsym`,
  `FTotalTriple.cload` (`@[fsym]`) and `AddrOf.cbytesAt`, `Reaches.cbytesAt`, `Reaches.cpts`
  (`@[fsym_provider]`).
* **Vtables** (`ZigLean/Sep/Full/Dispatch.lean`): `vtR vtp fns` is now the persistent sep-list of
  `cpts` entries (`vtR_dup`, `vtR_drop`, `vtR_load`, `vtR_project`, `vtR_intro` from the global's
  owned bytes). The owned form, for a vtable in any block (built at run time), is the old
  predicate renamed `vtOwn` (an `Assn`, used under `up`) with the old rules (`vtOwn_load`,
  `vtOwn_project`), same statements. Regression:
  `tests/roadmap/sep-full/ConstKnow.lean` (two handles whose invariants each hold the vtable, a
  store to and a free of a `const` global are `.illegal`).

### Byte-range claims (decision O1, 2026-10-12)

**The problem.** An extent share says that a block is live and long enough, not who may use which
bytes. An allocator that holds several grants of one child allocator in one block (an arena's
nodes from a fixed-buffer child) cannot learn that they are disjoint: their bytes are with the
clients, and the child's specification relates no new grant to the outstanding ones
([alloc-arena.md](alloc-arena.md) O1).

**The design.** `Ghost` has a third component, `cl : BlockId → Nat → ECell`: one claim cell per
byte of every block, the same kind of cell as a block's extent claims, used at bound `0`
(`ZigLean/Sep/Full/Claims.lean`).

* `bclaim b lo hi t`: the whole fraction `1` of the cell of every byte of `[lo, hi)` in world `t`
  (`ECell.shareT t 1 0`); `bcrcpt b lo hi γ e`: the receipts (`ECell.rcpt γ e 1 0`) of a claim lent
  as one tagged `(γ, e)`; `pclaim p lo hi t` names the block through a pointer.
* Validity (`Ghost.CValid`, the third conjunct of `Ghost.Valid`) is the extent cells' validity per
  byte (`ECell.Valid`, `ECell.TagOk` under the ledgers' statuses) and a bound on the ledger names
  that carry byte claims (a new ledger has none, `Upd.alloc`). So two claims on one byte of one
  active world are invalid (`Holds.bclaim_disjoint`, `ECell.ftot_act_le`), and tagged claims are
  lent, returned and revoked exactly as tagged shares are, with the same tag tree.
* A range claim is the union of its bytes' claims: split and join are **equalities**
  (`bclaim_split`, `bcrcpt_split`), not updates.
* Truth (`ClFresh`, the third conjunct of `GOk`): no resource claims a byte of a block the memory
  has not created. Primitives keep it because blocks are never removed (`KMono.size_le`).

**Claims are born with their block.** The creator of a block claims any range of it
(`FTriple.mintClaim`: a program whose run creates block `nb v` yields `bclaim (nb v) lo hi` next
to a post without claims on that block). There is no other source. Minting from `bext` later is
unsound with the existing extent rules: validity must be closed under dropping parts
(`Ghost.Ok.mono`), so a claim cannot require the presence of anything, and every condition of the
form "a live claim excludes the full extent" is broken by `EUpd.unlend`, which re-completes `bext`
from a share without looking at claims. Claims on bytes beyond a block's size or of a freed
block are harmless: block ids are never reused and in-place growth mints nothing. Existing rules
are unchanged (`bext`, `bauth`, the extent updates, `fsym`'s rules); proofs that build ghost states
by hand add the claim component (`Ghost.CValid.congr`, `ClFresh.congr`).

**Lending.** Tagged claims are lent, returned and revoked like tagged shares, byte by byte: the
cell steps of `EUpd.lendT`, `EUpd.returnT` and `EUpd.revoke` are lemmas of their own
(`ECell.stepE_lendT`, `stepE_returnT`, `stepE_revoke`), and `GOk.cl1`/`EUpd.cl1L` lift a per-byte
cell step of one block's claim cells to an update, so `EUpd.lendC`, `EUpd.returnC` and
`EUpd.revokeC` reuse them.

**Creation rules.** `FTriple.mintClaimOpt` mints the claim of a block a run creates, for the runs
whose result names one (`nb v = some b`), with bounds that may depend on the result.
`FTriple.allocC`/`allocStackC` add `bclaim b 0 size` to `alloc`; `FTotalTriple.mmapC` adds the
claim on `[0, 2^64)` of a new mapping (past its end, so that an in-place `mremap` growth, which
mints nothing, finds the new bytes claimed), and `FTotalTriple.mremapMoveC` passes the mapping's
claim `[lo, lo + 2^64)` on: in place it stays, a moved mapping gets a fresh one. The two mapping
rules are `fsym`'s rules for `mmap` and `mremap` growth.

**Use.** An allocator's grant carries the claim on its bytes tagged with the allocator's tag:
`FAllocInv.granted` holds `pclaim p p.off (p.off + n) I.tag` next to the grant's share, so
`FAllocSpec` gives a client exclusive claims on its grants. The FixedBufferAllocator's invariant
holds the claim on its free tail `[e, cap)` (a grant's claim is carved from it; the last grant's
free or shrink joins it back), the page allocator's token the claim on the mapping from the
grant's end on. `fsym` plans claims (`AutoClaims.lean`). An arena holds its nodes' claims (the
child's tag), so its nodes are pairwise disjoint while the child's tag is active
(`tests/roadmap/sep-full/ClaimsCX.lean`, `arena_nodes_disjoint`), lends its grants' claims tagged
with its epoch, and `reset` revokes them like their shares.

**Claims follow bytes in `resize`** (coordinator decision 2026-10-12). In the refined `resize`
(§`FAllocSpec` refined) `FAllocInv.held` is the token and the share only. The bytes a shrink
releases come with their claim (`I.relBytes`: `[n, len)`), and the new bytes of a growth come with
theirs (`I.newBytes`: `[len, n)`). The client keeps the claim on the bytes it keeps. If `held`
carried the whole claim instead, an arena could not grow a node in place while the node has
grants: the node's buffer claim is lent to the grants, so the arena holds only its receipt, and a
receipt and the parent world's claim on one byte cannot both hold (O-G, `docs/alloc-arena.md`).
**Not a weakening:** `FAllocInv.resize_whole_of` derives, from the refined triple, the form in
which `held` carries the whole claim before and after (`heldW`, `rresizePostW`). That form asks the
client for more and gives it the same claims back. `FAllocInv.resize_granted_of` (whole region)
splits and joins the claim along with the bytes.

### The fee of a grant (coordinator decision 2026-10-12)

**The problem.** A `reset` that revokes outstanding grants is unsound whatever ghost state it
bumps: a grant gives the client exclusive bytes, and revocation withdraws only ghost state
(`tests/roadmap/alloc-arena/ArenaObstruction.lean`, `not_reset_own`, kernel-checked). So `reset`
must know that no grant is outstanding. Its precondition cannot list the grants (the client does
not know them all), so the evidence must be a resource that every grant takes away and every
`free` gives back.

**The design.** `FAllocInv.fee : Frac → FAssn` (default `fun _ => emp`) is what `alloc` charges
for a grant. `FAllocSpec.alloc` takes `I.own ⋆ I.fee φ` for any `φ` the client picks; the token
records `φ` (`FAllocInv.tok`'s last argument), and with it `granted p k φ bs`, `held … φ`,
`allocPost len k φ`, `resizePost`, `rresizePost` and `remapPost`. A failed `alloc` gives `I.fee φ`
back (`allocPost … none = own ⋆ fee φ`), `free` gives it back (`fun _ => own ⋆ fee φ`), and
`resize` and `remap` keep the grant's `φ`. The wrapper contracts (`Full/Wrappers`) carry it too:
`owned k φ p bs` is the unspent fee for zero bytes (the wrapper does not call the allocator), and
`allocResult`, `sliceResult`, `bytesResult` give the fee back with `error.OutOfMemory`.

An arena charges a fraction of its epoch token (§Epoch tokens; `fee γ e φ = epTok γ e φ ⋆
⟪0 < φ⟫`, `AllocArena.Core.fee`), keeps each outstanding grant's fee next to its receipt
(`rcptOf`), and its `reset` takes the whole epoch token next to `own`: holding fraction `1` while
the state holds the fees of the grants of `M` forces `M = ∅` (`gauth_epTok_whole`,
`Core.own_epTok_empty`).

**The allocator records the fee.** `free` must refund exactly the fee that was paid. A token that
ignores `φ` would let a client claim any `φ` back (for an arena: mint epoch-token fractions). So
an allocator that charges a fee records it per grant: the arena's ledger has it as the sixth
component of `GRegion`. Keeping the fee only inside the client's token, with no record in the
allocator's state, is unsound for `reset`: a client that drops a token leaves `M ≠ ∅` with no
fee outstanding.

**Why this is no weakening for a fee-free allocator.** With `fee = emp`, `own ⋆ fee φ = own`,
`allocPost len k φ none = own ⋆ emp = own`, and `free`'s postcondition is `own`; a token that
ignores `φ` makes `granted p k φ bs` the same assertion for every `φ`. So each field, at every
`φ`, is the field without a fee: the `FixedBufferAllocator` (`FBA.fallocSpec`) and the page
allocator (`PageSpec`, `PageSpecMacos`, `PageAlloc.fallocSpec`) prove the same statements as
before, with an unused `φ`, and a client picks any `φ`.

**What it asks of a client.** To call `alloc` it holds a fee: nothing for a fee-free allocator; a
fraction of the epoch token for an arena (`init` gives the whole token next to `own`). To call an
arena's `reset` it gives back every outstanding grant (`free`, or `Core.grant_return`, a ghost
update that hands the bytes back without the code freeing them and refunds the fee) and so
reassembles the whole token. A client that keeps a grant cannot hold the whole token
(`Core.granted_epTok_false`), so the client of `not_reset_own` (`alloc`, `reset` with the grant
still out) has no precondition for the arena's `reset`. A leaked grant blocks `reset` for good;
that is inherent (`not_reset_own`), not a cost of this design. Like `own`,
a fee that never holds makes `alloc` vacuous, so the non-vacuity checks quantify over invariants
whose state and fees hold somewhere (`tests/roadmap/sep-full/AllocNeg.lean`,
`ArenaObstruction.not_fallocSpec_arena`).

**Status.** The library, the wrapper contracts, the `FixedBufferAllocator`, the page allocator and
the arena carry the fee. The `FixedBufferAllocator`'s and the page allocator's fee is `emp`; the
arena's is the epoch-token fraction (`free_spec`, `resize_spec` and `remap_spec` of
`tests/roadmap/alloc-arena` are proved with it, `free` refunding it), with `grant_return`,
`own_epTok_empty` and `granted_epTok_false`. The arena's `reset` code proof is next.

### Credits and room: non-mintable resources (2026-10-12)

**The problem.** Two counted resources were requested: `credits n` (time/turn credits for the
concurrent termination proofs, [sep-threads.md](sep-threads.md)) and `room n` (address room, so
that a total `alloc` can rule out `.stackOverflow`). Both must be **non-mintable**: no judgment may
end with more of them than it started with; only the adequacy theorem hands an initial supply to
`main`. A count that `Holds` does not see can be minted by every judgment (`EUpd emp (credits 1)`
holds whenever `Ghost.Ok` ignores the count).

**Two variants compared.**

1. *A non-mint conjunct per judgment*: every witness of `EUpd`, `Upd`, `FTriple`, `FTotalTriple`,
   `CTriple`, `FTTriple`/`FTTotalTriple` adds `r'.gh.cr ≤ r.gh.cr`. Each direct proof of a rule
   (`intro m r rF …`, about 110 of them) must prove it, and every future judgment must repeat it.
2. *An authoritative supply in validity* (Iris's `●n ⋅ ◯k` with `k ≤ n`): the credit cell has
   fragments and an exclusive authority `●N`, and `Ghost.Valid` requires at most one authority
   and fragments `≤ N` when it is present. The judgments already quantify over **every** frame
   `rF` that composes; a frame that holds `●N` with exactly `N` fragments outstanding leaves no
   room for one more fragment, so no judgment can produce one. No definition of a judgment and no
   proof that keeps the ghost state of its precondition changes.

Variant 2 is used: it is sound for every judgment that preserves `Holds m' r' rF` for an arbitrary
`rF` (all of the above; `Upd` quantifies over every `Ghost.Ok` frame), including future ones, and
its blast radius is the `Ghost` structure (one more field: each anonymous `Ghost` and each
field-by-field `ext1` proof gets one more component, each hand-made `Ghost.Valid` one more conjunct).

**Credits.** `Ghost.cr : CCell` with `frag : Nat` (`credits n`, `◯n`) and `auth : Nat → Nat` (how
many authorities `●N` hold the value `N`; additive, so that validity is closed under dropping parts,
`Ghost.Ok.mono`). `CCell.Valid`: every count is at most 1, at most one value has an authority, and
the fragments are at most its value. `credits (a + b) = credits a ⋆ credits b` and `credits 0 = emp`
are equalities; `credits n` is dropped with `EUpd.drop`. There is no rule that creates a fragment.
`creditAuth N` (`●N`) is not given to programs: the adequacy theorem keeps it in the frame and gives
`main` `credits N` (`Holds.addCredits`). Kernel-checked regression
(`tests/roadmap/sep-full/CreditsCX.lean`): `¬ EUpd emp (credits 1)`, and the same for `Upd`.

**Room: obstruction in the current memory model** (found 2026-10-12; for the memory-model lane).
The requested design ("Σ room ≤ the free address space below `Placement.addrLimit`; a total
`alloc` of `k` bytes consumes `k` plus a padding bound, `free` returns it") is not sound in the
current model (`ZigLean/Mem/Basic.lean`), for three reasons:

1. *`free` cannot return room.* The fallback address of a new block is `alignUp Mem.top align`,
   and `Mem.top` is past every block, dead or live. Freed address space is reused only when the
   placement proposes it, never by the fallback.
2. *Other primitives consume the same space without room.* `rawAlloc`/`mmap` (`Mem.mapAddr` is
   `Mem.newAddr`) and an in-place `mremap` growth raise `Mem.top`. Their rules (precondition
   `emp`; `FAllocSpec`; the page, FBA and arena proofs) cannot re-establish `Holds` against a frame
   that holds room. Charging room to them (variant B) would weaken rules that hold today: rejected.
3. *The placement can exhaust the fallback.* An accepted proposal near `addrLimit` (natively the
   stack mapping sits just below `2^47`) raises `Mem.top` to about `addrLimit`, so a later fallback
   fails with any amount of free space below. A sound "free space" must count the placement's
   future proposals: `addrLimit - max(Mem.top m, every proposal for a block id ≥ m.blocks.size)`.

Coordinator decision (2026-10-12): the target is (A), a native-faithful separate stack region for
`alloc` (stack locals, thread-local instances, runtime cells) with its own bump/LIFO pointer, so
that room is the stack region's slack, authoritative in `Holds` exactly as credits are, consumed by
`alloc` and returned by `free` of the top block, with no change to the allocator rules (new
memory-model lane). Until (A) lands: (C), a premise of the adequacy theorem (`Full/Init`) about the
start memory, not a judgment parameter and not a new judgment. The room cell will then be a second
`CCell`-like component of `Ghost` whose authority is tied to the memory in `GOk`.

## Stack depth (stack-region lane; design approved 2026-10-12)

Total `allocStack`/`enterFrame` rules need a resource that guarantees the next stack block. The
model side (per-thread stack regions with a LIFO budget and a reserve) is
`docs/architecture-audit/memory-model.md` §MM-18; this section is the resource on top of it and
replaces the "room" half of §Credits and room above. Status: the model is implemented (MM-18
step 1: `Mem.stacks`, `alloc .stack` charges the budget, `Mem.withStack`); the resource below
is step 3, as an instance of the same authoritative-counter pattern as the credits.

**Why not splittable `room n` credits.** A credit that `alloc` consumes and `free` returns is
sound only if the freed block is the top of its thread's stack: a stack slot is free again only
when everything above it is gone. With splittable credits the logic cannot know that.
Counterexample (budget `c + c'`): `alloc b` (pay `c`), `alloc b'` (pay `c'`), `free b` (get `c`
back, but `b'` still lies above `b`, so the slack is still 0), then `alloc b''` with the credit
overflows. So the resource is the thread's depth itself, held exclusively, as a stack pointer
is in separation logic for assembly.

**Resources** (a new `Ghost` component, next to `cl` and the credits `cr`):

* `sp t S D`: thread `t` has the budget `S`, and its LIFO depth plus its cells is at most `D`
  (`Mem.used t ≤ D`). Exclusive: one fragment per thread with a budget. The cells (TLS
  instances, `errno`) are reserved when the budget is set, so the first fragment is
  `sp t S cells` and no later cell creation needs it.
* `ent t ℓ c o`: a live stack entry of `t`, pushed at logical depth `ℓ` with charge `c`; `o` is
  its block (`some b`) or a frame charge (`none`). Exclusive.
* `room t n := ∃ D S, sp t S D ⋆ ⌜D + n ≤ S⌝` is notation, not a resource: it does not split.
  A function that needs `k` bytes of stack is specified for every depth:
  `∀ D, D + k ≤ S → FTotalTriple (sp t S D ⋆ P) f (fun v => sp t S D ⋆ Q v)`.

**Holds** (a conjunct of `GOk`, the arena lane's `Res`/`Ghost`):

* every thread `t` with a budget has exactly one `sp t S D` in `r ⊔ rF`, with `S = S_t` and
  `Mem.used t ≤ D`;
* the `ent` fragments of `t` are exactly its live entries; in push order their logical intervals
  `[ℓ, ℓ + c)` follow each other, the last ends at or below `D`, and each entry's real end
  (`Mem.used` at its push plus `c`) is at or below its logical end `ℓ + c`.

**Rules** (`@[fsym]`, `Full/Block`, with the current thread `t`, below):

* `allocStack size align`, `c = size + align`:
  `sp t S D ⋆ ⌜D + c ≤ S⌝ ⊢ ⟨p⟩ sp t S (D + c) ⋆ ent t D c (some b) ⋆ up (bytesAt p A size …) ⋆ bext b …`
  (total: the model's check `used + c ≤ S` follows from `used ≤ D`).
* `free p` of that block: `sp t S (ℓ + c) ⋆ ent t ℓ c (some b) ⋆ bytes ⋆ bext ⊢ sp t S ℓ`. The
  fragment `sp t S (ℓ + c)` makes `b` the top: an entry pushed after `b` would have a logical
  interval above `ℓ + c` with positive charge, ending above `D = ℓ + c`. So the free pops `b`,
  and the depth drops to at most `ℓ`.
* `enterFrame`/`leaveFrame`: the same with `o = none` and `c = frameBase`.
* Every other primitive keeps `Mem.used` of every thread (the frame of the conjunct): a new
  `Tame` field, proved once per primitive.

**Not mintable without touching the judgments.** `GOk` requires exactly one `sp` per budgeted
thread somewhere in `r ⊔ rF`, so `EUpd emp (sp t S D)` fails in every memory (a second fragment
is invalid), and no judgment can produce an `sp` from nothing. Unlike the credits, this needs
no new conjunct in `EUpd`/`FTriple`/`FTotalTriple`/`CTriple`/`Upd`. The only introductions are
the start memory (`Full/Init`: `sp 0 S k₀` under `Mem.withStack S`, `k₀` the main thread's
cells) and the spawn rule (the child's `sp c S_c k_c`). Regressions: `¬ EUpd emp (sp 0 S 0)`,
`¬ (sp t S D ⋆ sp t S D')`, and a total `allocStack` from `sp t S D` with `D + c > S` is
unprovable (a memory with `used = D` throws `.stackOverflow`).

**The current thread.** The rules apply only when `t` runs. A sequential triple quantifies over
memories with any `m.current`, so the rule needs it from the precondition: knowledge `cur t`
(`m.current = t`), kept by every `MemM` primitive (none switches threads), given by `Full/Init`
(`cur 0`) and by the thread rules to each thread's own resources. Knowledge of another thread's
`cur` in an invariant is useless, not unsound (`Holds` fails while that thread does not run).
Open point for the CSL lane (step 5).

**Interim (C).** Until this lands, a total statement that allocates on the stack takes room as
a premise of the adequacy theorem. That premise must be about the run ("this run throws no
`.stackOverflow`", STK-01), not a resource that `free` returns: over today's model such a
resource is unsound (`memory-model.md` §MM-18, scenario 1).

## Ghost state: epoch ledgers (revocable allocator tokens)

### The problem

`FAllocSpec` quantifies over every token `I.tok` that `I.own` can coexist with. Two allocator
behaviours need the token to say something about the allocator's *current* state, which `own`
holds and the token does not see:

* **A token must name a region that the allocator granted.** The arena's `free` and `resize`
  start with `loadFirstNode().?`, which panics on an arena without a node: a fresh one, or one
  after `reset(.free_all)` (`docs/alloc-arena.md`, O-A). So `own ⋆ granted p k bs` must be
  unsatisfiable when the arena has no node, and more generally when this allocator did not grant
  the region at `p` in its current state: a `free` of a foreign slice is a permission violation.
* **A reset revokes every outstanding token.** After `reset`, the bytes of every grant are the
  allocator's again. A client that kept a token must not be able to use it with the new state.

Owned bytes and persistent knowledge cannot express either. Bytes are exclusive, so a token can
own some, but it cannot constrain bytes it does not own. Knowledge is monotone, so it cannot be
revoked. This is what ghost state is for: logical resources that live only in the proof.

### The design

`Res` gets a third component, `gh : Ghost`, with `Ghost := Nat → GCell` (names to cells). A cell
is an **epoch ledger of named grants** (`ZigLean/Sep/Full/Res.lean`, rules in `Ghost.lean`):

```
abbrev GRegion := Ptr × Nat × Frac × Nat × BlockKind
                    -- a region: start pointer, length, lent extent fraction, cell labels A, K
abbrev GMap := Nat → Option GRegion      -- grant id ↦ the region granted under it
structure GCell where
  auth : Nat × GMap × STag → Nat   -- how many authorities ●(e, M) with parent tag p
  frag : Nat × Nat × GRegion → Nat -- how many tokens ◯(e, i ↦ g): grant i of epoch e names g
  ep : Nat → Frac                  -- the parts of each epoch's token (§Epoch tokens)
```

* **Composition** is pointwise addition of both counts, so it is total, associative and
  commutative, with the empty ledger as unit. Two authorities for one name are ruled out by
  validity, not by composition.
* **Validity** (`GCell.Valid`): at most one authority; where an authority `●(e, M)` exists, every
  token `◯(e, i ↦ g)` of epoch `e` is recorded, `M i = some g`, and there is at most one per id;
  there is none of a later epoch. Tokens of an earlier epoch are valid: they are *stale*.
* **Finiteness** (`Ghost.Fin`): only finitely many names are in use. This gives a fresh name for
  a new ledger.
* **Assertions.** `gauth γ e M` owns `●(e, M)` at `γ`; `gfrag γ e i g` owns `◯(e, i ↦ g)` at `γ`.
  Neither owns bytes or knowledge. `up`, `emp`, `known` and the byte assertions own no ghost
  state.

`Holds m r rF` additionally requires `Ghost.Ok r.gh rF.gh`: the sum of the two ghost states is
valid and finite. No primitive changes the ghost state: every primitive rule keeps
`r.gh`, so the existing proofs only pass the field along.

**Ghost updates** change only ghost state. `Upd P P'` says that every resource of `P` can be
replaced, without touching its bytes and knowledge, by one of `P'` that is compatible with every
frame the old one was compatible with (Iris's frame-preserving update). `FTriple.upd` applies
one to a precondition, `FTriple.upd_post` to a postcondition, and `Upd.frame` frames one. The
ledger's updates:

| update | from | to | why it is frame-preserving |
|---|---|---|---|
| `Upd.alloc` | `emp` | `∃ γ, gauth γ 0 GMap.empty ⋆ epTok γ 0 1` | `Ghost.Fin` gives a name no frame uses |
| `Upd.issue g` | `gauth γ e M` with `M i = none` | `gauth γ e (M.set i g) ⋆ gfrag γ e i g` | the frame holds no token for `i`: `M` does not record it |
| `Upd.retire` | `gauth γ e M ⋆ gfrag γ e i g` | `gauth γ e (M.set i none)` | the frame holds no other token for `i` |
| `Upd.reassign g'` | `gauth γ e M ⋆ gfrag γ e i g` | `gauth γ e (M.set i g') ⋆ gfrag γ e i g'` | `retire`, then `issue` |
| `Upd.bump` | `gauth γ e M` | `gauth γ (e+1) GMap.empty ⋆ epTok γ (e+1) 1` | the frame holds no token and no part of an epoch token of a later epoch; its tokens of epoch `e` become stale |

A token of the current epoch names a recorded grant (`gfrag_mem`, as a triple rule `FTriple.mem`:
`gauth γ e M ⋆ gfrag γ e i g` gives `M i = some g`, by validity). Fresh ids: an invariant keeps
`M` finite (`GMap.Fin`, kept by `set`), and `GMap.Fin.fresh` gives an unused id.

### Epoch tokens

Each epoch of a ledger has **one whole token** `epTok γ e 1`, a fractional resource
(`epTok_add`: `epTok γ e (q + q') = epTok γ e q ⋆ epTok γ e q'`; `epTok_zero`: the empty part is
`emp`). It is minted with its epoch and nowhere else: `Upd.alloc` gives epoch `0`'s, `Upd.bump`
gives epoch `e + 1`'s. Validity (`GCell.EpOk`, under an authority of epoch `e`) bounds the parts of
every epoch's token by one in sum and forbids parts of a later epoch, so the frame of a bump
holds nothing of the new token and the minted whole is the only one. Hence `gauth_epTok_le`:
next to the authority, a part `q` held anywhere is at most `1`, and holding the whole token means
that nobody else holds a part of it. Tokens of old epochs stay valid and are useless, like stale
grant tokens. `EUpd.dropEp` forgets a part (it owns no bytes and no knowledge).

What it is for: an allocator that **takes a part of the token with each grant and gives it back
with the grant** learns from the whole token that it has no outstanding grant. The arena's
`reset` needs exactly that (`docs/alloc-arena.md`, reset: every node goes back to the child,
whose `free` takes the node's whole region, so no client may still own bytes in one). The part
travels as the allocator's fee (`FAllocInv.fee`, §The fee of a grant). Next to the authority, the
whole token and any other part of it leave that part empty (`gauth_epTok_whole`). A counted or
non-fractional token would not do: a whole token held by the allocator for each grant is
vacuous (the client cannot produce `epTok e 1` at reset while the allocator holds a part), and a
part the client can detach from its grant lets a client drop a grant and still show the whole
token.

### Use by an allocator with reset

An allocator whose `own` holds a ledger `γ` uses the invariant family
`I e := { own := own' e, tok p n … := ∃ i, gfrag γ e i (p, n) ⋆ … }` indexed by the epoch:

* `own' e` holds `gauth γ e M` and relates `M` to its state, e.g. "no node ⇒ no grant". A fresh
  allocator starts at `gauth γ 0 GMap.empty` (`Upd.alloc`). With `gfrag_mem`, a token of epoch
  `e` names a grant of `M`, so the allocator has a node: O-A is no longer a premise.
* The token names the region: `granted p k bs` holds a token for `(p, bs.size)`. A client can only
  have one for a region that this allocator granted in this epoch, so a `free`, `resize` or
  `remap` of a foreign slice (or of a slice of another length) has no precondition to stand on: it
  is a permission violation, not a case the allocator's code has to survive.
* `alloc` issues (`Upd.issue` under a fresh id), `free` retires (`Upd.retire`), and a successful
  `resize` re-points the grant at the new length (`Upd.reassign`).
* `reset` is specified as `{own' e ⋆ (the bytes of every grant)} reset {own' (e+1)}`, by
  `Upd.bump`. Every token of epoch `e` that the client still holds is stale afterwards. A stale
  token is useless: `FAllocSpec … (I e)` needs `own' e`, which no longer exists (the authority is
  exclusive and now at epoch `e + 1`), and `FAllocSpec … (I (e+1))` needs a token of epoch `e+1`.
  A use after a retaining reset is therefore a permission violation twice over: the client no
  longer owns the bytes, and its token belongs to a dead epoch.

Nothing in the ledger is specific to arenas: any allocator with a reset (a `FixedBufferAllocator`
`reset`, a pool, a stack allocator's `freeAll`) can take the same family, and a named token is
also what a `deinit` that requires every grant back needs.

### Why named grants with epochs

* **Revocation needs epochs.** In a frame-preserving logic, an update cannot invalidate a
  resource held by the frame. With a plain authoritative map (`●M`, tokens `◯(i ↦ g)`) a reset
  must collect every token. With epochs, the bump leaves the frame's tokens valid but stale, so a
  reset needs only the bytes back (which it needs anyway), not the tokens.
* **Named, not counted.** A counted token (`●(e, n)`, `◯e`) says only that some grant of the
  epoch is outstanding. It can then come with any slice the client owns, so a `free` of a foreign
  slice would have a precondition, and the allocator's code would have to handle it (the arena
  turned such a slice into junk). Naming the region makes the token the proof that this exact
  region was granted, as `std.mem.Allocator`'s contract requires.
* **Ids, not a set of regions.** The map is keyed by a grant id rather than being a set of
  regions, so issuing needs only an unused id (`GMap.Fin.fresh`), not a proof that the new region
  differs from every outstanding one, which would need disjointness facts about memory that
  clients hold.
* **Alternatives.** A per-allocator `Prop`-valued "issued" knowledge is monotone and cannot be
  revoked. Putting the ledger into `Mem` (a model of the allocator) is ruled out by the
  principle that only the OS primitives are trusted. Iris's general cameras would subsume the
  ledger; one fixed camera keeps the algebra small (no step-indexing, no higher-order ghost
  state), at the cost of adding a camera when another proof needs a different one.

## Concurrency (RC11 approximation, `ZigLean/Conc`)

* **Ownership by threads** (`Mem.Owns`, `Owned` in `Conc/Csl.lean`) is about legacy heaps. It
  carries over by putting `FHeap`s in the parts. A thread's part then owns its constraints too,
  so an atomic op of thread `t` on its own word keeps another part's constraints (`holds_after`
  generalises: the new location covers only `t`'s bytes). With several threads a retire can
  throw `.unspecified` (a racing access to the old location); a concurrent rule needs the
  constraint `(o, n)` over its word, as `apts` has.
* **Knowledge is thread-independent.** `KMono` holds for every step of every thread (spawn, join,
  futex and atomic ops do not touch block addresses). So `known` facts are stable under the rely
  and can live in any thread's ghost value or in `Proto.inv`. This is the Iris notion of a
  persistent proposition.
* **Shared atomic words** (`Conc/Word.lean`: `Word.Ok` requires "no other location overlaps").
  This is the constraint `(o, n)` for a word that no thread owns. The full-state version keeps the word in the
  protocol invariant as `apts` contents with tag `some (o, n)`.
* **A process-shared PageAllocator** then has `Proto.inv ⊇ ∃ v, hint ↦ₐ v ∗ addrOf v …`, and each
  thread's `alloc` is a `WP` proof that opens the invariant around the `unordered` load and the
  `cmpxchg`. The sequential `AllocSpec` below is the special case of one thread.
* **Race footprints.** Owning tags does not change `recordAccess`. Atomic accesses never race with
  each other (`racePair`), and plain accesses to a word in `inv` are excluded by ownership.

## Comparison

* **Iris / HeapLang**
  * Atomics are ordinary `l ↦ v` (sequentially consistent), shared through invariants.
  * Freed locations are never reallocated, so the persistent `meta l N x` (gen_heap) survives
    deallocation. This is the same argument as for our `known b A`.
  * Persistent propositions (□) are duplicable and stable, like `Know`.
* **iRC11 / ORC11 (Iris for RC11)**
  * Separate atomic points-tos (`l ↦at h`, with histories) next to non-atomic `l ↦ v`, with
    conversion rules. Mixed-size access is excluded by typing.
  * Here the model really has a mixed-size failure, so the layout must be owned. The byte tag is
    the minimal ghost state for it.
* **VST / CompCert**
  * Atomics use `atomic_loc` / `atomic_int_at` resources.
  * Comparing or casting a dangling pointer is undefined (`valid_pointer` side conditions), so VST
    never needs dead-block metadata.
  * Zig defines `@intFromPtr` of a dangling pointer, so we need it.
* **CN / VIP**
  * The VIP provenance model (PNVI-ae-udi) keeps an allocation table whose entries outlive the
    allocation. Integer–pointer casts and comparisons consult it.
  * Our `known` is the logical view of that table: per block, address only, monotone.
* **RefinedC (Caesium)**
  * `loc_in_bounds l n` is persistent knowledge about an allocation's bounds, separate from
    ownership. This is the same split as `known` (address knowledge) versus owned bytes.

## Migration impact on existing Sep proofs

1. **Nothing breaks now.** The prototype is new modules; no existing statement changes.
2. **Legacy rules lift unchanged** through `FTriple.ofTriple` and `Tame`. Every generated
   plain-memory primitive is `Tame`, and `Tame` is closed under `bind`. Loops need a `Tame` for the
   fixpoint, by `loop` induction like `loop_spec_mm`. That is mechanical, but not done here.
3. **Staging** (status on `codex/alloc-p4b-page`):
   1. Done (`Logic.lean`): `FTotalTriple` (`FTriple` and `FReturns`) with its structural rules,
      `FTotalTriple.ofTotal` (lifting a legacy `TotalTriple` of a `Tame` program), and `FLogic`,
      the `Logic` record over full-state assertions (`FLogic.partial`, `FLogic.total`). The modules
      stay proof-only like the rest of `ZigLean/Sep`, so they are not added to `ZigLean.lean`.
   2. Done (`AllocSpec.lean`, `Tame.lean`): `FAllocSpec` over `FAllocInv` (next section).
      `FAllocSpec.ofTotal` turns a legacy total `AllocSpec` of a `VTame` vtable into a full one
      (`AllocInv.toFull`). `tame` proves `Tame` for normalized generated code (`gen_norm`), and the
      OS mappings (`Os.mmap`, `munmap`, `mremap`) are `Tame`. (`FAllocSpec.ofTotal` is gone with
      block extents; the FixedBufferAllocator's `FBA.fallocSpec` is now a native full-state proof,
      `tests/roadmap/alloc-fba/AllocFba/Full.lean`, with the rules of `ZigLean/Sep/Full/Ops.lean`.) The page
      allocator's `free`, `resize` and `remap` are proved against it
      (`tests/roadmap/alloc-translated/PageSpec.lean`), and its `alloc` for alignments up to a
      page (`PageAlloc.lean`, `docs/alloc-page.md`; larger alignments: O5). The wrapper contracts and the FBA client stay on the legacy
      `AllocSpec`.
   3. Done (`Disjoint.lean`, `Triple.lean`, `Tame.lean`): `LiveDisjoint` in `FSeq`, `LDMono` in
      `Tame`, `Holds.apart` and `FTriple.apart`.
   4. Once everything uses `FTriple`, fold the tag into `Cell` and make `Triple := FTriple`. Every
      `bytesAt`-based lemma keeps its statement, because tags are "any" under `up`.
4. **Cost.** The atomic rules took about 500 lines (`Atomic.lean`) on top of the existing
   `Conc/Lemmas` run lemmas (`atomicLoadAt_ok`, `locIdx_found`, …). A `cmpxchg` rule follows the
   store's pattern (`casPrep` at choice 0 reads the newest message; on success, `insertM` at the
   end), and was not mechanised.

## Concrete changes `AllocSpec` needs

This builds on the FBA branch's O2 shape (`codex/alloc-translated-p4-fba` 02a845e5):
`AllocInv.tok : Ptr → Nat → Nat → Nat → Nat → BlockKind → Assn`, and
`granted I p k bs := ∃ A S K, regionIn p A S K (2^k) bs ∗ I.tok p bs.size k A S K`.

1. **Assertions become full-state.**
   * `AllocInv.own : FAssn` and `tok : … → FAssn`.
   * `granted I p k bs := ∃ A S K, up (regionIn p A S K (2^k) bs) ⋆ I.tok p bs.size k A S K`.
   * Regions keep their legacy definitions under `up`, so the region library and the wrapper
     proofs carry over by `ofTriple` (the wrappers' `memsetUndef`, `memcpy` and `storeItem` are
     `Tame`).
2. **The logic.** Make `Logic.T` range over `FTriple`/`FTotalTriple`. `Logic.congr` quantifies
   over `FSeq` memories.
3. **PageAllocator (O1, O3).**
   * `I.own := ∃ h a, apts addr_hint h ⋆ hintKnown h a`. Here `hintKnown` is `addrOf` for the
     hint pointer, plus `⟪h's address ≡ 0 mod page⟫`, which discharges the `@ptrFromInt`
     alignment check.
   * At program start `addr_hint` is `null` with tag `none`.
   * `alloc`'s `cmpxchg` keeps `I.own` with the new mapping's `known` (taken by `know_intro`
     from the fresh mapping before it is granted).
   * `free` keeps `I.own` unchanged (it owns only knowledge of the mapping).
   * With pointer-valued atomics, `apts` gets a `Ptr` variant.
4. **PageAllocator (O2).**
   * `tok p n k A S K := ⟪K = .mapped p.off ∧ S = p.off + alignUp n P ∧ P ∣ A⟫ ⋆ up (regionIn (p.add n) A S K 1 tail)`.
   * The tail ownership pins the mapping size. When the tail is empty, the pure facts `S` and
     `K` pin it, which closes the `munmap`-prefix counterexample.
5. **FixedBufferAllocator.** Drop the pin byte. Put `known buf A` in `I.own`, and prove
   `@intFromPtr(buffer.ptr + end_index)` by `FTriple.ptrAddr`.
6. **Overlap checks.** Use `Holds.apart` / `FTriple.apart` (with `LiveDisjoint` from placement)
   instead of the placement premise.
7. **Size bounds.** These come from the upstream bugs in `docs/alloc-page.md`. Add the
   preconditions `len + 2^k ≤ 2^64 - P` for `alloc` and `n + P - 1 < 2^64` for `resize`/`remap`.

Items 1, 2, 4 and 7 are done (`FAllocSpec`, `PageSpec.tok`, `PageSpec.legacy.fits`). Item 5 is
not needed for the lifted FBA proof, which keeps its pin byte. Item 3 is done for alignments up to
a page (`PageAlloc.own`). Item 6's rule exists (stage 3); the FBA proof still uses its premise.

## Limits

* Atomic rules are sequential (choice 0). `Atomic.lean` has load and store of 64-bit integer
  words; `AtomicPtr.lean` has the pointer-valued points-to `aptsE`, the `unordered` load
  (`FTriple.atomicLoadUnorderedEnc`) and the strong pointer `cmpxchg` that succeeds
  (`FTriple.cmpxchgPtr`). `AtomicRules.lean` adds RMW (`atomicRmwW`, `atomicRmwAsW`), pointer
  `.Xchg` and weak pointer `cmpxchg` (`atomicXchgPtrW`, `cmpxchgWeakPtrW`) and `unordered`
  integer/packed loads (`atomicLoadUnorderedW`/`AsW`), all on any owned word. `Seq.lean` reads a one-thread scheduler run
  with the oracle `0` as a `MemM` program (`Sched.run_eq_seqRun`, for a `ThreadFree` function).
* `FTriple.ptrFromAddr` frames everything but says nothing about the result's provenance: an
  ambiguous address gives `⟨none, n⟩` (O4 fix), so a proof that dereferences the result needs
  its own argument that one block covers the address.
* `Tame` for loops and calls (`loop`, `callM`) is not proved. The lifting theorem is per program.
