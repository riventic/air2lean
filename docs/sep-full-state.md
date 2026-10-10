# Separation logic over the full state

Status: proof-only modules in `ZigLean/Sep/Full/`: the prototype (`Res`, `Triple`, `Atomic`, `Toy`)
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

1. **Owned bytes with their atomic layout.** `heap : FHeap` maps each location to an `FCell`,
   which is the legacy `Cell` plus `atom : Option (Nat × Nat)`, the start and length of the atomic
   location covering the byte (`tagOf (shapes m)`). Owning a byte also owns its atomic layout.
   * The frame rule keeps the layout of the frame's bytes.
   * A precondition can require the layout that an atomic op needs. The atomic points-to is
     `apts p v`: the 8 bytes at the 8-aligned `p` hold `v`, and their tag is either `none` (no
     atomic op yet) or exactly `(p.off, 8)`.
   * An atomic op on owned bytes creates or reuses a location over those bytes only, so it
     changes only owned tags.
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

* `m.fheap = r.heap ∪ rF.heap` exactly, and the two heaps are disjoint;
* both knowledge sets are true in `m`, i.e. contained in `Mem.kn m` (every block, live or dead,
  with its address).

The memory invariant is `Mem.FSeq := Mem.Seq ∧ ShapesWF (shapes m) ∧ Mem.LiveDisjoint m`: every
atomic location has a byte, no two overlap, and no two live blocks share an address (stage 3,
below). `locIdx` only creates a location where none overlaps, and every new block is placed clear
of the live ones, so every reachable memory satisfies this.

`FTriple P c Q` (in `ZigLean/Sep/Full/Triple.lean`) is `Triple` with `Holds` in place of the heap
split and `FSeq` in place of `Seq`.

```
FTriple P c Q := ∀ m r rF, Holds m r rF → P r → m.FSeq →
  match (c.run m).run with
  | none => True | some (.error _) => False
  | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq
```

### Why tags on bytes, and not a separate `↦ₐ` resource

An atomic location is a property of particular bytes. A separate atomic resource disjoint from
the bytes would need an extra exclusion invariant: plain ownership and atomic ownership of
overlapping bytes must not coexist, and mixed sizes must be ruled out. Putting the tag on the
byte gets this for free:

* disjointness of byte ownership is disjointness of layout ownership;
* `apts` is just "owned bytes with a uniform tag";
* plain loads and stores ignore tags, so every legacy rule still applies.

`apts` is the derived `↦ₐ`. It also frames like bytes.

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
| `Ghost` | `Upd.alloc`/`issue`/`retire`/`bump`, `gfrag_count`, `FTriple.upd`/`upd_post`/`count`, `Upd.frame` | epoch ledgers (§Ghost state): frame-preserving updates; a token of the current epoch shows one is outstanding |
| `Atomic` | `locIdx_post`, `locIdx_noErr_tag` | `locIdx` at bytes with a uniform tag: no error, new location only over those bytes, newest message = the bytes |
| `Atomic` | `FTriple.atomicLoad` | `{apts p v} atomicLoadAt 0 ord 8 p {w. ⟪w = v⟫ ⋆ apts p v}`, any order |
| `Atomic` | `FTriple.atomicStore` | `{apts p v} atomicStoreAt 0 ord 8 p w {apts p w}`, any order |
| `AtomicPtr` | `FTriple.atomicLoadUnorderedEnc`, `FTriple.cmpxchgPtr` | pointer-valued `aptsE`: the `unordered` load reads the value; a strong `cmpxchg` with the held value succeeds |
| `Seq` | `Sched.run_solo`, `Sched.run_eq_seqRun`, `ThreadFreeC.*` | a one-thread scheduler run of a `ThreadFree` concurrent function is its sequential reading |
| `Conc` | `CTriple.bind`, `liftMem`, `pick_bind`, `step`, `know_intro`, `forget`, `conc_norm` | full-state triples for a concurrent function called in one thread (`Sched.soloRun`, oracle `0`) |
| `Toy` | `toyAlloc_spec`, `toyFree_spec`, `cycle_spec` | the hint protocol: alloc, free, alloc from the invariant |
| `Toy` | `apts_layout`, `inv_no_odd` | **O3**: a memory with a 4-byte location at the hint holds no `inv` |
| `Toy` | `addrOf_block`, `inv_last_block`, `inv_no_lost` | **O1**: a memory whose remembered pointer's block is missing holds no `inv` |
| `Toy` | `start_inv`, `cycle_from_start` | nonvacuity: a concrete start memory holds `inv`, so the real alloc–free–alloc run satisfies the post |

The toy (`Toy.lean`) has the shape of `PageAllocator.map`'s hint protocol. It reads the hint
atomically, then reads the last mapping's pointer from `last` and takes its address (a dangling
pointer after `free`). It checks that the hint is that address plus a page (a panic otherwise),
maps a page, publishes the new hint atomically, and stores the mapping in `last`. Its invariant is:

```
inv hint last := ∃ q a, apts hint (ofInt (a + 4096)) ⋆ (up (pts last 8 q) ⋆ addrOf q a)
addrOf ⟨some b, off⟩ a := ∃ A, ⟪A + off = a⟫ ⋆ known b A     -- knowledge only
```

The invariant owns only knowledge of the mapping, so `toyFree_spec` keeps it, and `cycle_spec`
(alloc, then free, then alloc) goes through. Compare the legacy obstruction theorems:
`alloc_no_triple_at_start` builds a memory `odd`, and `alloc_no_triple_after_free` builds
`hintedLost`, each with the same heap as a good memory. In the full logic both differ from the
good memory in the resources a precondition can see. `odd` differs in the hint bytes' tag
(`inv_no_odd`); `hintedLost` lacks the knowledge `known 6 A` (`inv_no_lost`).

The toy keeps the pointer in a plain slot and the hint as a `u64`. The translated
`PageAllocator` uses the thread model's pointer atomics (`ZigLean/Mem/AtomicPtr.lean`, C09) and
an `unordered` pointer load (`ZigLean/Conc/AtomicWord.lean`). There the two slots become one
`apts` with a `Ptr` value. The same `locIdx_post` argument applies: an `unordered` read at choice
0 reads the newest message. The pointer `cmpxchg` compares identities (`ptrValEq`), so a
sequential run that compares the value it just read needs no address.

## Soundness

* **Frame rule.** The frame `rF` is in the definition, so `FTriple.frame` holds for every program.
  It now covers the frame's tags and knowledge. It is non-trivial for primitives because each
  primitive rule must re-establish `Holds m' r' rF` for an arbitrary `rF`:
  * the frame's bytes are unchanged;
  * their tags are unchanged, because a new location covers only owned bytes (`holds_after`,
    `locIdx_post`'s tag equation);
  * the frame's knowledge stays true (`KMono`: blocks are only pushed or replaced with the same
    address).
* **Lifting.** `FTriple.ofTriple` uses the legacy triple on the erased heaps. `Tame` gives
  `shapes m' = shapes m`, so the frame's tags in `m'` are the tags in `m`; `KMono` gives the frame's
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
  one (`tagOf_of_mem`), so a uniform tag over owned bytes determines what `locIdx` finds
  (`overlap_eq`).
* **Adequacy.** A client proof starts from a memory that holds its precondition. `start_inv`
  shows such a memory for the toy, and `cycle_from_start` applies the spec to the real run. A
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
  LiveDisjoint` (stage 3, done). `Holds.apart` turns ownership of a byte in each of two blocks
  into `A + S ≤ A' ∨ A' + S' ≤ A`, and the rule
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

## Ghost state: epoch ledgers (revocable allocator tokens)

### The problem

`FAllocSpec` quantifies over every token `I.tok` that `I.own` can coexist with. Two allocator
behaviours need the token to say something about the allocator's *current* state, which `own`
holds and the token does not see:

* **A token must imply that the allocator has issued something.** The arena's `free` and
  `resize` start with `loadFirstNode().?`, which panics on an arena without a node: a fresh one,
  or one after `reset(.free_all)` (`docs/alloc-arena.md`, O-A). So `own ⋆ granted p k bs` must be
  unsatisfiable when the arena has no node.
* **A reset revokes every outstanding token.** After `reset`, the bytes of every grant are the
  allocator's again. A client that kept a token must not be able to use it with the new state.

Owned bytes and persistent knowledge cannot express either. Bytes are exclusive, so a token can
own some, but it cannot constrain bytes it does not own. Knowledge is monotone, so it cannot be
revoked. This is what ghost state is for: logical resources that live only in the proof.

### The design

`Res` gets a third component, `gh : Ghost`, with `Ghost := Nat → GCell` (names to cells). A cell
is an **epoch ledger** (`ZigLean/Sep/Full/Res.lean`, rules in `Ghost.lean`):

```
structure GCell where
  auth : Nat × Nat → Nat   -- how many authorities ●(e, n): current epoch e, n tokens outstanding
  frag : Nat → Nat         -- ◯e, counted: how many tokens of epoch e this resource holds
```

* **Composition** is pointwise addition of both counts, so it is total, associative and
  commutative, with the empty ledger as unit. Two authorities for one name are ruled out by
  validity, not by composition.
* **Validity** (`GCell.Valid`): at most one authority; where an authority `●(e, n)` exists, at
  most `n` tokens of epoch `e` exist, and none of a later epoch. Tokens of an earlier epoch are
  valid: they are *stale*.
* **Finiteness** (`Ghost.Fin`): only finitely many names are in use. This gives a fresh name for
  a new ledger.
* **Assertions.** `gauth γ e n` owns `●(e, n)` at `γ`; `gfrag γ e` owns one `◯e` at `γ`. Neither
  owns bytes or knowledge. `up`, `emp`, `known` and the byte assertions own no ghost state.

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
| `Upd.alloc` | `emp` | `∃ γ, gauth γ 0 0` | `GFin` gives a name no frame uses |
| `Upd.issue` | `gauth γ e n` | `gauth γ e (n+1) ⋆ gfrag γ e` | the frame holds at most `n` tokens of epoch `e` |
| `Upd.retire` | `gauth γ e n ⋆ gfrag γ e` | `gauth γ e (n-1)` | the frame holds at most `n - 1` |
| `Upd.bump` | `gauth γ e n` | `gauth γ (e+1) 0` | the frame holds no token of a later epoch; its tokens of epoch `e` become stale |
| `Upd.count` | `gauth γ e n ⋆ gfrag γ e` | `⟪1 ≤ n⟫ ⋆ gauth γ e n ⋆ gfrag γ e` | validity |

### Use by an allocator with reset

An allocator whose `own` holds a ledger `γ` uses the invariant family
`I e := { own := own' e, tok := … ⋆ gfrag γ e }` indexed by the epoch:

* `own' e` holds `gauth γ e n` and relates `n` to its state, e.g. "no node ⇒ `n = 0`". A fresh
  allocator starts at `gauth γ 0 0` (`Upd.alloc`). With `Upd.count`, a token of epoch `e` gives
  `n ≥ 1`, so the allocator has a node: O-A is no longer a premise.
* `alloc` issues (`Upd.issue`), and `free` or a shrink to nothing retires (`Upd.retire`).
* `reset` is specified as `{own' e ⋆ (the bytes of every grant)} reset {own' (e+1)}`, by
  `Upd.bump`. Every token of epoch `e` that the client still holds is stale afterwards. A stale
  token is useless: `FAllocSpec … (I e)` needs `own' e`, which no longer exists (the authority is
  exclusive and now at epoch `e + 1`), and `FAllocSpec … (I (e+1))` needs a token of epoch `e+1`.
  A use after a retaining reset is therefore a permission violation twice over: the client no
  longer owns the bytes, and its token belongs to a dead epoch.
* A foreign free (a slice the allocator did not issue in this epoch) is a permission violation:
  no token of the current epoch exists for it.

Nothing in the ledger is specific to arenas: any allocator with a reset (a `FixedBufferAllocator`
`reset`, a pool, a stack allocator's `freeAll`) can take the same family, and a counted token is
also what a `deinit` that requires every grant back needs.

### Why counted tokens with epochs

* **Revocation needs epochs.** In a frame-preserving logic, an update cannot invalidate a
  resource held by the frame. With a plain authoritative count (`●n`, tokens `◯1`) a reset must
  collect every token. With epochs, the bump leaves the frame's tokens valid but stale, so a reset
  needs only the bytes back (which it needs anyway), not the tokens.
* **Counts, not sets.** The specification's `free` only needs "some token of this epoch exists",
  and `reset` needs no list of grants. A set of regions (`●S`, `◯{x}`) would also work but makes
  the client track which grants are outstanding.
* **Alternatives.** A per-allocator `Prop`-valued "issued" knowledge is monotone and cannot be
  revoked. Putting the ledger into `Mem` (a model of the allocator) is ruled out by the
  principle that only the OS primitives are trusted. Iris's general cameras would subsume the
  ledger; one fixed camera keeps the algebra small (no step-indexing, no higher-order ghost
  state), at the cost of adding a camera when another proof needs a different one.

## Concurrency (RC11 approximation, `ZigLean/Conc`)

* **Ownership by threads** (`Mem.Owns`, `Owned` in `Conc/Csl.lean`) is about legacy heaps. It
  carries over by putting `FHeap`s in the parts. A thread's part then owns its tags too, so an
  atomic op of thread `t` on its own word does not change another part's tags (`holds_after`
  generalises: the new location covers only `t`'s bytes).
* **Knowledge is thread-independent.** `KMono` holds for every step of every thread (spawn, join,
  futex and atomic ops do not touch block addresses). So `known` facts are stable under the rely
  and can live in any thread's ghost value or in `Proto.inv`. This is the Iris notion of a
  persistent proposition.
* **Shared atomic words** (`Conc/Word.lean`: `Word.Ok` requires "no other location overlaps").
  This is `TagOk` for a word that no thread owns. The full-state version keeps the word in the
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
      OS mappings (`Os.mmap`, `munmap`, `mremap`) are `Tame`. The FixedBufferAllocator gets
      `FBA.fallocSpec` this way (`tests/roadmap/alloc-fba/AllocFba/Full.lean`). The page
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
   * At program start `addr_hint` is `null` with tag `none` (the analogue of `start_inv`).
   * `alloc`'s `cmpxchg` keeps `I.own` with the new mapping's `known` (taken by `know_intro`
     from the fresh mapping before it is granted).
   * `free` keeps `I.own` unchanged (`toyFree_spec`'s argument).
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
  (`FTriple.cmpxchgPtr`). There is no RMW rule. `Seq.lean` reads a one-thread scheduler run
  with the oracle `0` as a `MemM` program (`Sched.run_eq_seqRun`, for a `ThreadFree` function).
* `FTriple.ptrFromAddr` frames everything but says nothing about the result's provenance: an
  ambiguous address gives `⟨none, n⟩` (O4 fix), so a proof that dereferences the result needs
  its own argument that one block covers the address.
* `Tame` for loops and calls (`loop`, `callM`) is not proved. The lifting theorem is per program.
