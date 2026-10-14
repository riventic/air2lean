# Threads in the full-state separation logic

Status: design (Plan A, phase A4: one proof logic; `~/.cache/air2lean/handoffs/plans/architecture-ABC.md`)
and the first library modules (`ZigLean/Sep/Full/Thread.lean`, `ZigLean/Sep/Full/ThreadOwned.lean`).
The sequential full-state logic is [sep-full-state.md](sep-full-state.md); `fsym` is
[proof-automation.md](proof-automation.md).

## Today

The concurrent proofs have two layers.

* **Proofs over all schedules** (`ZigLean/Conc/Logic.lean`): a protocol `Proto` with an invariant
  on the ghost values and the whole memory, and `Proto.WP t x Q G m n`, a weakest precondition of
  thread `t` that holds at every stop. `run_safe` / `run_sound` turn it into statements about
  `Sched.run`. This layer has no heap assertions and stays as it is.
* **Concurrent separation logic** over the legacy `Heap` (`ZigLean/Conc/Own.lean`, `Csl.lean`,
  `Lock.lean`, `LockRules.lean`, `Detach.lean`, `Transfer.lean`, `TlsLemmas.lean`,
  `SpawnLemmas.lean`, `Witness.lean`, `Unroll.lean`; about 7.5k lines):
  * `Mem.Owns m t h`: every recorded access to a byte of `h` happened before `t`'s clock;
  * `TTriple P c Q`: `Triple` with ownership in place of `SingleThread`, plus `StepIn hF m m'`
    (the step touches no frame byte and changes no other thread's clock);
  * `Owned own m`: the threads' parts `own : ThreadId → Heap`, disjoint and owned;
  * `WP.liftMem_owned`: a `MemM` step of thread `t` with a `TTriple` on `own t`.

  Its clients are `Proofs/{Sync,Threadsync,Threads,Cancel,Detach,Iogroup}` and the roadmap tests
  `spawn-failure`, `thread-locals`, `thread-tuples`, `detached-threads`, `rwlock-contracts`,
  `sync-contracts`, `shared-reclamation`, `pointer-atomics` (about 35k lines).

`TTriple` is the legacy logic in a thread: its assertions are legacy `Assn` (cells that carry
their block's size), so it has none of the full-state resources: atomic tag constraints, block
knowledge (`known`), extents (`bext`, `bshare`), ghost ledgers, byte claims. Plan A deletes it
(A7). This document restates it over `Res`.

## The thread triple `FTTriple`

```
FTTriple P c Q := ∀ m r rF, Holds m r rF → P r → m.current < m.clocks.size →
    m.Owns m.current r.heap.erase →
  match (c.run m).run with
  | none => True | some (.error e) => e = .stackOverflow
  | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.Owns m'.current r'.heap.erase ∧
      FStepIn rF.heap.erase m m' ∧ FPres m m'
FPres m m' := (ShapesWF (shapes m) → ShapesWF (shapes m')) ∧ (m.LiveLayout → m'.LiveLayout)
```

* **The same resources and the same `Holds`** as `FTriple`: a thread's part is a `Res` (bytes
  with tag constraints, knowledge, ghost state). Every assertion of the full-state library
  (`up`, `pts`, `apts`, `known`, `bext`, `bshare`, `gauth`, `bclaim`, …) is a thread assertion.
* **Ownership is about bytes only.** `Mem.Owns` reads the erased heap. Knowledge needs no clock: a
  block's address never changes and no step of any thread removes a block (`KMono`), so `known` is
  thread-independent (an Iris persistent proposition) and may sit in any part or in the protocol's
  rest. Ghost state lives only in the proof and is never accessed, so it needs no clock either.
* **The memory invariant.** `FSeq` (`Seq ∧ ShapesWF ∧ LiveLayout`) does not hold in a concurrent
  run (`Seq` is one thread). A thread triple only asks for `current < clocks.size` (as `TTriple`)
  and promises to *keep* `ShapesWF` and `LiveLayout` (`FPres`); a primitive keeps them for the
  reasons given in sep-full-state.md §Soundness (`Tame`: shapes unchanged, `LDMono`).
* **Race freedom** is the `FStepIn` conjunct (`TTriple`'s `StepIn`, generalized in S1 below): no
  new footprint entry touches a frame byte, no other thread's clock changes, the thread's own
  clock only grows, the atomic locations over the frame stay.

### One logic: the sequential triple is a special case

`FTTriple.toFTriple : FTTriple P c Q → FTriple P c Q`. A sequential memory (`FSeq`) is a
concurrent one in which the current thread owns everything (`SingleThread`: every entry is its
own and happened before its clock), and `FStepIn` plus `FPres` give `FSeq` after the step. So a
thread rule is a sequential rule; there is no second assertion language, no second `Holds`, and
the frame rule, `Upd`/`EUpd` (ghost and extent updates), `know_intro` and the structural rules
are the same proofs over the same `Res` algebra.

### Why `FTotalTriple` does not imply `FTTriple` (and what the backend must do)

The converse fails, so `FTTriple` is not an `FLogic` instance (`FLogic.ofTotal`). A sequential
triple may read a byte that the frame owns as long as the precondition guarantees that the byte is
live: `bshare b q k` keeps block `b` live with `k` bytes, and `FTotalTriple (bshare b q k)
(load u8 1 ⟨b, 0⟩) (fun _ => bshare b q k)` holds (the load reads a frame byte and changes
nothing). In a concurrent run another thread may have written that byte concurrently: the load
races and gives `.illegal`. A thread rule must also say that the step touches only owned bytes,
which a sequential triple does not say. So:

* thread rules for **primitives** come from their sequential triples and their **locality**
  (`Full/ThreadStep.lean`, S2 below): the thread owns what the step touches, so the step runs in
  the concurrent memory as in the same memory without its record of accesses. Where no native
  rule exists yet, there is no thread rule (the bridge from legacy `TTriple` rules is gone);
* **`fsym` on thread triples** needs a backend whose step rules are thread rules: an `@[fsym]`
  rule with an `FTTriple` conclusion, and the structural steps over a record `TLogic`
  (`FLogic` without `ofTotal`, with `toPartial := toFTriple`). That is an engine change in
  `Full/Auto.lean` (fsym owner; requested through the coordinator). Generated thread bodies are
  short today (the client steps are single primitives under `WP.liftM_owned`), so the backend is
  not on the critical path of the migration.

### Decision (T-ctriple, R2): `CTriple` becomes the stop-wise thread triple

Today `CTriple P x Q := ∀ n, FTriple P (Sched.soloRun n x) Q` (`Full/Conc.lean`): a sequential
statement about a `ConcM` body read in the caller's thread (oracle choice `0`, no other thread
between its stops). Its clients are `PageAlloc`'s `alloc`, the arena and `sep-auto/Conc`.

**Non-solo stops fail closed (done ahead of R2; audit `structure-2026-10-13.md` #1).** The
in-thread reading answers only solo ops (`yield`, a `choose`, a `pick`): `Sched.soloResp` is
`none` for every other op, and a stop at a spawn, join, futex wait or wake, gate or async choice
reads as `.illegal` (`soloTree`, and `seqTree` alike). Before, it answered a spawn with `.ok 0`
and a join or a wait at once, so `CTriple emp (sync (.spawn t)) (fun r => ⟪r = .ok 0⟫)` was
provable. Now no `CTriple` with an admissible precondition holds across such a stop
(`tests/roadmap/sep-full/SoloSpawnCX.lean`: `no_triple`, `no_spawn_triple`). No existing proof
relied on the old answers: none of the clients spawns, joins or waits.

**Why not `∀ n, FTTriple P (soloRun n x) Q`** (the first plan, withdrawn): `Proto.WP` resumes a
thread at each sync stop in an *arbitrary* memory `m₁` (other threads ran) and for a pick with
*any* `c < count m₁` (`Conc/Logic.lean`, `Safe`/`Step`). A thread triple of the uninterrupted
`soloRun` from `m` says nothing about the continuation `k c m₁`, so no rule for a thread follows;
its only consumer would stay the sequential caller, which the current definition already serves.

**The definition (R2).** `CTriple P x Q` is a thread triple over the run tree `x n m`, stop by
stop: from every memory where the thread owns `P` (`Holds`, `FConc`, `Owns`), the segment up to
the next stop (or the result) is an `FTTriple` segment (the frame kept, race free); at a pick
stop the thread holds some `r'`, and for **every** memory `m₁` and frame `rF₁` in which it still
owns `r'` (`Holds m₁ r' rF₁`, `FConc`, `Owns`) and every `c < max 1 (count m₁)` (the in-thread
answer, or any in a memory that covers its messages, `Mem.MsgCov` below), the rest `k c m₁` is
again such a run. A stop of another kind (yield, futex, spawn, join, …) has no case
(the definition is `False` there: fail closed; those belong to protocols). Consequences:

* the **old statement follows** (`m₁ = m'`, `rF₁ = rF`, `c = 0`), so every existing `CTriple`
  statement is kept or strengthened (the strength examples restate them word for word);
* **`WP.call_fowned`**: a thread `t` of a protocol whose invariant keeps the thread's part
  (`FOwned`) runs a `CTriple` function inside `Proto.WP`. Allocator specifications
  (`FAllocSpec`) become usable inside threads.

**What it needs.** `FTriple`/`FTotalTriple` rules are not thread rules (above), so:

* **S1 — race relation and atomic thread rules** (csl lane: `Conc/Clock`, `Full/Thread*`,
  `Full/Atomic`, `Full/AtomicPtr`, `Full/AtomicRules`). `FTTriple`'s race conjunct is the legacy
  `StepIn`, which fixes `atomics`, `seen` and `nextMsg`; every atomic op changes them, so no
  atomic thread rule is provable today. A generalized relation for `FTTriple` lets a step change
  the atomic locations over non-frame bytes (each location keeps its index; the locations over
  frame bytes, the other threads' `seen` entries stay), with `nextMsg` only growing; the legacy
  layer keeps `StepIn`. Then the atomic rules on owned words are proved once as thread rules
  (the owner's access does not race, `locIdx` does not retire under the word's tag) and the
  sequential `FTriple` rules follow by `toFTriple`.

  **The relation (done): `FStepIn hF m m'`** (`ZigLean/Conc/Clock.lean`), the race conjunct of
  `FTTriple` and of `ThreadLocal`, and what `WP.liftMem_fownedS` hands its continuation. It keeps
  everything `StepIn hF` says about the threads, their clocks and the frame's bytes, and
  generalizes three things:
  * the atomic locations (`AMap hF m m' σ`): a location whose bytes are all the frame's stays as
    it is; the others may change their messages or be retired; a new one has a byte and none of
    the frame's; the ones that stay keep their order (`σ`, their new indices) and the other
    threads' views (`seen`) move with them; the message counter only grows. The first location
    with a property of its bytes stays the first one (`AMap.first_iff`), so a lock word's
    location survives every step of another part's owner (`LockWord.loc_fstep`);
  * the record of accesses: an old entry stays or is narrowed (`FootprintEntry.Narrows`: part
    of its bytes, an earlier clock, as `Mem.forgetFrom` does), a new one is the current thread's,
    touches no byte of the frame and is not a write to a `const` global (`Mem.IsConst`);
  * `const` globals: no block of `m` becomes one (new blocks may). With the new-entry clause this
    is the step's half of the `const` ruling (decision (a) below): no step of a thread records a
    write to a `const` global, so a reader of one races with nobody.

  A `StepIn` that writes no `const` global and makes none is an `FStepIn` (`FStepIn.of_stepIn`);
  the primitives' locality gives it directly (`FStepIn.recordAt`, `write`, `setBlock`,
  `afterAlloc`, `kill`). `ThreadLocal.loadBytes` takes a read kind (`hk`, decided by default): a
  `loadBytes` checks no `const` global. Ownership (`Mem.OwnsC.fstep`) and a lock's invariant
  (`LockWord.WInv.stepIn`, `Owns.stepIn`) only need the clock bounds of the entries, which a
  narrowing keeps (`Narrows.touches`, `Narrows.clock`, `PlainLe.fstep`).

  **Atomic thread rules (done, step 5; coordinator ruling after agent #10).** Atomics are the
  exception to "a thread rule is `ofSeq` of the sequential rule": an atomic op reads the record
  of accesses beyond its race check (`locIdx` asks `plainSince`/`plainClock` whether and with
  which clock to add a message; `retireAt` asks `ALoc.overAt`), so its run from `m` and from
  `m.noFp` differ beyond the record (messages, release clocks, hence clocks after an acquire),
  and no `ThreadLocal` holds. So each op is proved natively, **once**: one analysis of its run at
  choice `0` (`atomicLoad_run`, `atomicStore_run`, `cmpxchgHit_run`, `atomicRmw_run`,
  `atomicXchgPtr_run`, `cmpxchgWeakPtr_run`, `atomicLoadUnordered_run`), for every memory where
  the thread owns the word (`Mem.Owns`: the access races with nothing, `Owns.noRace`). It gives
  the thread rule of a `wpts`/`wptsE` word of any tag constraint (`FTTriple.atomicLoadW`, …, by
  `FTTriple.of_step`); the `apts`/`aptsE` thread rules are those with the stronger precondition
  (`FTTriple.pre`), and every sequential rule is a thread rule read sequentially (`.toFTriple`).
  The ops that have no `wpts` rule (`atomicLoadPtr`, `cmpxchgPtr`, `atomicLoadUnorderedEnc`) are
  `apts` thread rules only, and the typed ops (`atomicLoadAs`, `atomicRmwAs`, `atomicStoreAs`,
  `atomicLoadUnorderedAs`) are the integer thread rules with the decode. Choice `0` needs no
  floor argument: it is the newest message, which has the block's bytes (`locIdx` adds a message
  when they differ), so the owner reads and writes its bytes as a plain access. The step is an
  `FStepIn` of every frame without the word's bytes (`ZigLean/Conc/Clock.lean` §The steps of an
  atomic op: `FStepIn.locIdx` in every branch, `observe`, `acq`, `loadM`, `insertLast`,
  `storeM`, `rmwM`; the tail of a write is `write_newest`). **Mixed-size accesses** (MM-21): an
  atomic op on a word under a location of another offset or size retires that location when
  every recorded access to the bytes the op shares with it happened before the op
  (`ALoc.overAt`, LLVM's per-byte model); accesses to the location's other bytes, which after a
  reuse belong to other objects, do not matter. The owner of the word has that
  (`ALoc.overAt_of_owns`), so `locIdx` never throws at an owned word (`locIdx_noErr_word`), and
  the `CTriple` picks extend to `wpts`/`wptsE` (`CTriple.pick_loadW`, …). A genuine mixed-size
  race (an access to the op's bytes concurrent with it) still throws `.unspecified`.
  Kernel-checked: `tests/roadmap/sep-full/MixedSizeCX.lean` (`arena_reads`: thread 1 plainly
  wrote bytes `8..16` of a stale 16-byte location concurrently, thread 0's load of bytes `0..8`
  reads the word, and the `wpts` thread rule holds there; `race_throws`: thread 1's concurrent
  16-byte atomic access keeps the load `.unspecified`).
* **S2 — primitives as thread-total rules** (csl lane, new files or additive edits to
  `Ops`/`Block`/`Arr`/`Mmap`; existing statements kept): `load`/`store`/`ptrProject`/arrays/
  slices/`cload`/`ptrAddr`/`alloc`/`free`/`mmap`/`munmap`/`mremap` as `FTTotalTriple`, the
  `FTotalTriple` rules derived by `toFTotalTriple`. A `StateT.lift` step of a `Result` touches
  no memory and is a thread rule as it is.

  **Mechanism** (`Full/ThreadStep.lean`, one kernel for every primitive). A primitive reads the
  record of accesses (`Mem.footprint`) only in its race check. `ThreadLocal P c`: from every
  memory `m` where the thread owns `P`, the run of `c` is its run from `m.noFp` (a sequential
  memory) up to the record of accesses (the results agree after `Mem.noFp`), and a result of
  the run from `m` is an `FStepIn` of the frame's bytes in which a byte of an old block that
  comes alive has only accesses before the thread's clock (`Mem.RevivesOwned`; a step that
  revives nothing, `Mem.NoRevive`, has it). "Up to the record" (S1, step 4) rather than "with
  `m`'s record in front" lets a revival forget part of the old record (`Mem.forgetFrom`); a step
  whose run is the run from `m.noFp` with the record in front (`RunFp`) and that revives nothing
  is local by `ThreadLocal.intro`. The
  kernel `FTTotalTriple.ofSeq : FTotalTriple P c Q → ThreadLocal P c → FTTotalTriple P c Q`
  (and `FTTriple.ofSeq`, partial) reads the sequential triple in `m.noFp`: the resources, the
  postcondition and the invariant come from it, race freedom from locality, and ownership of the
  post's bytes from both (a byte of the post is a byte of the pre, in a new block, or revived
  without history: `owns_step`). Locality is
  proved once per memory operation from ownership (`ThreadLocal.loadBytes`, `load`, `storeBytes`,
  `store` from `OwnsPtr P p n`; `alloc` for every `P`; `free` of a wholly owned block, whose
  end then races with no access) and frames (`ThreadLocal.frame`). A step that leaves the memory
  as it is has its thread rule directly (`FTTotalTriple.of_read`). Each primitive then has one
  proof: its thread rule is `FTTotalTriple.ofSeq` of the sequential rule and its locality (or
  the sequential rule is `.toFTotalTriple` of a thread rule proved directly).

  Locality composes: `ThreadLocal.bind` (a local step whose successful sequential runs end in
  `Q`, then a step local for `Q`), `pure`, `throw`, `ite`, `readBind` (a read of the blocks, as
  `Mem.access`); from these `@memset`, `@memmove` and `@memcpy` are local from the ownership of
  their bytes. Ownership providers: `OwnsPtr.bytesAt_add`, `arr_elem`, `pts_add`, and for
  `fsym` (`Full/AutoThread.lean`) `OwnsPtr.bytesAt_in`, `regionIn_in`, `region_in`, `pts_in`,
  `arr_in`, `errPayload`.

  **`fsym` makes the thread rules of owned accesses** (`Full/AutoThread.lean`,
  `docs/proof-automation.md` §Threads): in a thread goal it applies a sequential `@[fsym]` rule
  through `FTTotalTriple.ofSeq` (`FTTriple.ofSeq` for a partial rule), with the `ThreadLocal`
  side goal proved by the locality providers (`ThreadLocal.load`, `store`, `loadBytes`,
  `storeBytes`, `memset_of`, `memmove`, `memcpy`, `alloc`, `pure`, `throw`, `liftR`; ownership
  by `OwnsPtr`). So the owned accesses of `Full/Ops`, `Full/Region`, `Full/Typed` and `Full/Arr`
  have no hand-written thread copy (their statements are the regressions of
  `tests/roadmap/sep-auto/Threads.lean`). A command that no provider shows local gets no thread
  rule from its sequential one (fail closed): the atomic ops (step 5 below) and the `const`
  reads (below) have their own native thread rules.

  Done: `Full/Block` (`FTTriple.alloc`, `allocZero`, `FTTotalTriple.free`: hand-written, their
  callers are term proofs), `Full/Ops` (`ptrAddr_of`, `checkAlign_of`, `ptrEqAddr_of`,
  `ptrProject_of`, `ptrProject_elem_of`; `load_bytesAt` and `storeBytes_bytesAt` stay for the
  rules framed with `bext` in `Full/Local`: `FTTriple.storeAt`, `loadAt`, `ptrProjectAt`).
  `Full/Region` (`ptrLe_of`, `ptrLt_of`, `checkIndex_of`, `checkSentinelIndex_of`): the pointer
  order and bounds checks read no byte, so their thread rules are the proofs and the sequential
  rules are read from them; these native rules are `@[fsym]` in thread goals. `Full/Mmap`
  (`mmap'`, `mmapC`, `munmapTail'`, `munmapPrefix'`, `munmapWhole'`, `munmapTailR`,
  `mremapShrink'`, `mremapShrinkR`; no hand-written copies, the regressions are in
  `tests/roadmap/sep-auto/Threads.lean`): the locality providers `ThreadLocal.mmap` (every
  precondition: no record read, a new block), `ThreadLocal.munmap_of` and `mremapShrink_of`/`_at`
  (the removed bytes are the precondition's, `OwnsPtr`; the block's size and kind from its
  extent, `BlockIs`; over `ThreadLocal.munmap`/`mremapShrink`; `Mem.NoRevive.setBlock`: a block
  keeps or loses live bytes, never gains one).
  An empty cut records a zero-length write at the mapping's end. A zero-length access touches no
  byte and races with nothing (`raceAt`, `Mem.freeRaces`; model fix, coordinator ruling;
  `noRace_zero`, regression `tests/roadmap/sep-full/ZeroLenCX.lean`). Before the fix it raced
  with a stale entry of a concurrent thread across the end, which the extent alone does not
  order, so the shrink's thread rules needed a nonempty cut; now their statements equal the
  sequential ones. One mechanism: the model's other byte tests (`plainHit`, `ALoc.over`,
  `NaEntry.conflicts`) and the logic's ownership (`FootprintEntry.Touches`, `Covers`, the word
  and lock `Hits`) also count a zero-length access as touching nothing. So an owned access
  needs no positive length (`Mem.Owns.noRace`, `StepIn.recordAt`, `ThreadLocal.load`/`store`
  lost that premise), and a zero-length access of the current thread is a `StepIn` for every
  frame.

  **Done: `Const` (`cload`, `cfield_*`), by a model change (MM-20).** Two obstructions stood in
  the way. (1) A read of a `const` global owns no bytes, so its race check passes only if no
  recorded write to the global is concurrent with the reader; every recorded write went through
  `Mem.accessW` (or a mapping's kind check), but `Mem.FConc` does not say so. (2) `cpts` is
  knowledge, and the bytes it describes may belong to the frame (`cbytesAt_intro` hands out the
  knowledge and keeps the bytes); a load recorded a `.read` entry on them, and `FStepIn.fp`
  allows a new entry only if it touches no byte of the frame. So the thread `cload` failed even
  in a memory with no recorded write at all (kernel-checked, `cload_no_thread_rule` on
  `codex/csl-s1-const` 08f34cd8e). Coordinator ruling (2026-10-13): option A, the model. **A read
  of a `const` global records nothing** (`recordAccessIn`, used by `loadBytes`,
  `loadDiscardBytes` and `External.claim`): no step ever records a write to one (a write access
  to one throws `.illegal` before recording, now also an external model's write claim and a
  `loadBytes` with a write kind), so the read races with nothing, and nothing else reads its
  record (the consumer audit is MM-20 in `docs/architecture-audit/memory-model.md`). A `const`
  load then leaves the memory unchanged (`Zig.load_const`, `Full.load_const_step`), the thread
  rule is a read step (`FTTotalTriple.of_read`): `FTTotalTriple.load_const`, `cload`,
  `cfield_loadAt`, `cfield_load`, and the sequential rules are their `toFTotalTriple`. No
  `FConc` invariant is needed; the `ConstRO` plan is dropped. Regression
  `tests/roadmap/sep-full/ConstReadCX.lean`: the old counterexample's memory, resource and frame
  now satisfy the thread rule. Atomic reads of a `const` global still record an `.atomicRead`
  entry (it races with nothing either; no rule reads such an entry, and the atomic thread rules
  take non-`const` words).

  **`mremap` growth in place (`mremapGrow'`, and the in-place case of `mremapMove'`,
  `mremapMoveC`).** The grown bytes `[S, lo + n)` of the old block come alive without a
  recorded access, so the thread owns them only if every recorded access to those offsets
  happened before its clock. The precondition holds the extent (`bext`) and at most the old
  bytes; the extent is ghost state, not linked to clocks: with the old model a footprint entry of
  thread 1 at offset `S` (its `munmap` of the old tail, concurrent with thread 0) made the post's
  ownership false. Fixed in the model (coordinator decision), not in the logic: a revival
  forgets the recorded accesses to the revived offsets (`Mem.forgetFrom`, in `Mem.mremapGrown`
  and `Mem.afterByteRemap`; an entry that starts past the old end gets the empty clock, one that
  crosses it ends there), so they start with no access history, as the bytes of a new block do
  (natively the growth maps new pages). Every clock then owns the grown bytes
  (`Mem.OwnsC.forgotten`); regression `tests/roadmap/sep-full/RemapHistoryCX.lean` (the
  counterexample's write races with the old record and does not after the fix). The thread
  rules (done, S1 step 4): the step edits old entries, which `StepIn` does not allow and
  `FStepIn` does (a narrowing, `FStepIn.forgetFrom`); `ThreadLocal`'s second clause allows the
  revival of history-free bytes (`Mem.RevivesOwned.of_forgetFrom`). Providers:
  `ThreadLocal.mremapGrow` (no `MAYMOVE`, from the authority `bauth` alone: the run reads no
  record, `Os.mremapLive_grow0`), `ThreadLocal.mremapMove` (either flag, from the ownership of
  the live bytes `[lo, S)`: the move's write of them races with nothing,
  `Os.mremapLive_grow_of`; the move ends the block and pushes one, `FStepIn.kill`,
  `FStepIn.push`) with its provider form `mremapMove_of` (`OwnsPtr` of the live bytes, `BlockIs`
  from the extent), and `ThreadLocal.remapByteBuffer` (`Full/Block`: a byte remap that does not
  move, of a heap block that `P` owns whole). `fsym` makes the thread rules (`ofSeq` of the
  sequential rule and the provider; regressions `mremapGrow'`, `mremapMove'`, `mremapMoveC` in
  `tests/roadmap/sep-auto/Threads.lean`; no thread rule is stated). The atomic locations over ended bytes are retired (done, coordinator
  ruling (b), model change): `Os.munmap`, `Mem.mremapShrunk` and a shrinking
  `Mem.afterByteRemap` drop the locations that overlap the removed bytes, with their messages
  and the threads' views (`Mem.retire`, factored out of the mixed-size `retireAt`). Before,
  an atomic read of a revived byte could read a message from before the unmap: regression
  `tests/roadmap/sep-full/RetireCX.lean` (a relaxed load of a regrown zero byte read `5`; now
  it has one option and reads `0`). The sequential rules carry every resource across
  (`Holds.retire`: a byte keeps its location or has none, and a tag constraint allows none);
  the thread rules see a retirement as an `FStepIn` whenever the removed bytes are not the
  frame's (`FStepIn.retire`). `Os.munmap` and `Os.mremap` are no longer `Tame` (the layout
  shrinks); `Tame.munmap_mono`/`mremap_mono` keep their address and liveness facts.
* **S3 — `fsym` backend** (fsym-engine lane, ledger #8): the record `TLogic` (`FLogic` without
  `ofTotal`); `@[fsym]` rules with `FTTriple`/`FTTotalTriple` conclusions; in a thread goal only
  thread rules apply (an `FTotalTriple` rule there would be unsound).
* **S4 — the switch** (csl lane): `CTriple` redefined as above with its rules (`bind`, `liftMem`
  from an `FTTriple`, `pick_bind`, `loop`, `admissible*`, `upd`/`eupd`, `facts` over `FConc`),
  the concurrent backend on thread rules, `WP.call_fowned`; re-check `alloc-translated`,
  `alloc-arena`, `sep-auto`.

  **Message coverage and the oracle's choice (done; coordinator rulings after agents #15–#17).**
  The atomic thread rules are proved for choice `0`, but a resumed pick has every choice
  `c < count m₂`, and ownership of a word does not make it offer one message: ownership speaks of
  the recorded accesses, nothing tied the messages to them. Kernel-checked:
  `tests/roadmap/sep-full/MsgFloorCX.lean` (an owned `apts p 1` whose location has an older
  message `0` from another thread: `count_two`, `reads_old`; the memory is even `FSeq`, `fseq`).
  The fix is one memory invariant, **`Mem.MsgCov`** (`ZigLean/Conc/Clock.lean`): every clock that
  covers the recorded accesses to a location's bytes covers each of its messages' clocks and
  release clocks, and every location lies in its block. Every step keeps it (`FStepIn.cov`, per
  constructor; relative to any record in front, for the `ThreadLocal` kernel): a step only adds
  accesses, narrows ones past a block's end (no location there), retires locations, and makes
  messages whose clocks are those of its own recorded access (a store, an RMW, a `cmpxchg`), of
  the plain writes to the bytes (`locIdx`, `retireAt`: `plainClock`), or joined with the release
  clock of a message it read (an acquiring RMW). A lock word's steps keep it too
  (`LockWord.Step.cov`; an RMW's message is covered by the op's recorded access, `LockWord.Rec`).
  It is not an invariant of `Mem.FSeq` (`MsgFloorCX.fseq`, so `toFTriple` is unchanged and no
  sequential rule is weakened); the concurrent logics carry it: `FOwned.conc`, and the
  resumption of `CTriple.Run` at a stop, `soloResp op = some ρ ∨ m₂.MsgCov` (the in-thread
  reading answers itself; `WP.call_fowned` resumes with `FOwned`'s coverage). With it an owner's
  floor is the newest message (`newest_before`, `floor_newest`), so an atomic op at an owned word
  has one option (`loadCount_le`, `rmwCount_le`, `storeCount_le`, `casCount_le`,
  `casPtrCount_le`, `unorderedCount_le`) and its pick is the choice `0` (`CTriple.pick_one`; the
  rules `CTriple.pick_load`, …, which `fsym` tries before `C.pick`, the rule for every choice). A
  weak `cmpxchg` keeps two options, a success and a spurious failure (`weakCasCount_le`,
  `weakCasPtrCount_le`, `CTriple.pick_le`: the choice is `0` or `1`). `MsgFloorCX.not_msgCov`:
  the counterexample's memory violates the invariant, and `load_ctriple` is the load's `CTriple`
  at an owned word. The seen-floor follow-up (read-read coherence) builds on this invariant.

  **`CTriple P · Q` is not admissible** (so there is no fixpoint-induction rule for recursive
  call groups yet; follow-up row `CTriple.fix` by depth/fuel). At a stop `CTriple.Run` asks for
  *one* part `r'` (an existential) from which every resumption runs. The elements of a chain may
  need different parts there, and their least upper bound one that none of them has. Sketch with
  credits (`Full/Ghost.lean`): a precondition and invariant in which each later stop needs one
  credit more, so the approximation `x_k` (cut after `k` stops) is proved from a part with `k`
  credits at its first stop, while the limit would need a part with more than every `k`. (A
  sketch, not a kernel-checked counterexample.) `CTriple.loop` is therefore
  proved by induction on the depth and fixpoint induction on the root of the tree
  (`Sched.admissible_root`), not by admissibility of `CTriple`.

### Relation to `Proto.WP` (one concurrent logic)

The logic for several threads is `Proto.WP` (all schedules) with `FOwned` (below) as its heap
layer; a thread's `MemM` steps enter it through `WP.liftMem_fowned` with an `FTTriple`, and after
S4 a concurrent function's calls through `WP.call_fowned` with a `CTriple`. So there is one
concurrent logic (`Proto.WP`), one heap logic (`Res`, `Holds`, `⋆`), and one thread judgment pair
(`FTTriple`/`FTTotalTriple`, with `CTriple` its stop-wise form for `ConcM`).

## The threads' parts: `FOwned`

```
FOwned own rO m := ∃ rT, sepN m.threads.size (fun u r => r = own u) rT ∧ Holds m rT rO ∧
  (∀ u < m.threads.size, m.Owns u (own u).heap.erase) ∧
  (∀ u, m.threads.size ≤ u → own u = Res.empty) ∧ m.clocks.size = m.threads.size
```

* `own u : Res` is thread `u`'s part; the parts compose (`sepN`, so their bytes are disjoint and
  their ghost states are valid together) and hold in `m` next to **the protocol's rest `rO`**.
* `rO` is explicit (the legacy `Owned` leaves the rest implicit as "the other bytes"): resources
  that no thread holds are a `Res` too, with knowledge and ghost state. A free lock's resource,
  a shared atomic word (as `apts` with its tag), a ledger authority that the protocol keeps: all
  are parts of `rO`, which the protocol's invariant describes (`∃ rL, R rL ∧ …`).
* **Rules** (each the analogue of an `Owned` rule):
  * `FOwned.start`: no parts, `rO` = the whole memory, in a memory without recorded accesses
    (`initRes`, D1(b), gives its knowledge and extents for the globals);
  * `FOwned.step` and `WP.liftMem_fowned`: a `MemM` step of thread `t` with an `FTTriple` on
    `own t`, with the other parts and `rO` as its frame;
  * `FOwned.keep`: a step that changes no part's bytes, retires or adds atomic locations only over
    bytes of `rO`, keeps every block's address (`KMono`) and the extents (`KeepsExt`), adds no
    footprint entry on a part, and makes no clock smaller (an atomic op on a word of `rO`, a futex
    op, a stop, `setThread`);
  * `FOwned.fork` / `join`: spawn moves a sub-resource of the parent's part to the child; join
    moves the child's part to the parent (clocks as in `Owned.fork`/`join`);
  * `FOwned.take` / `give` (legacy `add`/`shrink`): a part takes a sub-resource of `rO` whose bytes
    its clock owns, or gives one back to `rO` (a lock's acquire and release, a handoff).

### Locks, transfer, spawn/join/detach, TLS

* **Locks** (done as T5's library: `Full/LockWord.lean`, `Full/ThreadRest.lean`, `Full/Lock.lean`,
  `Full/LockRules.lean`, `Full/Mutex.lean`). The word's reasoning has no heap assertion
  (`LockWord.WInv P m` over the threads' places `P`; a lock step `LockWord.Step`; the clock transfer
  of an acquire `Acq` and a release `Rel`). `FLock γ` adds `R : (ThreadId → γ) → FAssn` and the
  parts: `FLock.Inv G rX m` is the word's invariant and `FOwned` whose rest is the word's cells
  (`cellsAt`, no tag constraint; `LocOk` stays a memory fact), the free lock's resource `rL` (with
  `R` and `LockWord.Owns`) and the protocol's own rest `rX`. A lock step is a `RestStep` at the
  word's bytes (`FOwned.restStep`); `lock` is `FOwned.take`, `unlock` is `FOwned.give`. A
  protocol fits the lock if its invariant is `∃ rX, Inv G rX m ∧ U G rX m` with `U` stable under
  lock steps. The client contract is `MutexImpl` (`lock_wp`, `unlock_wp`); an implementation
  (std `Io.Mutex`, `Thread.Mutex`) proves it from the rules, a client uses only the contract.
* **Transfer** (`Transfer.lean`, C01 captures): `Capture.grant` over `Res`; `fork_grant` and
  `join_regain` are `FOwned.fork`/`join`. Done in `Full/ThreadSpawn.lean` (`FTransfer`,
  `FCapture.grant`, `FCapture.fork_grant`/`join_regain`; `tests/roadmap/spawn-failure` migrated).
* **Spawn failure** (`SpawnLemmas.lean`): the frame of a failed spawn keeps `FOwned` unchanged.
  Done in `Full/ThreadSpawn.lean` (`WP.spawnFailureRetains_fowned`). A struct store whose encoding
  is not `LawfulEnc` (an `Io.Group`) is `FTTriple.storeAt'` (`Full/Local.lean`).
* **Detach** (`Detach.lean`): `FOwned.setThread` (a `keep`), and `not_bytesAt_granted` for
  `up (bytesAt …)` in a part.
* **TLS** (`TlsLemmas.lean`): a thread-local block is a part of its thread; its knowledge may be
  shared. Done in `Full/ThreadTls.lean` (`tests/roadmap/thread-locals` migrated): an instance is a
  `.global` block with its full extent in its thread's part (`tlsOwn`, `tlsDying`); the thread
  start and end are `FTTriple`s on the part (`FTTriple.tlsAllocs`, `freeBlocks`) with the record
  update kept by `FOwned.setTls` (`WP.liftMem_tlsEnter_fowned`, `WP.liftMem_tlsExit_fowned`).
  `tlsPtr` reads only the thread records, which are protocol facts, not resources: it is resolved
  against the current memory inside a `MemM` step (`WP.liftMem_tlsPtr_bind`), so no thread triple
  needs the records (the legacy `TTripleIn` has no counterpart). `main`'s instances are start
  globals in its part (`FOwned.one`, `initRes_holds`).
* **Witnesses / Unroll** (`Witness.lean`, `Unroll.lean`): no heap assertions of their own; they
  follow the parts' type.

## Termination and turn cost: `Proto.cost`, not a second judgment

Coordinator decisions (2026-10-12; #178 closed; option (A) approved): termination of concurrent
code is the **one weakest precondition `Proto.WP`** with an opt-in turn cost. There is no
`Stops`/`Turns`/`WPT` judgment and no `stops`/`halts` tactic (`ZigLean/Conc/Logic.lean`,
`ZigLean/Conc/Returns.lean`).

* **Why a field and not an invariant.** `Safe`'s stop lets the thread pick any new ghost value
  that keeps the invariant, and a yield or a pick changes no memory, so no invariant can force a
  turn to cost anything. The charge must be part of the stop itself.
* **`Proto.cost : Option (γ → Nat)`** (default `none`) reads the credits `cr g` of a ghost
  value. With `some cr`, each stop pays for its turn (`Proto.Charged`, `Proto.ChargeOk`): the
  thread resumed with `old` credits, stops with `new`, `1 ≤ new` (it keeps one for the turn that
  resumes it, which may end the thread) and `new + 1 ≤ old`; at a **spawn** it also reserves the
  new thread's credits, `new + k + 1 ≤ old`, where every start value of the target (`init`) has
  between `1` and `k` credits. A **futex wait, a gate and a deferred spawn have no charge**
  (`ChargeOk = False`): their turns depend on another thread's progress, so a cost proof fails
  closed there (`wait_fails_closed`); fairness-dependent clients stay unproved (C13, SCH-01).
* **No result.** `Safe`'s `leaf none` case is `Partial ∨ depth = 0` (`Partial := strict = false
  ∨ cost = none`): a strict protocol with a cost needs every `MemM` step to return. The FOwned
  step rules take `hret : Partial ∨ FTTReturns Pa x` (the second half of an `FTTotalTriple`).
* **`cost = none` is exactly the partial-correctness `Safe`** (`Safe.sync_none`; no existing
  statement changes). The generic rules (`WP.sync`, `pickC`, `spawnC`, `joinC`, futex, group,
  lock rules, …) take `(hcost : P.cost = none := by first | rfl | assumption)`, which a concrete
  protocol discharges by `rfl`; `WP.syncC` is the charged form. The reusable Sync contracts
  quantify over protocols with `P.cost = none`, which is what they meant before the field.
* **The theorem** (`Proto.returnsWithin`): a strict protocol proof with `cost = some cr` where
  `main` starts with `B = cr (G0 0) ≥ 1` credits returns under **every oracle** within `B` turns,
  with `main`'s value (or a stack overflow, STK-01). The potential is the sum of the waiting
  threads' budgets (credits, plus a spawn's reservation; `PB`, `BInv`); every turn makes it
  smaller by at least one, and a waiting thread has as much depth as credits, so the run never
  runs out of depth. `stop_needs_credits`: a thread with at most one credit has no proof of any
  stop (kernel-checked).
* **Credits as a resource.** `cr` is any function of the ghost value; a protocol over `FOwned`
  reads it from the thread's part (`credits n`, `Full/Ghost.lean`), which no update mints.
* **Re-expressed #178 theorems** (next): `Proofs/Threads/Termination` (`disjoint`) and
  `Proofs/Atomics/Termination` (`publishRead`). They need the thread-total primitive rules
  (`FTTotalTriple` of `alloc`/`store`/`load`/`free`, stage S2 of T-ctriple) for `hret`. Bound for
  `disjoint`: `main` starts with 7 credits (5 at its first spawn after reserving 1 for kid 1, …);
  the worst schedule takes 6 turns.

## No bridge from legacy thread triples

`Full/Thread.lean` does not import the legacy layer: clock ownership and `FStepIn` live in
`ZigLean/Conc/Clock.lean`. The transitional bridge from legacy thread triples
(`FTTriple.ofTTriple`, `Full/ThreadBridge.lean`) is gone: the primitive thread rules on a block
held with its extent (`FTTriple.storeBytesAt`, `storeAt`, `storeAt'`, `loadAt`, `ptrProjectAt`,
`Full/Local.lean`) are the native thread byte rules of `Full/Ops` with `bext` framed, and
`FTTriple.alloc`, `free'`, `free_front` are the native rules of `Full/Block`. No full-state thread
module imports `ZigLean/Conc/Own.lean`.

## Strength (D1 for thread triples)

* **Client statements.** The clients' final theorems are about `Sched.run` (`*_safe`,
  `*_result`, …) and do not mention a triple. A migration keeps them verbatim; the strength
  check is `example : <old statement> := <new theorem>` in the strength log for every migrated
  theorem (the run-level statement is the claim; intermediate `WP` lemmas are proof structure).
* **Library.** `FTTriple.toFTriple` (every thread rule is a sequential rule). Thread rules with
  `up` pre/postconditions are at least as strong as their legacy versions on size-free
  assertions; rules that use full-state resources (`apts`, `known`, `bext`) have no legacy
  counterpart.
* **Preconditions.** A migrated client's protocol needs no new premise: its initial memory is
  `{}` (no blocks: `FOwned.start` with `rO` empty) or `initRes` (D1(b)); ghost resources appear
  only where their creator provides them.

### Strength log

Each migrated client ends with its legacy statements as `example`s checked against the new
theorems (`## Strength` at the end of the file).

| client | theorems | statement | precondition delta |
|---|---|---|---|
| `Proofs/Detach/Worker` | `worker_safe`, `worker_result` | verbatim | none (start memory `{}`, `FOwned.start`) |
| `Proofs/Threads/Disjoint` | `disjoint_spec`, `disjoint_safe` | verbatim | none (start memory `mem0 σ`, `Mem.init_fseq`); witnesses of `writeFlag_spec` and of the library's `FTTriple.free_front` (`FTTAdmit.of_exts`) |
| `Proofs/Cancel/Group` | `cancelClient_spec`, `cancelClient_canceled_not_completed` | verbatim | none (start memory `{}`, `FOwned.start`; the legacy `Covered` is `FOwned.cover` with the empty rest) |

## Phases

| | content | state |
|---|---|---|
| T1 | `FTTriple`, structural rules, `toFTriple` (`Full/Thread.lean`); the bridge `ofTTriple` (removed) | done |
| T2 | `FOwned` + `WP.liftMem_fowned` (`Full/ThreadOwned.lean`); thread `alloc`/`free'`/`storeAt`; `Proofs/Detach/Worker` | done |
| T3 | `Proofs/Threads` (`Disjoint` done: `FOwned.join`, `disj`, `WP.callMC_fowned`), `Proofs/Cancel/Group` (done: `FOwned.keep`, `recordAt`, `cover`, `WP.callMC_fownedS`), `Proofs/Detach/Transfer` | next |
| T4 | `Transfer`, `SpawnLemmas` (done: `Full/ThreadSpawn`), `Detach`, `TlsLemmas` (done: `Full/ThreadTls`) restated; `spawn-failure` (done), `thread-locals` (done), `thread-tuples`, `detached-threads` | next |
| T5 | `Lock`, `LockRules` over `FOwned`; `Proofs/Iogroup/Counter` (a lock that owns the counter), `Proofs/Sync`, `Proofs/Threadsync`, `rwlock-contracts`, `sync-contracts`, `shared-reclamation`, `pointer-atomics` | library done (`Full/LockWord`, `ThreadRest`, `Lock`, `LockRules`, `Mutex`, `Word`, `WordRules`); one judgment for every sync primitive: `FLock.Fits L K P U ok` (the protocol with the lock `L` keeps the primitive `K : FPrim`, a data record: place, roles, what the rest keeps, its steps; the lock alone is `FPrim.empty`, a primitive over futex words is `FPrim.ofWords`, with its generic lemmas `Fits.back`, `Fits.atOp`, `Fits.wStep`, `Fits.wOwn`); `Io.Mutex` proved once over its code (`Full/IoMutex`, `IoMutexCode`; instances `Proofs/Iogroup/Lock`, `Proofs/Sync/IoMutex`); `Thread.Mutex` of 0.15.2 (Linux x86/aarch64, macOS) in `Proofs/Threadsync/ThreadMutex`; `Proofs/Iogroup/Counter` done (over `MutexImpl`); the futex event `Full/Event` (`FEvent`, `EventImpl`; scope: one waiter at a time, after every earlier `waiting` write, because a read's model facts give its happens-before floor but not the read-read coherence of `Mem.seen`; several waiters are a follow-up; roles: the client names who may wait (`FEvent.wx`) and who may set (`FEvent.sx`, the setter role that `set_wp` requires and that a setter keeps after its `set`), and a step of one sync object moves a thread's place in the other's code only between `out` and `away`, `away` only for a waiter (the steps of `FCond.prim`, `FEvent.prim`); a condition step is indexed by the word it splits off the rest (`FCond.MStep W`)), `Io.Event` in `Proofs/Sync/Event` (0.16.0 and 0.17.0 translations); `Thread.ResetEvent` of 0.15.2 in `Proofs/Threadsync/Event` (its `Deadline` stack block is in the waiter's part: `FLock.setPart`, `FEvent.wp_liftPart`); the futex-epoch condition `Full/Cond` (`FCond`, `CondImpl`; scope: one waiter at a time that enters after every epoch write, and signallers whose stops come after the registration, for the same reason as the event; several waiters are a follow-up), `Io.Condition` in `Proofs/Sync/Cond` (0.16.0 `waitInner` and the 0.17.0 inlined loops), `Thread.Condition` of 0.15.2 in `Proofs/Threadsync/Cond` (its `Deadline` block is allocated while the waiter holds the mutex: `FLock.Inv.wp_liftPart` frames the held resource, `FCond.wp_liftPart`); `handoff` done once over `MutexImpl`, `CondImpl` and `EventImpl` for every `Box` layout (`Proofs/Handoff/`: protocol, steps, operations; `io` read for a layout with an `io` prefix whose alignment divides the `Box`'s), walked per version in `Proofs/Sync/Handoff` (0.16.0, 0.17.0) and `Proofs/Threadsync/Handoff` (0.15.2) |
| T6 = T-ctriple S1–S4 | generalized race relation, atomic thread rules (S1); primitives as `FTTotalTriple` (S2); `TLogic` `fsym` backend (S3, engine lane); stop-wise `CTriple`, `WP.call_fowned` (S4) | next (after T3, T-term) |
| T-term | credits in `Res` (merged, #193), `WPT`, `returnsWithin` from credits; #178's theorems | next |
| T7 | delete `Conc/Own`, `Csl` and the legacy halves (with A7) | after A6 |
