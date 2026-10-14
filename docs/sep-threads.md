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
      StepIn rF.heap.erase m m' ∧ FPres m m'
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
* **Race freedom** is the `StepIn` conjunct, as in `TTriple`: no new footprint entry touches a
  frame byte, no other thread's clock changes, the thread's own clock only grows.

### One logic: the sequential triple is a special case

`FTTriple.toFTriple : FTTriple P c Q → FTriple P c Q`. A sequential memory (`FSeq`) is a
concurrent one in which the current thread owns everything (`SingleThread`: every entry is its
own and happened before its clock), and `StepIn` plus `FPres` give `FSeq` after the step. So a
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
  rule exists yet, `FTTriple.ofTTriple` lifts the legacy `TTriple` rules (next section);
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
owns `r'` (`Holds m₁ r' rF₁`, `FConc`, `Owns`) and every `c < max 1 (count m₁)`, the rest
`k c m₁` is again such a run. A stop of another kind (yield, futex, spawn, join, …) has no case
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
* **S2 — primitives as thread-total rules** (csl lane, new files or additive edits to
  `Ops`/`Block`/`Arr`/`Mmap`; existing statements kept): `load`/`store`/`ptrProject`/arrays/
  slices/`cload`/`ptrAddr`/`alloc`/`free`/`mmap`/`munmap`/`mremap` as `FTTotalTriple`, the
  `FTotalTriple` rules derived by `toFTotalTriple`. A `StateT.lift` step of a `Result` touches
  no memory and is a thread rule as it is.

  **Mechanism** (`Full/ThreadStep.lean`, one kernel for every primitive). A primitive reads the
  record of accesses (`Mem.footprint`) only in its race check. `ThreadLocal P c`: from every
  memory `m` where the thread owns `P`, the run of `c` is its run from `m.noFp` (a sequential
  memory) with `m`'s record in front (`Mem.withFp`), and a result of the run from `m.noFp` is a
  `StepIn` of the frame's bytes that makes no byte of an old block alive (`Mem.NoRevive`). The
  kernel `FTTotalTriple.ofSeq : FTotalTriple P c Q → ThreadLocal P c → FTTotalTriple P c Q`
  (and `FTTriple.ofSeq`, partial) reads the sequential triple in `m.noFp`: the resources, the
  postcondition and the invariant come from it, race freedom from locality, and ownership of the
  post's bytes from both (a byte of the post is a byte of the pre or in a new block). Locality is
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
  rule from its sequential one (fail closed): the atomic ops keep their own thread rules (step 5
  below) and the `const` reads have none (Open, below).

  Done: `Full/Block` (`FTTriple.alloc`, `allocZero`, `FTTotalTriple.free`: hand-written, their
  callers are term proofs), `Full/Ops` (`ptrAddr_of`, `checkAlign_of`, `ptrEqAddr_of`,
  `ptrProject_of`, `ptrProject_elem_of`; `load_bytesAt` and `storeBytes_bytesAt` stay for the
  callers of `Full/Local`); the bridge's `alloc'`/`free'` are the native rules. `Full/Region`
  (`ptrLe_of`, `ptrLt_of`, `checkIndex_of`, `checkSentinelIndex_of`): the pointer order and
  bounds checks read no byte, so their thread rules are the proofs and the sequential rules are
  read from them; these native rules are `@[fsym]` in thread goals. Next: `Mmap` (`mmap`, `munmap` tail/prefix/whole,
  `mremap` shrink; their locality must show `NoRevive`, i.e. that a remapping makes no byte of
  an old block alive).

  **Open: `Const` (`cload`, `cfield_*`).** A read of a `const` global owns no bytes, so its race
  check passes only if no recorded write to the global is concurrent with the reader. Every
  write that is recorded went through `Mem.accessW` (or a mapping's kind check), which rejects a
  `const` global, so no reachable memory has one; but `Mem.FConc` does not say so, and a thread
  rule must hold in every `FConc` memory. Counterexample to `FTTotalTriple.cload` as stated: a
  memory whose footprint has a write by thread 1 to a live `const` block, concurrent with thread
  0, where thread 0 holds `cpts` of it (knowledge only: `Mem.kn` reads the blocks); the load
  throws `.illegal`. A thread rule needs a memory invariant "no recorded write to a `const`
  block" in `FConc` (with `FSeq → FConc` kept for `toFTriple`) or in `Mem.kn`'s `.cbyte` facts.
  Decided (coordinator): the invariant goes into `FConc`, proved preserved by every step.

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
  rules come with S1: the step edits old entries, which `StepIn` (every entry of the result is
  an old one or a new one of the thread) does not allow, so they need S1's step relation (an
  entry may also be a narrowing of an old one) and a `ThreadLocal` clause for the revival of
  history-free bytes. Open: the atomic locations (`Mem.atomics`, their messages) over offsets
  that a shrink or unmap ends are kept, so an atomic read of a revived byte can still read a
  message from before the unmap; retiring them is part of S1's atomic step relation.
* **S3 — `fsym` backend** (fsym-engine lane, ledger #8): the record `TLogic` (`FLogic` without
  `ofTotal`); `@[fsym]` rules with `FTTriple`/`FTTotalTriple` conclusions; in a thread goal only
  thread rules apply (an `FTotalTriple` rule there would be unsound).
* **S4 — the switch** (csl lane): `CTriple` redefined as above with its rules (`bind`, `liftMem`
  from an `FTTriple`, `pick_bind`, `loop`, `admissible*`, `upd`/`eupd`, `facts` over `FConc`),
  the concurrent backend on thread rules, `WP.call_fowned`; re-check `alloc-translated`,
  `alloc-arena`, `sep-auto`.

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
  is not `LawfulEnc` (an `Io.Group`) is `FTTriple.storeAt'` (`Full/ThreadBridge.lean`).
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

## Transitional bridge

`Full/Thread.lean` does not import the legacy layer: clock ownership and `StepIn` live in
`ZigLean/Conc/Clock.lean`. The bridge below and the primitive thread rules lifted through it
(`storeAt`, `loadAt`, `ptrProjectAt`; `alloc'` and `free'` are the native rules of `Full/Block`)
are `Full/ThreadBridge.lean`, the one full-state module that imports `ZigLean/Conc/Own.lean`; it
goes with the native rules (T6).

`FTTriple.ofTTriple : TTriple P c Q → Tame c → SizeFree P → Keeps c → FTTriple (up P) c (up ∘ Q)`
lifts a legacy thread triple, as `FTriple.ofTriple_up` lifts a legacy triple. A client file
switches to `FOwned` and the F library in one step; its own legacy `TTriple` lemmas (and the legacy
primitive rules `TTriple.load`, `storeAt`, `alloc`, `free`, `ptrProjectAt`) lift through the bridge
until their native versions exist. The opposite direction (`TTriple.ofF`, an F thread triple used
by the legacy `Owned`) needs size-free postconditions (a legacy frame cell records its block's
size, a full-state one does not), so it would not cover `bytesAt`; the coordinator's
"`TTriple.ofF`" is therefore realised as this bridge.

## Strength (D1 for thread triples)

* **Client statements.** The clients' final theorems are about `Sched.run` (`*_safe`,
  `*_result`, …) and do not mention a triple. A migration keeps them verbatim; the strength
  check is `example : <old statement> := <new theorem>` in the strength log for every migrated
  theorem (the run-level statement is the claim; intermediate `WP` lemmas are proof structure).
* **Library.** `FTTriple.toFTriple` (every thread rule is a sequential rule) and
  `FTTriple.ofTTriple` (every size-free legacy thread rule is a thread rule) relate the two layers.
  Thread rules with `up` pre/postconditions are at least as strong as their legacy versions on
  size-free assertions; rules that use full-state resources (`apts`, `known`, `bext`) have no
  legacy counterpart.
* **Preconditions.** A migrated client's protocol needs no new premise: its initial memory is
  `{}` (no blocks: `FOwned.start` with `rO` empty) or `initRes` (D1(b)); ghost resources appear
  only where their creator provides them.

### Strength log

Each migrated client ends with its legacy statements as `example`s checked against the new
theorems (`## Strength` at the end of the file).

| client | theorems | statement | precondition delta |
|---|---|---|---|
| `Proofs/Detach/Worker` | `worker_safe`, `worker_result` | verbatim | none (start memory `{}`, `FOwned.start`) |
| `Proofs/Threads/Disjoint` | `disjoint_spec`, `disjoint_safe` | verbatim | none (start memory `mem0 σ`, `Mem.init_fseq`); witnesses of `writeFlag_spec`, `free_front` ported (`FTTAdmit.of_exts`) |
| `Proofs/Cancel/Group` | `cancelClient_spec`, `cancelClient_canceled_not_completed` | verbatim | none (start memory `{}`, `FOwned.start`; the legacy `Covered` is `FOwned.cover` with the empty rest) |

## Phases

| | content | state |
|---|---|---|
| T1 | `FTTriple`, structural rules, `toFTriple`, `ofTTriple` (`Full/Thread.lean`) | this branch |
| T2 | `FOwned` + `WP.liftMem_fowned` (`Full/ThreadOwned.lean`); thread `alloc'`/`free'`/`storeAt`; `Proofs/Detach/Worker` | done |
| T3 | `Proofs/Threads` (`Disjoint` done: `FOwned.join`, `disj`, `WP.callMC_fowned`), `Proofs/Cancel/Group` (done: `FOwned.keep`, `recordAt`, `cover`, `WP.callMC_fownedS`), `Proofs/Detach/Transfer` | next |
| T4 | `Transfer`, `SpawnLemmas` (done: `Full/ThreadSpawn`), `Detach`, `TlsLemmas` (done: `Full/ThreadTls`) restated; `spawn-failure` (done), `thread-locals` (done), `thread-tuples`, `detached-threads` | next |
| T5 | `Lock`, `LockRules` over `FOwned`; `Proofs/Iogroup/Counter` (a lock that owns the counter), `Proofs/Sync`, `Proofs/Threadsync`, `rwlock-contracts`, `sync-contracts`, `shared-reclamation`, `pointer-atomics` | library done (`Full/LockWord`, `ThreadRest`, `Lock`, `LockRules`, `Mutex`); clients next |
| T6 = T-ctriple S1–S4 | generalized race relation, atomic thread rules (S1); primitives as `FTTotalTriple` (S2); `TLogic` `fsym` backend (S3, engine lane); stop-wise `CTriple`, `WP.call_fowned` (S4) | next (after T3, T-term) |
| T-term | credits in `Res` (merged, #193), `WPT`, `returnsWithin` from credits; #178's theorems | next |
| T7 | delete `Conc/Own`, `Csl` and the legacy halves (with A7) | after A6 |
