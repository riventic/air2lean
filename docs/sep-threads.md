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

* thread rules for **primitives** are proved once each (ownership gives `NoRace`, then the
  sequential run lemma). Until the native ones exist, `FTTriple.ofTTriple` lifts the legacy
  `TTriple` rules (next section);
* **`fsym` on thread triples** needs a backend whose step rules are thread rules: an `@[fsym]`
  rule with an `FTTriple` conclusion, and the structural steps over a record `TLogic`
  (`FLogic` without `ofTotal`, with `toPartial := toFTriple`). That is an engine change in
  `Full/Auto.lean` (fsym owner; requested through the coordinator). Generated thread bodies are
  short today (the client steps are single primitives under `WP.liftM_owned`), so the backend is
  not on the critical path of the migration.

### Decision: `CTriple` is derived from `FTTriple` (one concurrent judgment pair)

The concurrent judgment pair is `FTTriple` / `FTTotalTriple`. `CTriple` does not survive as a
judgment of its own: it becomes the thread triple of a concurrent function's in-thread reading,

```
CTriple P x Q := ∀ n, FTTriple P (Sched.soloRun n x) Q          (after migration step T-ctriple)
```

and today's definition (`∀ n, FTriple P (soloRun n x) Q`) follows from it by `toFTriple`, so the
statements of its clients (`PageAlloc`'s `alloc`, the arena) are kept or strengthened. Migration
step **T-ctriple**: restate `Full/Conc.lean`'s rules (`bind`, `liftMem` from an `FTTriple`,
`pick_bind`, `loop`, `admissible*`, `step`, `readStep`, `upd`) over `FTTriple`; port the
`FTriple` atomic rules on owned words (`Atomic`, `AtomicPtr`, `AtomicRules`) to thread rules (an
atomic access by the owner of the word does not race); switch `fsym`'s concurrent backend to
`TLogic` (below); re-check the page allocator and the arena. Until T-ctriple, `CTriple` is the
sequential `FTriple` of a `MemM` program (`soloRun`), not a concurrent judgment.

### Relation to `CTriple` (one concurrent logic)

`CTriple P x Q` (`Full/Conc.lean`) is `FTriple` of the in-thread reading `Sched.soloRun` of a
concurrent function (oracle choice `0`): a *sequential* statement about a `ConcM` body called by
a sequential caller. It is not a logic for several threads, and it is reused as it is: a
sequential caller of concurrent code keeps using `CTriple` and its `fsym` backend. The logic for
several threads stays `Proto.WP` (all schedules) with `FOwned` (below) as its heap layer; a
thread's `MemM` steps enter it through `WP.liftMem_fowned` with an `FTTriple`. So there is one
concurrent logic (`Proto.WP`), one heap logic (`Res`, `Holds`, `⋆`), and `FTTriple` is the
`FTriple` of a step inside a run.

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

* **Locks** (`Lock.lean`, `LockRules.lean`): `Lock.R : (ThreadId → X) → FAssn`. While the lock is
  free, `rO` contains a resource with `R` whose bytes every thread's clock (or the release clock of
  the word's newest message) owns (`Lock.Owns`, unchanged in substance, over `r.heap.erase`); the
  mutex word is an `apts`-like part of `rO` with the constraint `(o, 4)`, which states today's
  `LocOk` ("no other location overlaps the word") as a resource: the frame rule then keeps it.
  `lock` is `FOwned.take`, `unlock` is `FOwned.give`.
* **Transfer** (`Transfer.lean`, C01 captures): `Capture.grant` over `Res`; `fork_grant` and
  `join_regain` are `FOwned.fork`/`join`.
* **Spawn failure** (`SpawnLemmas.lean`): the frame of a failed spawn keeps `FOwned` unchanged.
* **Detach** (`Detach.lean`): `FOwned.setThread` (a `keep`), and `not_bytesAt_granted` for
  `up (bytesAt …)` in a part.
* **TLS** (`TlsLemmas.lean`): a thread-local block is a part of its thread; its knowledge may be
  shared.
* **Witnesses / Unroll** (`Witness.lean`, `Unroll.lean`): no heap assertions of their own; they
  follow the parts' type.

## Termination and turn cost: credits, not a second judgment

Coordinator decision (2026-10-12, #178 on hold): termination of concurrent code is the **total
variant of the one concurrent judgment**, with turn budgets as a ghost resource (credits), proved
by `fsym` rules. There is no separate `Stops`/`Turns` judgment and no `stops`/`halts` tactic.

* **A step** (`MemM`): `FTTotalTriple P c Q := FTTriple P c Q ∧ FTTReturns P c` (this branch,
  `Full/Thread.lean`): from every memory where the thread owns `P`, `c` returns a value.
  `toFTotalTriple` makes it an `FTotalTriple`, so the sequential total rules and `fsym`'s
  `FTotalTriple` backend are the termination proofs of steps. It replaces `MemM.Halts` (which says
  only "a value or an error", unconditionally) and the `halts` tactic.
* **Credits** `£ n`: a ghost component of `Res` (`cr : Nat`, composed by addition, always valid,
  owning no byte; `£ (a + b) = £ a ⋆ £ b`; requested from the owner of `Full/Res.lean`). Like every
  other resource it lives in a thread's part or in the protocol's rest (`FOwned`), moves with
  spawn and join (`FOwned.fork`/`join`), and is framed by the frame rule.
* **The total concurrent judgment** `WPT` is `Proto.WP` whose sync nodes each consume `£ 1` from
  the current thread's part (`opCost`: a yield, pick, join, wake, choose; a spawn of a target with
  budget `k` moves `£ k` to the child's part and costs `£ 2`). A futex wait and a deferred task
  have no rule (fail closed, as `opCost = none` on #178), so fairness-dependent clients stay
  unproved (C13). The parts are read from the ghost values (`Proto.parts : (ThreadId → γ) →
  ThreadId → Res`), so a protocol needs nothing beyond its `FOwned` invariant.
* **The theorem** (`Proto.returnsWithin`, re-proved): the potential is the sum of the credits of
  all parts and of `rO`; each turn of a thread consumes one, a spawn moves `k` and consumes two, so
  every schedule returns within the initial credits `B`, for every oracle. This is #178's
  potential argument (`Returns.lean`: `bsum`, `settle_budget`, `fork_blocks`, `join_blocks`) with
  the budget read from the resources instead of a `Turns` tree; those lemmas move into the
  library as they are.
* **In-thread reading** (`CTriple`): its total variant counts the same credits at the oracle
  picks of a solo reading (`C.pick` consumes `£ 1`), so `fsym` charges a pick or an atomic op one
  credit by an `@[fsym]` rule; a loop needs a credit invariant (`£ (c * k)` for `k` iterations).
* **Re-expressed #178 theorems** (next phase): `Proofs/Threads/Termination` (`disjoint` returns
  `a + b` within 6 turns; 6 is tight) and `Proofs/Atomics/Termination` (`publishRead`) as `WPT`
  proofs: `main` starts with `£ 6`, each spawn gives the kid `£ 0` and costs 2, each join 1.

## Transitional bridge

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

## Phases

| | content | state |
|---|---|---|
| T1 | `FTTriple`, structural rules, `toFTriple`, `ofTTriple` (`Full/Thread.lean`) | this branch |
| T2 | `FOwned` + `WP.liftMem_fowned` (`Full/ThreadOwned.lean`); thread `alloc'`/`free'`/`storeAt`; `Proofs/Detach/Worker` | done |
| T3 | `Proofs/Threads`, `Proofs/Cancel`, `Proofs/Iogroup`, `Proofs/Detach/Transfer` | next |
| T4 | `Transfer`, `SpawnLemmas`, `Detach`, `TlsLemmas` restated; `spawn-failure`, `thread-locals`, `thread-tuples`, `detached-threads` | next |
| T5 | `Lock`, `LockRules` over `FOwned`; `Proofs/Sync`, `Proofs/Threadsync`, `rwlock-contracts`, `sync-contracts`, `shared-reclamation`, `pointer-atomics` | next |
| T6 | native primitive thread rules (no bridge); `TLogic` `fsym` backend (engine change) | next |
| T-term | credits in `Res` (request), `WPT`, `returnsWithin` from credits; #178's theorems | next |
| T7 | delete `Conc/Own`, `Csl` and the legacy halves (with A7) | after A6 |
