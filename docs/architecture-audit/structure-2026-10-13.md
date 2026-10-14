# Architecture audit 2026-10-13: design weaknesses at the arena landing

Date: 2026-10-13. Read-only audit; it changes no code. Trees:

| Ref | Tip | Relation to the landing |
|---|---|---|
| `origin/codex/arena-landing` (PR #279) | d73bc71a6 | what lands on main: 635 files, +293k lines |
| `codex/fsym-ofseq` | 493e13b12 | 17 ahead, 40 behind the landing |
| `codex/fsym-views` | da5df40ec | contains fsym-ofseq |
| `codex/csl-s1-const` | dc8873b67 | contains fsym-ofseq; 73 ahead |
| `codex/mig-sync-handoff4` | 5b264fe8c | 51 ahead; contains no other lane |
| `codex/lists-append` | 9cff41410 | shares the fsym-reads chain (14 commits) |
| `codex/arena-reset` | f337238b1 | shares the fsym-reads chain; contains arena fee B/C |
| `codex/enc-exactness-2` | 33e1a9541 | based on main before the landing: 606 behind |

The critic log covers process and hygiene (stacking depth, unpushed WIP, worktrees, ratchet
counts). This audit covers design only. References are `ref:path:line`; `landing` means
`origin/codex/arena-landing`.

## Summary

| # | Finding | Severity | When | Owner |
|---|---|---|---|---|
| 1 | `CTriple` reads `spawn`/`join`/`wait` as if they were solo ops, and the claim registry trusts it | SOUNDNESS (claims) | fix now | CSL (S4) + claims tooling |
| 2 | Two concurrent logics with no bridge, and the allocator contract sits in the solo one | DESIGN (rewrite risk) | fix now | CSL + interface lane |
| 3 | `Proto.WP`, the logic of every sync proof, has no `fsym` backend, and the gate does not see it | DESIGN / SCALE | fix now | engine + sync; tooling for the gate |
| 4 | The event and condition contracts allow only one waiter | CONTRACT (rewrite risk) | fix now | sync + CSL |
| 5 | Lanes change shared contract signatures in parallel: semantic conflicts at merge | MERGE (rewrite risk) | fix now | coordinator / integrator |
| 6 | `intExtOrder?` guesses the LLVM encoding for every backend it does not know | SOUNDNESS (opt-in profiles) | fix now (before enc merges) | enc-exactness |
| 7 | "External storage is not written during the run" has no premise ID, and MM-20 now relies on it | PREMISE GAP | fix now (docs) | translator / premises |
| 8 | Heartbeat growth: 40M per theorem for `ArrayList.append` | SCALE | gate now, engine later | engine |
| 9 | `fsym` grows special cases: hard-coded library heads, rule variants per resource shape, client workarounds | DEBT | later (stop adding now) | engine |
| 10 | The roots of the full-state library still import the legacy layer | STRUCTURE | later (before A7) | one-logic / fold |
| 11 | CI discovery is hard-coded, and one `lake build` line is edited by 4 of 6 lanes | STRUCTURE | later (cheap) | tooling |
| 12 | `Ghost` is a closed record: each new resource kind edits the core | STRUCTURE | later | stack lane (ACell) |
| 13 | `Byte.handle` builds the retiring std-model representation into `Byte` | DEBT | later | enc / allocator lanes |

Checked and found consistent: zero-length accesses (`raceAt`, `freeRaces`, `ALoc.hits`), atomic
retirement (`Mem.retire`, with `FStepIn.atomics` taking a re-indexing `σ`), mremap revival
(`Mem.forgetFrom` narrows the entries and `FStepIn.fp` allows narrowings), and MM-20 against every
write path (`accessW` for stores, RMW, CAS and atomic stores; `recordAccessIn` for `loadBytes` and
`External.claim`). Notes on these are under findings 1, 7 and 13.

---

## 1. `CTriple` gives non-solo ops a solo reading (SOUNDNESS of claims; fix now)

**Evidence.** `CTriple P x Q := ∀ n, FTriple P (soloRun n x) Q` (landing:ZigLean/Sep/Full/Conc.lean:139).
`soloRun` answers **every** sync op with `soloResp` (landing:ZigLean/Sep/Full/Seq.lean:28-38):
`.spawn _ => .ok 0`, `.join _ => ()`, `.wait .. => ()`, `.spawnGated _ => 0`, `.gate => ()`. But
`SyncOp.Solo` (Seq.lean:23) admits only `yield`/`choose`/`pick`. The connection to real runs
(`run_solo`) needs `ThreadFree` (Seq.lean:13-14, 152), while `CTriple` and its claim head do not.
assurance/claim-heads.json:19 registers `Zig.Full.CTriple` with claims `no-panic` and
`correct-if-returned` for its program. docs/claim-strength.md:33 lists it next to `FTriple`.

**Counterexample (kernel-checked on the landing, axioms `propext, Classical.choice, Quot.sound`):**

```lean
theorem spawn_returns_caller (t : Tgt) :
    CTriple FAssn.emp (ConcM.sync (.spawn t) : ConcM Tgt (Except ErrName ThreadId))
      (fun r => ⟪r = .ok 0⟫) := by
  intro n m r rF hh hp hs
  cases n with
  | zero => trivial
  | succ n => exact ⟨r, hh, ⟨rfl, hp⟩, hs⟩
```

Natively, `Thread.spawn` never returns the caller's id (thread 0), and the spawned thread runs.
In the same way, `spawn writer; join; load p` has a `CTriple` that says `p` is unchanged, because
the solo reading never runs the writer. `claims.py` would report that as correct-if-returned.
Today no shipped `CTriple` proof covers a spawning function (users: alloc-arena, alloc-translated,
interfaces, sep-auto, ConstKnow; none spawns). The head stays unsound as soon as one does, and
nothing fails closed.

**Fix (one mechanism).** In the solo reading, a non-solo op has no answer. `soloTree` at a stop
with `SyncOp.Solo op = false` gives `some (.error .illegal)`, so no `CTriple` holds across it (fail
closed). Admissibility is unaffected: it is still a leaf. The S4 redefinition (docs/sep-threads.md
§T-ctriple R2: "a stop of another kind ... has no case: fail closed") already plans this; do the
`soloResp` part now, separately from S4. Add `tests/roadmap/sep-full/SoloSpawnCX.lean`: the
theorem above must no longer be provable, and its negation should be provable.

## 2. Two concurrent logics with no bridge; the allocator contract sits in the solo one (fix now)

**Evidence.**
- Interface contracts: `FnSpec P Q g := ∀ a, CTriple (P a) (g a) (Q a)` (landing:ZigLean/Sep/Full/Dispatch.lean:247).
  `CAllocSpec vt ctx I := ∀ fuel, FAllocSpec FLogic.partial (vt.solo fuel) ctx I` (Dispatch.lean:499)
  is defined directly over `soloRun`. It is neither four `FnSpec`s nor a `CTriple`, despite the
  coordinator ruling of 00:21 ("interface contracts = instances of ONE generic FnSpec").
- Sync contracts: `MutexImpl`, `EventImpl` and `CondImpl` are stated over `Proto.WP`
  (mig-sync-handoff4:ZigLean/Sep/Full/Mutex.lean:37, Event.lean:1215, Cond.lean:1786).
- No rule moves a `CTriple` into `Proto.WP`: `CTriple` occurs in none of `Full/Thread*`, `Lock*`,
  `Mutex`, `Cond` or `Event` on any lane tip. `WP.call_fowned` is only planned (S4).
- CLAUDE.md calls `CTriple` "concurrent". It is the single-thread reading (finding 1).

**Failure scenario.** Every allocator client written now is a claim about a single-thread
reading: lists-append `Proofs/Lists/{Alloc,Append,Container}.lean`, the arena `Core.lean` (67
`CTriple.` steps), and `interfaces/*`. A multi-threaded program that allocates through a vtable
(`ThreadSafeAllocator`, a spawned worker calling `page_allocator`, an `Io.Group` task appending to
a list) has no proof route. When S4 redefines `CTriple` (resumption in any memory, `pick` for
every `c < count`, `liftMem` from `FTTriple`), every one of those clients must be walked again.
`CAllocSpec` would not even change, because it is not defined through `CTriple`, so after S4 it
would still be solo while its clients claim the new meaning.

**Fix.**
1. Define `CAllocSpec` as the four entries' `FnSpec`/`CTriple`s; `CAllocSpec.of_ctriples`'s shape
   becomes the definition.
2. Do S4 next on the CSL lane, before more `CTriple` clients are written. Clients walked purely by
   `fsym` then only need the backend change. Hand `CTriple.` steps (arena Core) need rework, so
   do not add more.
3. Write `WP.call_fowned`, so that a contract proved once is usable in threads.

## 3. `Proto.WP` has no `fsym` backend, and the gate does not see it (fix now)

**Evidence.** `Proto.WP` (landing:ZigLean/Conc/Logic.lean:245) is "the one concurrent logic"
(docs/sep-threads.md:206-212), and every sync proof is written in it. It has 1955 mentions in 41
files on the landing and 2354 in 50 files on mig-sync-handoff4. `fsym`'s backends are
`FTriple`/`FTotalTriple`/`CTriple`/`FTTriple`/`FTTotalTriple` (fsym-views:ZigLean/Sep/Full/AutoAttr.lean
module doc); docs/proof-automation.md plans no `WP` backend. Sync lane files and their `fsym` uses:

| File (mig-sync-handoff4) | Lines | `fsym` | `WP.` steps |
|---|---|---|---|
| ZigLean/Sep/Full/Cond.lean | 1816 | 0 | lemmas |
| ZigLean/Sep/Full/Event.lean | 1239 | 0 | lemmas |
| Proofs/Iogroup/Counter.lean | 1583 | 0 | 51 |
| Proofs/Sync/Cond.lean | 724 | 0 | 78 |
| Proofs/Threadsync/Cond.lean | 507 | 0 | 69 |
| Proofs/Threadsync/Event.lean | 418 | 0 | 70 |

To get generic instances anyway, the lane writes the std code's shape by hand.
`IoMutexCode.bodyOf`/`lockOf`/`unlockOf` (mig-sync-handoff4:ZigLean/Sep/Full/IoMutex.lean:29,39,58)
restate `Io.Mutex`'s 0.16.0 code in normal form, and each program proves its `Gen` equal to it by
`rfl`/`simp`. A change of `Io.Mutex` in 0.18 means a new normal form and new equations: this is
the "upstream changes need no proof edits" rule broken by construction.

**Gate blind spot.** scripts/proof-framework.py:42-44 recognises a judgment only by name suffix
(`Triple`, `Returns`, `Within`, `Spec`, …). `Proto.WP`, `MutexImpl`/`EventImpl`/`CondImpl`,
`FLock.Inv`, `FStepIn` and `ResetLedger` are judgments or contracts by shape, but they are not
listed in assurance/proof-framework.json, so new ones pass the ratchet unseen.

**Failure scenario.** Each further sync primitive (WaitGroup, RwLock, Semaphore, `Io.Group`), per
std version and OS (futex vs `os_unfair_lock`), costs another 1-2k lines of hand `WP` walks plus a
hand normal form. This is the one design that cannot scale to std coverage.

**Fix.**
- Engine: a `WP` mode of `fsym`. It walks the `MemM` segments between stops with the thread rules
  (`FTTriple`, as `Inv.wp_liftMem` already consumes), and at each stop applies registered
  `@[fsym]` WP rules: `WP.sync`, futex, spawn/join, and contract rules such as
  `MutexImpl.lock_wp`. The client supplies the protocol (`Proto`, `FLock.FitsOn`) and nothing else.
  The normal-form templates are then deleted.
- Tooling: proof-framework.py also flags `Prop`-valued definitions and structures whose type
  quantifies over `Mem` and `ConcM`/`MemM`, or adds the suffixes `WP`/`Impl`; then list `WP` and
  the `*Impl` contracts in the allow-list with their status.
- Until the backend design exists, do not start new `*Impl` instances.

## 4. The event and condition contracts allow only one waiter (fix now)

**Evidence.** `EventImpl.wait_wp` assumes `∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw`
(mig-sync-handoff4:ZigLean/Sep/Full/Event.lean:1222; module doc :30 "Scope (one waiter at a
time)"). `CondImpl.wait_wp` assumes `∀ u, u ≠ t → C.ph (G u) = .out` (Cond.lean:1796): every other
thread is outside the condition's code. The reason given (Event.lean:30-37) is that the full-state
frame (`Word.Keep`, `FStepIn`) does not keep `Mem.seen`, so read-read coherence is lost across
other threads' steps.

**Failure scenario.** A condition variable with two waiters (a worker pool, `Io.Group`, a
producer/consumer with several consumers) cannot use the contract at all. Four instances (`ioEvent`,
`resetEvent`, `ioCond`, `threadCond`) and their clients prove the restricted statement. Lifting
the restriction later changes the contract's statement, and every instance and client must be
re-proved. CLAUDE.md forbids weakening a spec, but the restriction is a scope that is still being
extended.

**Fix.** Put read-read coherence into the step relation now: `FStepIn` keeps the other threads'
`seen` entries for locations over frame bytes, as the S1 design (docs/sep-threads.md:121-123,
"the other threads' `seen` entries stay") intended. Then restate the event and condition contracts
for N waiters (one ghost ticket per waiter) before more instances or WaitGroup/RwLock/Semaphore are
built on the one-waiter shape.

## 5. Shared contract signatures change in parallel lanes (fix now)

None of the seven lane tips contains the landing tip. Beyond textual conflicts, three pairs change
the meaning of a shared definition under each other:

| Change (lane) | Built against the old meaning (lane) |
|---|---|
| `FAllocInv.tok` gets a fee `Frac`; `alloc` takes `I.own ⋆ I.fee φ`; `granted p k φ bs`; `allocPost … φ` (arena-reset:ZigLean/Sep/Full/AllocSpec.lean, +182) | lists-append: `Proofs/Lists/Alloc.lean:101-340`, `Append.lean` (40M-heartbeat proofs), `Container.lean`, `interfaces/ListsSpec`. All use `I.granted p 3 bs` with no fee, and the fee commits are not ancestors of lists-append |
| `FTTriple`'s step relation `StepIn` → `FStepIn`; `FLock.Inv.wp_liftMem` and `recordX` restated (csl-s1-const:ZigLean/Sep/Full/Lock.lean) | mig-sync-handoff4: the new `Event.lean`/`Cond.lean` (3k lines) quantify over `StepIn` (Event.lean:153). 17 files are shared with CSL, among them Lock, LockWord, Local, Block, Conc/Word |
| `Enc Io`/`Enc Allocator`/`Enc ThreadId` decode only handle bytes; proofs that load `io` need `BlkOk` facts (enc-exactness-2) | mig-sync-handoff4 rewrote `Proofs/Iogroup/Counter.lean` (1625 lines changed); csl-s1-const edits `Proofs/Sync/{Mutex,Handoff,SemCounter,RwLock}` and `ZigLean/Mem/{Basic,Thread,Alloc,Enc}` too |

**Failure scenario.** Each pair merges textually and then fails to build. The fix-ups land in the
largest and slowest proofs: lists `append` and the sync clients.

**Fix (order).** landing → enc-exactness-2 (soundness first; its proof patch is small) → fsym
chain → arena fee (signature) → lists-append rebased on the fee → csl-s1 (`FStepIn`) →
mig-sync rebased on csl-s1 **before it writes more** → arena-reset. Rule for the coordinator: a PR
that changes a contract's signature (`FAllocInv`, `FAllocSpec`, `CAllocSpec`, `FTTriple`'s
relation, an `Enc` of a model type) names every lane that consumes it, and those lanes rebase
before continuing.

## 6. `intExtOrder?` guesses the encoding for an unknown backend (fix before enc merges)

**Evidence.** enc-exactness-2:Air2Lean/Air/Dialect.lean:297:

```lean
def intExtOrder? (d : Dialect) : Option String :=
  if d.version.intPaddingExtended || d.backend == "stage2_x86_64" then some … else none
```

Every backend other than `stage2_x86_64` before 0.17.0 gets the ≤0.16 LLVM encoding (padding
undefined at a store, ignored at a load). That includes `unverified`, the legacy profile, whose
reference model is x86_64, where Debug uses the self-hosted backend from 0.15.2. It also includes
any backend admitted with `--allow-unqualified-build-mode` (`stage2_aarch64`, `stage2_wasm`,
`stage2_c`, …). The same file treats `unverified` conservatively for another fact:
`misplacesEuPayload` (:331) counts `unverified` as possibly LLVM.

**Scenario.** A 0.15.2 Debug x86_64 export with a legacy schema, translated with
`--profile legacy-abi64-le`: `i10ZeroPad(0x0200)` is `-512` in the model and `512` natively (the
BUG-1 row of docs/architecture-audit/enc-exactness.md on that branch).

**Fix.** Make it three-valued: LLVM gives `intEncOf`; `stage2_x86_64` gives `intEncExt`; anything
else (including `unverified`) rejects storage of an integer with padding bits, with a diagnostic
that names the backend.

## 7. "External storage is not written during the run" has no premise ID (fix now, docs)

docs/generated-code.md:270-271 (csl-s1-const): "external writes during the run are not modelled".
External blocks (`Zig.ExternBlock`, L12) that are not `writable` become `.constGlobal`
(ZigLean/Mem/Basic.lean:1342). Before MM-20, a read of one recorded an access. Now it records
nothing (`recordAccessIn`, Basic.lean:676), so a model run races with nothing there. The
assumption that no C thread writes an `extern const` storage block during the run is now
load-bearing for race freedom, but neither docs/premises.md nor assurance/premises.json has an ID
for it. SEM-02 only says that a `const` global is never written by the program, and EXT-04 covers
registry model calls only.

**Fix.** Add a premise row (for example EXT-06, "external static storage is not written during
the run"). Derive it from the `ExternInit` token, so that claims of programs with `extern` globals
list it.

A related note: atomic loads still record on `const` blocks (non-RMW `atomicLoad`,
ZigLean/Mem/Thread.lean:207; `unorderedPrep`, ZigLean/Conc/AtomicWord.lean:41-42). That is
conservative, but it means there is no thread rule for an atomic read of a `const` global.
docs/architecture-audit/memory-model.md MM-20 states "a read of a `const` global records nothing"
without that exception.

## 8. Heartbeat growth (gate now; engine work later)

| Tree | `maxHeartbeats` options | ≥ 1M | ≥ 10M | max |
|---|---|---|---|---|
| origin/main | 20 | 13 | 0 | 4M |
| landing | 24 | 18 | 0 | 4M |
| lists-append | 32 | 26 | 4 | **40M** |

`lists-append:Proofs/Lists/Append.lean:195,215,250,268` need 40,000,000 heartbeats (200× the
default) for `ArrayList(u32).append`, a 30-line std function. `Alloc.create_spec` needs 2M.
Memory: the CSL handoff records "rss 11 GB is hit intermittently even with `--jobs 1`" on the full
build (cap 12 GB). The 9e kernel blow-up (definitional `StateT.run` joins) was fixed by
proof-carrying normalization (#274). The engine handoff also notes that `tryRule`'s `catch` turns
deterministic timeouts into "no rule", which hides cost.

**Failure scenario.** `HashMap`, `ArrayList` growth paths and `std.sort` are each several times
`append`'s size. At this rate full std coverage exceeds the 12 GB cap and CI time.

**Fix now (cheap).** A heartbeat gate in preflight: any `maxHeartbeats` above 4M must cite an
open engine-ledger row. **Later.** Profile `append` (planner backtracking over `granted`/`buf` with
existentials, provider depth 6) and fix it in the engine.

## 9. `fsym` special cases (debt; later, but stop adding)

`fsym` is still one engine with registries (`@[fsym]`, `fsym_provider` by the `.of_within`
convention, `fsym_plan` range laws, `fsym_view`, `fsym_facts`, `fsym_drop`). The registries do
not carry everything, though:
- **Library heads hard-coded in the engine** (fsym-views:ZigLean/Sep/Full/Auto.lean, 4077 lines,
  +866 over the landing): the share/authority planner over `bshare`/`bauth` (`St.auth` :2276,
  `lendShare` :2296, `planShares` :2524), region carving over `regionIn` (`carve` :2375),
  struct parts (`ReadsAt.base/field/mono` :1482-1590, `load_reads` pushed last for every load
  :3537, `storeSplitRule?` :3618), `EncField` (:1371), `callIndirect`, `Frac.half`.
- **Rule variants per resource shape** (csl-s1-const:ZigLean/Sep/Full/Mmap.lean): `mmap'`/`mmapC`,
  `mremapMove'`/`mremapMoveC`/`mremapMoveCore`, `munmapTail'`/`munmapTailR`,
  `mremapShrink'`/`mremapShrinkR`, `munmapWhole'`/`munmapWholeCore`, plus providers
  `mremapShrink_of`/`_at`/`_cut`.
- **Client workarounds**: `alistG` (lists-append:Proofs/Lists/Append.lean:172), an `if`-free copy
  of `alist`, because an assertion-level `if` whose condition names an existential is not decided.
  Also `cases x` on a symbolic `Except` result (engine #20/#35).

**One mechanism.** Everything the planner knows about a resource should come from registered
algebra: split/join laws (exists), lend/return laws for shares and authorities (new registry
kind; `bshare`/`bauth` become its first instances), and views (exist). One rule per op over the
most precise resource; the weaker shapes come by `@[fsym_view]`/`@[fsym_drop]`. Assertion-level
`if` is decided by case-splitting on the condition after instantiating the existential witnesses
from the state. Until then: no new hard-coded heads in `Auto.lean`.

Positive: the hand thread mirrors (`:= ofSeq …`) fell from 31 (landing) to 21 (fsym-ofseq),
and to 27 on csl-s1-const, which contains fsym-ofseq. No `Proofs/` file registers its own
`@[fsym]` rule.

## 10. The full-state library's roots still import the legacy layer (later; before A7)

landing:ZigLean/Sep/Full/Res.lean:1 `import ZigLean.Sep.Triple`; Full/Logic.lean:2
`import ZigLean.Sep.Total` (→ `Sep.Loop`); Full/Triple.lean:2-3 `import ZigLean.Conc.Lemmas`,
`ZigLean.Sep.Block`. 12 Full modules import `ZigLean.Conc.*` (13 on mig-sync-handoff4, which adds
`Conc.Word`/`WeakWord`; its module docs now say memory-model facts only). Plan A's `Sep/Base`
split has not started, so A7 (delete the legacy layer) cannot happen without first re-rooting
`Res`/`Logic`/`Triple`.

**Fix.** Move the vocabulary that Full uses (Heap, Assert, `pts`/`arr` defs and run lemmas,
`AllocSpec.Region`/`Norm`, `Mem` lemmas from `Conc.Lemmas`) into `ZigLean/Sep/Base/*`. Full
imports only Base and Mem. Add a check-tree ratchet: no `ZigLean/Sep/Full/*` import of a
`LEGACY_MODULES` module.

## 11. CI discovery is hard-coded (later; cheap)

landing:.github/workflows/ci.yml has 3551 lines and 335 literal `tests/roadmap/` paths. The
sep-full step is one `lake build` line of about 40 modules (ci.yml:1119) that fsym-views,
csl-s1-const, lists-append and arena-reset each edit, so each pair conflicts. Each kernel-checked
CX adds a 9-line inline Python stanza (csl-s1-const adds four). Plan C1 (discovery manifests) has
not started.

**Fix.** A per-directory manifest (`tests/roadmap/<dir>/ci.toml`: modules, check script, expected
axioms) and one generic runner. The CX stanzas become one table.

## 12. `Ghost` is a closed record (later)

landing:ZigLean/Sep/Full/Res.lean:1157: `structure Ghost where led extent cl cr`, built with
anonymous constructors (`Ghost.unit`, `Ghost.add`). Each new resource kind (epoch tokens went into
`led`; the stack depth and step ticks on codex/stack-sp) touches `Ghost`, `GOk`, `Valid` and every
proof that destructures them. `ACell` (codex/stack-sp:ZigLean/Sep/Full/ACell.lean) is the right
generic cell. Finish the move: `Ghost` becomes a keyed family of ACell-style cells, `cr` its first
key, and `sp`/ticks keys rather than fields.

## 13. `Byte.handle` builds the std-model representation into `Byte` (later)

enc-exactness-2:ZigLean/Mem/Basic.lean adds `ModelHandle := allocator | io | thread tid` and
`Byte.handle`. For `std.Thread` this is right (a platform handle the model does not have). For
`Allocator` and `Io` it fixes BUG-2 in the hand-written std model, which CLAUDE.md retires
("allocators, threads and IO come from translated real Zig code"). In translated and interface
mode the allocator is two real pointers (`CVTable`, `vtR` in Dispatch.lean). The fix is sound and
fails closed. The risk is that more std types are turned into handles instead of being
translated.

**Rule.** No new `ModelHandle` kinds without an audit entry. Remove `.allocator`/`.io` together
with the std models (D2).

---

## What to do in the next two days

1. Fail closed at non-solo ops in `soloRun` (finding 1), with a CX test.
2. Merge enc-exactness-2 right after the landing, with the three-valued `intExtOrder?` (finding 6).
3. Order the contract-signature merges (finding 5): fee before lists; csl-s1 before sync continues.
4. CSL lane: S4 (`CTriple` as the thread-stop triple, `WP.call_fowned`) before more `CTriple`
   clients; `CAllocSpec` restated as `FnSpec`s (finding 2).
5. Engine lane: a design note for an `fsym` `WP` mode; sync lane: no new `*Impl` instances until it
   exists. Restate the event and condition contracts for N waiters with `seen` kept by `FStepIn`
   (findings 3 and 4).
6. proof-framework.py: detect `WP`/`*Impl`; add a heartbeat gate; add the premise row of finding 7.
