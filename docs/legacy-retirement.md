# Legacy retirement plan (planner 2026-10-14, read-only analysis)

This is the recorded deletion plan for the `legacy-to-retire` entries of `assurance/proof-framework.json`
([proof-framework.md](proof-framework.md)). Lanes L1-L13 and the stages D-a to D-e are the IDs that PRs and
the ROADMAP cite; edit the lane text in the PR that changes the lane. Moved here from the coordinator's
handoff directory on 2026-10-15 without changes to the text below; "engine rows #N" there are rows of the
[engine ledger](engine-ledger.md) (the first `#20` is row `20a`, the atoms equal up to arithmetic).

Goal: ONE proof framework on main. Delete the legacy layer after migrating its users.
Sources: origin/main d2072ce1e (`assurance/proof-framework.json`: 96 `legacy_users`), the READY-PENDING
branch tips of `_coordinator.md` "POST-LANDING MERGE ORDER", Plan A, migration-brief, lane handoffs.

## 0. Baseline after the merge train

Branches whose tip removes legacy users (diffed against origin/main's list, base-recent branches only;
`mig-sync-iogroup-wip`, `lists-alloc-contract`, `iface-model-bridge`, `csl-mmap` have stale bases and are ignored):

| branch | removes |
| --- | --- |
| lists-append (+ lists-fba-witness) | Proofs/Lists/{Append,Container}, container-contracts/Clients, tutorials/memory-safety/{Main,Negative,Solution} (6) |
| mig-sync-handoff4 | Proofs/Iogroup/Counter, Proofs/Sync/Handoff, Proofs/Threadsync/Handoff, Full/ThreadBridge (4) |
| csl-s1-atomic / csl-s1-const / csl-s4* | Full/{Atomic,AutoClaims,Conc,Mmap,Pinned,ThreadBridge}, alloc-arena/AllocArena/Core (7) |
| fold-delete-bridge / fold-mmap | same set minus Atomic (ofTriple/ofTotal deleted; Full/Logic and Full/Triple lose their `TotalTriple`/`Triple` names) |

Union = 16 files done. **96 - 16 = 80 files remain** (this plan covers all 80).
`ZigLean/Sep/Full/AutoRules.lean` shows up as a 97th entry on pf-structural's tip, but only through an older
base (legacy lemma `pts_slice_field_load`); it is not a user on main. Verify after the merge train, no lane.

Findings about the ratchet itself (lane L1):
* **False positives.** `LEGACY_NAMES` scans the `import` lines, so `import ZigLean.Sep.Full.Triple` counts as
  "names Triple". Full/Ghost, Full/Tame and (after fold-delete-bridge) Full/Logic are listed for that reason alone;
  Full/Atomic was too. One-line scanner fix (strip `import` lines before the name scan); no proof work.
* **False negatives.** `LEGACY_MODULES` omits `Conc.{Csl,TlsLemmas,Witness,Lock,LockBase,LockRules}` and the
  other legacy Conc modules. Their importers are invisible: Conc/{Detach,Lock,Transfer,Unroll},
  Full/{ThreadOwned,ThreadTls}, Proofs/Threads/Disjoint, spawn-failure/Runtime, thread-tuples/ThreadTuples/Proofs,
  thread-locals/ThreadLocals/Leak (10 files). "Ratchet empty" is not enough to delete Conc/Csl. L1 extends the regex
  (needs maintainer approval, +10 entries) so the list is exact.
* Legacy-status entries outside `legacy_users` that also must reach zero: 44 judgments (Conc.Lock `Lock/Fits/FitsOn/Step`,
  Conc.Logic `WP`, Conc.Spec.* (5 specs), Conc.Total (3), Conc.TimedBudget (2), Conc.Clock `StepIn`, Conc.Lemmas `Grows`,
  LockBase `LocsKeep`, Conc.Witness `TLive`, Proofs.Sync.{RwLock,Semaphore} (4), Float.Allowed `AllowedSpec`, tests:
  futures `CancelSpec`, asm-wrappers `Spec`, claims.Fixture `Wrapped/FWrapped`, sep-full `FTripleCell/FTripleExact`)
  and 23 tactic entries (Sep.Step 7, Automation 2, Wrappers 2, Norm `gen_norm`, Full.Conc `conc_norm`, Full.Tame `tame`,
  Full.Extent `within`, Full.Unroll `unroll_solo`, Conc.Unroll `unroll_sched`, Conc.Lemmas `blkat_alloc`, Spec.Count
  `tomega`, VC.Extract (3), Witness (2), VersionGate `when_defined`, Threadsync.Lock `if_decl`, AllocArena.Core 12,
  AllocFba 3, Air2Lean.Sem 2, Floatops 2, idle-loops `nn_step`, Assurance/audit commands). Section 5 assigns them.

## 1. Legacy library modules and their importers

Not imported by `ZigLean.lean` (proof-only), not by Air2Lean (exe/lib) and not by any script at run time. Importers are
Lean files in `ZigLean/`, `Proofs/`, `tests/`, `tools/`, `tutorials/`, plus names in the files listed below.
Direct importers on main, minus the 16 done files:

| module | direct importers left |
| --- | --- |
| Sep/Triple (Triple, `pts`, `arr`, `copyItems`) | Automation, Block, Discard, Loop, Try, Full/Res, tools/Assurance |
| Sep/Total (TotalTriple, Returns, TotalTripleIn) | Lists/Sep, AddrReuse, AllocSpec/{Norm,Region}, Bounded, Full/Logic (until bridge), Mmap, Step, Witness, tools/Assurance; transitively 200 files (strength-log via Full.Strength) |
| Sep/Loop | Sep.lean, Cost, Total |
| Sep/Block (`Mem.SameThreads`) | Conc/Own, Sep.lean, Alloc, AllocSpec/Ops, Full/Triple, resize-remap/Check |
| Sep/Alloc | Sep.lean, AddrReuse, Cost, Mmap, Owned, Remap, Sentinel, allocation-policy/Check |
| Sep/{Owned,ArenaClient,RawAlloc,Remap,Sentinel,SentinelRealloc} | each other, Sep.lean, allocator-identity/{Check,Kernel}, sentinel-realloc/Check, resize-remap/Kernel, byte-sentinel/Check |
| Sep/Cost, Bounded | Lists/Cost, Lists/Bounded, Witnesses/Sep, claims/Fixture, tools/Assurance |
| Sep/AllocSpec (+Wrap, Wrappers, Dispatch) | each other, Full/AllocSpec, Full/Dispatch, alloc-fba/{Bridge,Fba}, PageObstruction |
| Sep/AllocSpec/{Region,Ops,Norm} | **kept as base**: Full/{AutoRules,Reclaim,Region,Malloc}, Wrappers; they import Total/Block and hold legacy `TotalTriple` rules (strip) |
| Sep/Witness, Conc/Witness | Lists/Sep, Witnesses/{Sep,Conc}, claims/Fixture, Conc/Unroll, Proofs/Threads/Disjoint, RwLockContract, SnapshotCache |
| Sep/{Try,TryAlias,Discard,Step,Automation,Mmap(Sep),AddrReuse} | Sep.lean, each other, Lists/Sep, Wrappers, tutorials/Controls (AddrReuse); Sep/Mmap: none |
| Conc/Own (TTriple) | Conc/Csl, Conc/Witness, claims/Fixture, tools/Assurance |
| Conc/Csl, TlsLemmas | Conc/{Detach,Lock,Transfer}, Full/{ThreadOwned,ThreadTls}, spawn-failure/Runtime, thread-tuples, thread-locals/Leak |
| ZigLean/Sep.lean (umbrella) | Lists/Sep, Witnesses/Sep |

Non-Lean references that must be edited in the deletion lanes: `.github/workflows/ci.yml` (about 20 `lake build` lines
name `ZigLean.Sep.{Automation,Total,Cost,Bounded,Step,AllocSpec*,Mmap,Try,Discard,Loop}` and `ZigLean.Conc.{Csl,TlsLemmas}`),
`assurance/claim-heads.json` (heads at Sep.Triple, Sep.Total, Sep.Bounded, Conc.Own), `assurance/policy.json`,
`assurance/premises.json`, `assurance/register/{L04,M05,P01,P06}.md`, `scripts/mutate.sh` (comment on Csl),
`scripts/proof-framework.py` (regexes), `tests/roadmap/{alloc-fba,alloc-translated,allocation-policy,allocator-identity,
byte-sentinel,claims,resize-remap,sentinel-realloc,thread-locals}/check.sh|static.py|mutant.sh`,
`tests/roadmap/proof-framework/test_proof_framework.py`, `tests/roadmap/thread-tuples/mutation-tests.py`.

## 2. Totals and blocker counts (80 remaining files)

Codes: NONE (plain migration or deletion), TOOL (gate/claims tooling, no proofs), TICK (tick-cost model), D2 (hand-written
allocator model to retire), ENG (fsym engine gap), CONC (CTriple/WP/seen-floor), STAY (strength-log: stays, compiled
against legacy defs, until the final PR).

| blocker | files | which |
| --- | --- | --- |
| NONE | 20 | Lists/Sep, Controls, Sep/{AddrReuse,Mmap,Try,TryAlias,Discard,Step,Automation}, Sep.lean, 3 strength relocations, Base split (Full/{Res,Triple,AllocSpec,Dispatch}, AllocSpec/{Region,Ops,Norm}) |
| TOOL (gate/claims/witness tooling) | 9 | Full/{Ghost,Tame,Logic}, Assurance, Fixture, Witnesses/{Sep,Conc}, Sep/Witness, Conc/Witness |
| TICK | 4 | Lists/Bounded, Lists/Cost, Sep/Bounded, Sep/Cost |
| D2 (hand-written allocator / std model) | 19 | Sep/{Alloc,Owned,RawAlloc,Remap,Sentinel,SentinelRealloc,ArenaClient}, 7 model tests, Sep/AllocSpec, Wrap, Wrappers, Sep/Dispatch, alloc-fba/Bridge |
| ENG (fsym engine rows #12 realloc, #20 atom arithmetic, FBA reset design) | 2 | alloc-fba/{Fba,Client} |
| OTHER | 1 | alloc-translated/PageObstruction (obsolete finding, becomes a doc record) |
| CONC (CTriple/WP, seen-floor, Impl instances) | 13 | 10 Sync/Threadsync clients, Conc/{Own,Csl,TlsLemmas} |
| STAY (strength-log / last-PR core) | 12 | 8 strength-log files + Sep/{Triple,Total,Loop,Block} |
| total | 80 | |

Class (approximate): strength-log 8 (stay until the final PR), proofs about 19 (Lists 3, sync/threadsync 10, alloc-fba 3, relocations 3), tests 9 (7 model checks, Fixture, PageObstruction), tutorial 1 (Controls), tools 3 (Assurance, Witnesses/Sep, Witnesses/Conc), the rest (about 40) library modules.
Effort by lane: S lanes L1, L2; M lanes L3, L4, L7, L9; M-L lane L5; L lanes L6, L8, L10, L11, L12.

## 3. Lanes (parallel inside a group, easiest first). Lanes in one group touch disjoint files.

Group 1 (start now, independent)

### L1. Gate hygiene (S, 1 agent, 1 day). Blocker TOOL.
| file | what | uses | blocker | eff | class |
| --- | --- | --- | --- | --- | --- |
| ZigLean/Sep/Full/Ghost.lean | ghost-resource FTriple rules | none (listed through `import Full.Triple`) | TOOL false positive | S | library |
| ZigLean/Sep/Full/Tame.lean | `Tame` (program keeps layout), `tame` tactic | none (same false positive); `tame` tactic entry is legacy-to-retire | TOOL | S | library |
| ZigLean/Sep/Full/Logic.lean | `FLogic`, `FReturns`, FTotalTriple | `Sep.Total` import + `TotalTriple` until fold-delete-bridge; false positive after | TOOL (after fold chain) | S | library |
Work: strip `import` lines in the name scan; extend `LEGACY_MODULES` to the Conc cluster (maintainer approval, adds 10
entries, section 1); re-run `--write`. Also decisions memo (section 7).
Deletable after: nothing.

### L2. Strength examples out of finished proofs (S each, 1 agent, 1 day). Blocker NONE.
| file | proves | legacy pieces | eff | class |
| --- | --- | --- | --- | --- |
| tests/roadmap/dispatch-templates/TokenizerProof.lean | total correctness of `countTokens` (labelled switch) with fsym | `TotalTripleIn` strength example | S | proof |
| tests/roadmap/loop-tactics/nested/Proof.lean | nested loops by fsym | `TotalTriple`, `TotalTripleIn` strength example | S | proof |
| tests/roadmap/vcs/Extract.lean | memory VCs = FTotalTriple contracts (addTo, swap, ...) | `TotalTripleIn` strength examples | S | proof |
End state: move the examples into new `tests/roadmap/strength-log/{DispatchTemplates,LoopTactics,Vcs}.lean` (class pre-approved);
the three proof files leave `legacy_users`. Also needed for 3 more files with the same pattern checked in section 6 (none found).
Deletable after: nothing.

### L3. Sep/Base split (M, 1 agent, keystone, 4-5 days). Blocker NONE. Must be ONE owner (same Base files).
Create `ZigLean/Sep/Base/*` (Plan A): vocabulary only, no judgment: `pts`/`arr`/`copyItems` + `_run` lemmas (from Sep/Triple),
`Mem.SameThreads` (Sep/Block), `RawVTable/AllocInv/granted/keepsPrefix/allocPost/resizePost/remapPost` and the pure
`Logic` record (Sep/AllocSpec), `VTableFns/dispatch/vtR` (Sep/AllocSpec/Dispatch, used by Full/Dispatch), `mapping` if still
needed by Full/Mmap.
| file | what it holds | change | eff | class |
| --- | --- | --- | --- | --- |
| ZigLean/Sep/Full/Res.lean | FAssn resources (1860 lines) | `import Sep.Triple` -> Base | S | library |
| ZigLean/Sep/Full/Triple.lean | FTriple, Tame, Holds (1195) | `Sep.Block` -> Base (`SameThreads`); `ofTriple` already gone with fold-delete-bridge | S | library |
| ZigLean/Sep/Full/AllocSpec.lean | FAllocSpec, FAllocInv | `import Sep.AllocSpec` -> Base vocabulary | M | library |
| ZigLean/Sep/Full/Dispatch.lean | CAllocSpec, FnSpec dispatch | `AllocSpec.Dispatch` vocabulary -> Base | S | library |
| ZigLean/Sep/AllocSpec/Region.lean | region algebra (kept) | `Sep.Total` import; strip legacy `TotalTriple` rules (Full/Region has the native ones) | M | library (kept) |
| ZigLean/Sep/AllocSpec/Ops.lean | region ops (kept) | `Sep.Block` import; strip `TotalTriple` rules | M | library (kept) |
| ZigLean/Sep/AllocSpec/Norm.lean | `gen_norm` normalization (kept) | `Sep.Total` import; `gen_norm` tactic -> `fsym_norm` (legacy tactic entry) | S | library (kept) |
Risk: AllocArena.Core, Full/Reclaim and AutoRules import Region/Ops/Norm and are owned by arena/engine lanes; the split moves
names, not statements (re-export shim until Group 3). Run alloc-arena, sep-auto, sep-full, alloc-fba checks.
Deletable after: nothing yet, but **no file under `Sep/Full/` imports a legacy module any more.**
L3 RESULT (codex/sep-base, 2026-10-14): Base = Sep/Base/{Pts,Block,Alloc}. No re-export shim: legacy Sep/Triple and
Sep/Block import Base and keep only the judgment. Region/Ops/Norm TotalTriple rules moved into legacy Sep/AllocSpec.lean
(deletion plan: go with Sep/AllocSpec in L6, stage D-b). AllocInv/granted/*Post/Logic stay in legacy Sep/AllocSpec (Full
uses FAllocInv; Logic.ofTotal is a TotalTriple field). gen_norm deleted (alloc-fba uses `simp only [fsym_norm]`).
Remaining Full -> legacy imports are the Conc cluster only: Full/{ThreadOwned,ThreadTls,ThreadFacts,LockWord} (L12).

Group 2 (after Group 1 L3; independent lanes)

### L4. Lists + dead-end modules (M, 1 agent, 4 days). Blocker NONE (lists-append landed).
| file | what | uses | eff | class |
| --- | --- | --- | --- | --- |
| Proofs/Lists/Sep.lean | `push_spec`, `reverse_spec`, `freeAll_spec` over `create(Node)` (321) | `Triple`, `TotalTriple`, `sep_step(s)`, Sep.Witness | M | proof |
| tutorials/memory-safety/Controls.lean | refuted clients (push/freeAll/sum buggy) | AddrReuse facts, builds Proofs.Lists.Sep | M | tutorial |
| ZigLean/Sep/AddrReuse.lean | legacy `Triple.withPlacement` | Alloc, Total | S | library (delete) |
| ZigLean/Sep/Mmap.lean | legacy mapping rules (821) | Alloc, Total | S | library (delete; Full/Mmap native on fold-mmap) |
| ZigLean/Sep/Try.lean, TryAlias.lean, Discard.lean | pointer-try / discard ownership (native in Full/Try) | Triple | S each | library (delete) |
reverse/sum are done in Proofs/Lists/Linked (full-state). push/freeAll need an Allocator-parameter proof: lists-append's
`CAllocSpec` = 4 FnSpecs + generic bridge provides it. The strength example for each theorem goes to `strength-log/ProofsLists.lean`
(exists). Controls: restate the three refuted clients with FTotalTriple/negative controls (Main/Negative/Solution already moved).
**Deletable after L4:** Sep/AddrReuse, Sep/Mmap, Sep/Try, Sep/TryAlias, Sep/Discard (prune Sep.lean; drop CI lines 1845, 1870).

### L5. Hand-written allocator models, D2 (M-L, 3 agents in parallel). Blocker D2.
5a Sentinel/realloc chain: Sep/{Sentinel,SentinelRealloc,RawAlloc,Remap} + tests byte-sentinel/Check, sentinel-realloc/Check, resize-remap/{Check,Kernel}.
5b Owned/arena: Sep/{Owned,ArenaClient} + allocator-identity/{Check,Kernel}.
5c Alloc/policy: Sep/Alloc + allocation-policy/Check.
| file | proves | legacy pieces | eff | class |
| --- | --- | --- | --- | --- |
| Sep/Sentinel.lean (81) | `allocSentinel` owns n+1 bytes | Triple, Alloc | M | library (delete) |
| Sep/SentinelRealloc.lean (441) | byte realloc / sentinel realloc owns `remapBytes` | Triple | M | library (delete) |
| Sep/RawAlloc.lean (252) | raw vtable interface contracts (M04) | Triple | M | library (delete) |
| Sep/Remap.lean (231) | remap whole-block facts | Alloc | S | library (delete) |
| Sep/Owned.lean (281) | cross-allocator free/reset (M01) | Alloc | M | library (delete) |
| Sep/ArenaClient.lean (386) | request-scoped arena client `session_spec` | Owned | M | library (delete; replaced by AllocArena Core + reset) |
| Sep/Alloc.lean (258) | OOM rules of the hand-written heap, `releaseAttempts` | Block | M | library (delete after Cost) |
| tests/roadmap/allocation-policy/Check.lean | executable regression of `AllocPolicy` | `releaseAttempts` helper | S | test |
| tests/roadmap/allocator-identity/{Check,Kernel}.lean | executable + kernel check of M01 client | ArenaClient | S, M | test |
| tests/roadmap/byte-sentinel/Check.lean, sentinel-realloc/Check.lean | executable regressions | Sentinel, RawAlloc | S each | test |
| tests/roadmap/resize-remap/{Check,Kernel}.lean | executable + kernel check of remap | Block, Remap | S each | test |
End state: executable checks stay (they test the `Mem` model); the helper defs they import (`releaseAttempts`, `sentinelBytes`,
`remapBytes`, `dupeBytes`...) move into `ZigLean/Mem/*` as plain defs (no triples); each retired theorem gets a documented
replacement over translated allocators/FAllocSpec or is listed as dropped in `docs/alloc-spec.md` "Retired claims" (register M01/M04/M05).
Kernel.lean files (`session_spec`) become full-state statements over the translated arena. ENG dependencies:
byte `realloc`/`allocSentinel` contracts need engine rows #12 and #20 (draft `scratch-alloc/w5-realloc-draft.lean`) and the translator
gap "mem.Allocator.allocSentinel rejected in translated 0.17 mode"; the arena replacement needs `arena-reset` + `arena-free-fsym` merged.
Deletable after 5a/5b: Sentinel, SentinelRealloc, RawAlloc, Remap, Owned, ArenaClient; after 5c AND L8: Alloc.
**L5b note (2026-10-14, coordinator ruling):** Sep/Owned, Sep/ArenaClient, allocator-identity/Kernel deleted on
codex/l5b-owned; M01 (a) `Core.granted_in_node`, (b) `ArenaSpec.reset_free_all_frame` (tests/roadmap/alloc-arena).
(c) session_spec & co. = "replaced (pending)". **Planned lane (not started):** ONE generic session client over
`FAllocSpec` + a `ResetLedger` reset (translated Zig client, proved once for every allocator meeting both), instances:
FixedBufferAllocator after codex/fba-reset-ledger merges; patched arena after its `alloc` is proved (wpts headers).
Blocker for the arena instance: stock arena has no `alloc` (`not_fallocSpec_arena`, O-E/O-B), patched `alloc` unproved.

### L7. Witness and claims tooling (M, 1 agent, 3-4 days). Blocker TOOL.
| file | what | uses | eff | class |
| --- | --- | --- | --- | --- |
| ZigLean/Sep/Witness.lean (74) | `Admit`/`Live` witnesses for `Triple` | Total | S | library (delete) |
| ZigLean/Conc/Witness.lean (72) | `TLive` for TTriple | Conc.Own, Sep.Witness | S | library (delete; FTTAdmit/FTTLive exist in Full/Witness) |
| ZigLean/Witnesses/Sep.lean (229) | witnesses for Lists/Sep and Cost theorems | Sep, Witness, Cost | S | tool (delete) |
| ZigLean/Witnesses/Conc.lean (151) | witnesses for TTriple theorems | Conc.Witness | S | tool (delete) |
| tests/roadmap/claims/Fixture.lean (271) | claim-strength classifier fixtures over `Triple`, `TotalTripleWithin`, `EventuallyReturns`, `TTriple`, `Wrapped` | Witness, Bounded, Own | M | test |
| tools/Assurance.lean (342) | imports every claim head so a module cannot shadow it | Triple, Total, Bounded, Own | M | tool |
End state for Fixture and Assurance (long-term, no loss of the anti-spoofing property): `claim-heads.json` keeps the legacy head names as
**reserved names** (no import needed) and `claims.py` rejects any theorem whose head resolves to a reserved or unknown name; Fixture is rewritten
against `FTriple/FTotalTriple/CTriple` heads plus reserved-name negatives. Order: Witnesses/* can only go after their users
(Lists/Sep in L4; TTriple clients in L9-L11), so L7 first removes the claim-head import dependence, then deletes witness modules as users disappear.
Deletable after: Sep/Witness (after L4, Fixture), Conc/Witness (after Fixture, Witnesses/Conc, RwLockContract, SnapshotCache in L9).
**L7 step 1 (codex/claims-reserved, 2026-10-14):** claim-heads.json `reserved` holds the 8 legacy head names. claims.py rejects them by name and blocks them in hypotheses. tools/Assurance.lean imports only the Full heads. Fixture uses the Full heads plus 3 Conc.Total spoofs, approved by the coordinator 2026-10-14. Fixture, tools/Assurance and `Wrapped` leave the ratchet. No witness module was deleted, because every candidate still has users:
- Sep/Witness: Proofs/Lists/{Append,Sep}.lean, Conc/Witness, Witnesses/Sep.
- Conc/Witness: Proofs/Sync/{RwLockContract,SnapshotCache}.lean, Proofs/Threads/Disjoint.lean, Conc/Unroll.lean, Witnesses/Conc.
- Witnesses/{Sep,Conc}: the companions of the Sep/* and Conc/* library lemmas, so they go with those modules (D-c, D-d).
Witnesses/{Mem,VC} are not legacy. L7 step 2 deletes Sep/Witness after L4, and Conc/Witness after L9 and L12 (Disjoint, Unroll). The claim `bound` and under-premise mechanisms have no registered head now. They are tested through the spoofs in a test-only registry. If L8 ends up with no bounded head, the final PR removes them.

Group 3 (needs design or engine work; start the design now, implement as unblocked)

### L6. Allocator wrappers and the FBA client (L, 2 agents). Blocker ENG + D2.
| file | proves | legacy pieces | blocker | eff | class |
| --- | --- | --- | --- | --- | --- |
| Sep/AllocSpec.lean (218) | `AllocSpec` judgment over a `Logic` | Triple, TotalTriple | D2/judgment (vocabulary moved in L3) | S | library (delete) |
| Sep/AllocSpec/Wrap.lean (188) | `Wrap.*` hand-written step semantics of std `mem.Allocator` wrappers | AllocSpec | D2 (hand-written std model) | M | library (delete) |
| Sep/AllocSpec/Wrappers.lean (746) | wrapper contracts for any `AllocSpec` (`sep_from`, `tame_prim`) | Wrap, Automation | D2 | M | library (delete; Full/Wrappers is the native one) |
| Sep/AllocSpec/Dispatch.lean (158) | vtable dispatch, `vtR` | Wrappers | D2 (vocabulary to Base in L3) | S | library (delete) |
| tests/roadmap/alloc-fba/AllocFba/Fba.lean (1268) | translated FixedBufferAllocator meets `AllocSpec` | Dispatch, TotalTriple (146) | ENG #12 realloc contract, #20, FBA reset design (ResetLedger second instance) | L | proof |
| tests/roadmap/alloc-fba/AllocFba/Client.lean (691) | `fba_client` returns OOM code or `v+v+(v+1)`, realloc keeps prefix | TotalTriple (89), `sep_from`, TotalTripleIn | ENG (same), `roomFor` full-state form | L | proof |
| tests/roadmap/alloc-fba/AllocFba/Bridge.lean (161) | translated wrappers = `Wrap.*` | Wrap, Dispatch, Norm; tactics `bridge_norm`, `bridge_close` | D2: disappears when Client is proved over the translated wrappers (alloc-param lane) | M | proof |
| tests/roadmap/alloc-translated/PageObstruction.lean (193) | why the legacy `AllocSpec` cannot hold for the page allocator | AllocSpec, Triple | OTHER | S | test |
End state: FBA and Client move to `FAllocSpec`/`CAllocSpec` (lists-append's four `FnSpec`s) with the translated `Allocator` code walked
directly (no `Wrap.*` model); `Bridge.lean` and the `bridge_*`/`pure_norm` tactics are deleted. PageObstruction becomes a doc record
(`docs/alloc-page.md`, the obstruction is what motivated FAllocSpec) plus a kernel-checked counterexample if one is wanted; it cannot stay compiled
after `AllocSpec` goes, so it is deleted in the same PR as AllocSpec with the finding preserved in the docs.
Deletable after L6: Sep/AllocSpec, Wrap, Wrappers, Dispatch, Automation (and Step once L4 is in).

### L8. Tick-cost model (L, design-blocked). Blocker TICK.
| file | proves | legacy pieces | eff | class |
| --- | --- | --- | --- | --- |
| Proofs/Lists/Bounded.lean (56) | `sum_loop_within`: loop of `sum` exits in `xs.length+1` runs; tight | `TotalTripleWithin`, `LoopRuns` | L | proof |
| Proofs/Lists/Cost.lean (284) | allocation counts (retire per alloc-spec.md) and exact loop-body counts | `Sep.Cost` | M (counts part) + L | proof |
| ZigLean/Sep/Bounded.lean (163) | `TotalTripleWithin` | Total, Cost | delete after users | library |
| ZigLean/Sep/Cost.lean (301) | `Mem.allocs/liveHeap`, `LoopRuns` | Alloc, Loop | delete after users | library |
Blocker (kernel-checked in `codex__mig-lists.md`): credits are not spent by the semantics, so `FTotalTriple` with credits cannot bound loop runs
(`credits 0 = emp`). Needed: a tick per `Zig.loop` body run/call in the model, a non-mintable tick authority in `GOk` (stack-region lane's
generic authoritative cell, "ACell generalizing CCell: credits, sp, later ticks"), loop/call rules in `Full/Loop` that consume one credit per body run,
then `sum_loop_within` restated as `FTotalTriple` + credits with the tightness as a kernel-checked negative. Allocation counts (`push_cost`, `liveHeap`)
are retired by the `docs/alloc-spec.md` row. Design report from the stack-region lane first (`codex__stack-region.md`: step-tick design report).
Also feeds Conc.Total (`EventuallyReturns`, `ReturnsWithin`): same mechanism with turn credits.
Deletable after L8 + L7 + L5c: Sep/Bounded, Sep/Cost, Sep/Alloc, Witnesses/Sep.

### L9-L11. Concurrent clients (CONC). Fixed ruling: no new `*Impl` until fsym WP mode (#290, merged) and seen-floor.
Common recipe (as Handoff on handoff4): statements verbatim, `CTriple`/`FOwned` + Full/Lock/Mutex/Cond/Event `*Impl`, thin walks over
`Proofs/Handoff/*`-style generic protocol lemmas, `fsym` WP mode, one strength note (none: these are `∀ schedule` theorems, not triples), Native/aarch64/0.17 check rows
of the old fixture. Premise of the old files: they use `TTriple` only via `WP.liftM_owned (TTriple.load …)`, hand `unroll_sched`, and the legacy `Conc/Lock` library.

L9 Mutex-based clients (M each, 1 agent, 1 week). Existing `MutexImpl`/`IoMutexCode`/`Proofs/Sync/Contracts` suffice.
| file | proves | eff | class |
| --- | --- | --- | --- |
| Proofs/Sync/Mutex.lean (970) | `mutexCounter` = 4 under every schedule, no race/deadlock (Io.Mutex, 0.16) | M | proof |
| Proofs/Threadsync/Mutex.lean (889) | same, `Thread.Mutex` (0.15.2) | M | proof |
| Proofs/Sync/SnapshotCache.lean (803) | reader sees consistent snapshot (`MutexContract`), `cache_spec`/`cache_safe`; imports Conc.Witness | M | proof |
| Proofs/Sync/RwLockContract.lean (217) | restricted shared-lock contract adapter (`ProtectedFacts`); imports Conc.Witness | M | proof |

L10 Condition/semaphore clients (L, 1 agent, 2 weeks): needs a `SemImpl` on `FCond`+`MutexImpl` (one-waiter scope accepted, multi-waiter after seen-floor).
| file | proves | eff | class |
| --- | --- | --- | --- |
| Proofs/Sync/Semaphore.lean (2916) | `Sem.wait_spec`/`post_spec` of translated Io.Semaphore; `Sem.Fits` | L | proof |
| Proofs/Sync/SemCounter.lean (1482) | `semaphoreCounter` = 4 under every schedule | M | proof |
| Proofs/Sync/Mailbox.lean (1173) | producer/consumer over `SemContract`, result 34 | M | proof |

L11 RwLock and WaitGroup (L, 1-2 agents, 3 weeks): need `RwLockImpl` (readers/writer, state word) and `WaitGroupImpl` + Event; seen-floor lifts the one-waiter limit.
| file | proves | eff | class |
| --- | --- | --- | --- |
| Proofs/Sync/RwLock.lean (4707) | `rwLockRead` result in {2,12,22}, safe; `Sem.Spec` legacy judgment | L | proof |
| Proofs/Sync/RwLockSnapshotPair.lean (224) | snapshot-pair client of the RwLock contract (0.16/0.17 tree) | M | proof |
| Proofs/Threadsync/WaitGroup.lean (3561) | `waitGroup` result 2 under every schedule (Thread.WaitGroup + ResetEvent + Mutex, 0.15.2) | L | proof |

Task 08 (RwLock) has a design-only phase until both seen-floor (task 06) and L10's `SemImpl`
(task 07) are merged on `main`; no new `*Impl` code or branches stacked on those changes before
then. Its contract proposal is reviewed in the draft PR description. The proposed boundary has
exclusive acquire/release and shared acquire/release, for arbitrary client resources and live
reader sets. Shared readers hold protocol handles while one protected full-state resource stays
in the invariant; the last reader can transfer that complete resource through `SemImpl` to a
waiting writer. Extent fractions do not provide fractional ownership of bytes. The general
active-reader read/record and reader-drain clock rules need to be specified before implementation:
`FLock`/`LockWord` currently model an exclusive 4-byte mutex, and `wp_readRest`'s `ReadShared`
premise requires prior writes to precede every thread, rather than just admitted readers. Reuse
those libraries through general lemmas; do not copy a client-specific holder or `wp_io` walk.
`Threadsync/WaitGroup` is a separate futex lane (STD-05), outside task 08. Design review does not
remove these files from `legacy_users` or satisfy the implementation gates.

### L12. CSL layer retirement (L, CSL agent, after L9-L11 and the D-WP decision). Blocker CONC.
| file | what | uses | eff | class |
| --- | --- | --- | --- | --- |
| ZigLean/Conc/Own.lean (408) | `TTriple` thread-local heap triple, `TTriple.{load,store,alloc,free,storeAt,..}` | Block | M | library (delete) |
| ZigLean/Conc/Csl.lean (537) | `Owned` parts of the heap, `Owned.{step,fork,join,keep,start,shrink,add}`, `WP.liftM_owned` | Own | L | library (delete or re-state over FOwned) |
| ZigLean/Conc/TlsLemmas.lean (629) | `TTripleIn`, TLS lemmas | Csl | M | library (delete; Full/ThreadTls is native) |
Consumers to move first (invisible to the ratchet today, listed by L1): Conc/{Detach,Lock,Transfer,Unroll}, Full/{ThreadOwned,ThreadTls}, Proofs/Threads/Disjoint,
spawn-failure/Runtime, thread-tuples/ThreadTuples/Proofs, thread-locals/ThreadLocals/Leak (`unroll_sched`, `blkat_alloc` tactics, legacy `Lock/Fits/Step`).
Open decision D-WP: `Proto.WP` is `legacy-to-retire` in the ratchet but all migrated sync proofs (Handoff, Counter) use it with FOwned. Recommended: the maintainer re-statuses
`Proto.WP` as `target` (it is the all-schedules adequacy engine under `CTriple`, with fsym WP mode as its backend), and retires only `TTriple`, `Owned`, `TlsLemmas`, `Conc.Lock`, the Conc specs
(`MutexSpec` ...) and `Conc.Total`. Without this decision L12 has no end state.

### L13. Final deletion (see section 4)
| file | role at the end |
| --- | --- |
| ZigLean/Sep/Triple.lean (453) | `Triple` judgment (strength examples need it); vocabulary already in Base |
| ZigLean/Sep/Total.lean (167) | `TotalTriple`, `Returns`, `TotalTripleIn` |
| ZigLean/Sep/Loop.lean (127), Block.lean (239) | loop rules / `SameThreads` (Total imports Loop) |
| ZigLean/Sep/Step.lean (541), Automation.lean (113) | `sep_*` tactics (delete in Group 3 once L4 and L6 are in; they have no strength dependency) |
| ZigLean/Sep.lean (12) | umbrella: shrink with every deleted module, delete last |
| tests/roadmap/strength-log/{GlobalInit,GlobalPayloadPointers,OutcomeTaxonomy,ProofsLayout,ProofsLists,ProofsPointers,ProofsSlices,TryPointers}.lean | STAY (class pre-approved) |

## 4. Final deletion PR (stages)

Stage D-a (after L4): delete Sep/{Try,TryAlias,Discard,Mmap,AddrReuse}.
Stage D-b (after L6): delete Sep/AllocSpec* (Wrap, Wrappers, Dispatch, AllocSpec), Automation, Step; `sep_*`, `sep_from`, `tame_prim`, `sep_frame/normalize` tactic entries go.
Stage D-c (after L5, L7, L8): delete Sep/{Alloc,Owned,RawAlloc,Remap,Sentinel,SentinelRealloc,ArenaClient,Cost,Bounded,Witness}, Witnesses/Sep.
Stage D-d (after L9-L12): delete Conc/{Own,Csl,TlsLemmas,Witness,Lock,LockBase,LockRules,Detach,Transfer,Unroll,Total,Spec/*,TimedBudget}, Witnesses/Conc.
Stage D-e = the **final PR** (needs the strength log):
1. Run every `tests/roadmap/strength-log/*.lean` and `Full/Strength.lean` against the legacy defs; attach the output and the per-theorem precondition-delta table (D1) to the PR body.
2. Delete `tests/roadmap/strength-log/`, `Full/Strength.lean` (`toTriple_on`, `toTotal_on`), `Sep/{Triple,Total,Loop,Block}.lean`, `Sep.lean`; check `Full/Init` lost its dependency on `Sep.Total`.
3. `assurance/proof-framework.json`: `legacy_users: []`, no `legacy-to-retire` judgment or tactic entries; `scripts/proof-framework.py` regexes and `test_proof_framework.py` reduced to the target set; `claim-heads.json` legacy heads become reserved names.
4. Acceptance (Plan A): (a) ratchet list empty and the extended regex finds nothing; (b) `git grep -wE "Triple|TotalTriple|TotalTripleIn|TTriple|TTripleIn|TotalTripleWithin|Returns"` outside `ZigLean/Sep/Base` (and docs) is empty; (c) full build of default targets + `Proofs` + `AssuranceTools`, no raised `maxHeartbeats` (`git grep maxHeartbeats` unchanged vs main); (d) `scripts/claims.py` shows no strength loss against the recorded inventory (re-record `docs/theorem-inventory.md`, `assurance/claim-heads.json`); (e) strength log attached; (f) `assurance/premises.json`, `docs/premises.md`, `assurance/register/{L04,M05,P01,P06,M01,M04}.md` updated, `scripts/register.py generate`; (g) ci.yml `lake build` lines and the `check.sh`/`mutant.sh` files of section 1 point at surviving modules; (h) docs mention no deleted module (`docs/sep-full-state.md`, `alloc-spec.md`, `proof-framework.md` migration table becomes history); (i) `scripts/regen.sh --pr`, `preflight.sh`, native Docker rows (x86_64 Rosetta, aarch64) of the parts touched (alloc-arena, alloc-fba, sync fixtures, thread-locals).

## 5. Per-item ownership of the legacy-status judgments/tactics outside `legacy_users`
* Sep.* judgments (`Triple`, `TotalTriple`, `Returns`, `AllocSpec`, `Logic`, `AllocInv`, `TotalTripleWithin`, `Live`, `Mem.SameAllocs`, `Mem.SameThreads`, `ArenaClient.Grows`): disappear with L3-L8 and the final PR (`SameThreads`, `AllocInv`, `Logic` survive as Base vocabulary and must then be re-statused `target` or renamed).
* Conc.* (`TTriple`, `TTripleIn`, `TLive`, `Lock*`, `Spec.*`, `Total`, `TimedBudget`, `Clock.StepIn`, `Lemmas.Grows`, `WP`): L12 + D-WP; `Conc.Total`/`TimedBudget` also need the L8 tick mechanism.
* Proofs.Sync.{Semaphore,RwLock} local `Fits/Sem/Step/Sem.Spec`: vanish with L10/L11.
* Tests: `CancelSpec` (futures), `asm-wrappers Interp.Spec`, `FTripleCell/FTripleExact` (sep-full CX files), `Wrapped/FWrapped` (Fixture, L7): pure-result or counterexample fixtures; re-status as target when they are `FTriple` instances, or rewrite (needs maintainer approval for any status change).
* Tactics: AllocArena.Core 12 `arena_*` macros and `within`/`unroll_solo` were approved only "gone before landing"; they are gone from `legacy_users` (Core done) but the 12 entries remain: arena lane replaces them with `@[fsym]` rules. `Air2Lean.Sem` (`mono_step/ok_step`), `Floatops` (`fma_case/spec_case`), `idle-loops nn_step`, `Threadsync.Lock if_decl`: module glue for pure/float/lock proofs, owner: respective proof lanes (not in this plan's 80 files).

## 6. Execution order and critical path

```
Group 1: L1 (1d) ; L2 (1d) ; L3 (4-5d)                         [parallel; L3 gates all Full-free deletions]
Group 2: L4 (4d) ; L5a/b/c (1-2w, parallel) ; L7 (4d) ; L9 (1w)   [parallel after L3 (L9/L7 independent of L3)]
Group 3: L6 (2-3w, needs engine #12/#20/#28 + FBA reset) ; L8 (design now, impl 2-3w) ; L10 (2w) ; L11 (3w)
Group 4: L12 (1-2w) ; D-a..D-e
```
Critical path (longest, with unknowns): **CSL/seen-floor -> SemImpl -> Semaphore/SemCounter/Mailbox (L10) -> RwLockImpl/WaitGroupImpl + RwLock/WaitGroup (L11, about 8.4k lines) -> L12 CSL layer -> Conc cluster deletion -> final PR**
(about 8-10 weeks of one sync agent plus the CSL agent). Riskiest: **L8 tick model** (design not yet decided; blocks Sep/Cost, Bounded, Alloc, Lists/Bounded, Lists/Cost, Fixture heads and Conc.Total) and **D-WP** (a status decision without which L12 has no target). Third chain: engine rows #12/#20 -> FBA (Fba 1268 + Client 691 lines) -> L6 -> D-b, about 4 weeks, parallel to the others.
Quick wins (one week, 14 files out of the ratchet or retargeted): L1 (3), L2 (3), L3 (7), plus L4 deletions (5 library modules).

## 7. Decisions needed from the maintainer before the lanes start
1. Extend `LEGACY_MODULES` to the Conc cluster (adds 10 visible users; "only shrinks" rule).
2. D-WP: re-status `Proto.WP` as target (recommended) or require a CTriple-only replacement.
3. Tick-cost design: ticks in `Mem`/GOk, one credit currency (matches the ruling "credits not mintable") and who owns it (stack-region lane vs CSL lane).
4. Strength-log end state: keep `Full/Strength` + `Triple/Total/Loop/Block` compiled until the final PR (this plan), or snapshot the legacy statements as frozen `theorem` text in the PR body and delete earlier. Recommended: keep until the final PR; it is the only check that migrated statements are not weaker.
5. Claim heads: reserved-name mechanism in `claims.py` instead of importing deleted modules.

## 8. Per-file table (80 files, one line each: lane / blocker / effort / class)
Proofs/Lists/Sep L4 NONE M proof | Lists/Bounded L8 TICK L proof | Lists/Cost L8 TICK M-L proof |
Proofs/Sync/Mutex L9 CONC M proof | Sync/SnapshotCache L9 CONC M proof | Sync/RwLockContract L9 CONC M proof | Threadsync/Mutex L9 CONC M proof |
Sync/Semaphore L10 CONC L proof | Sync/SemCounter L10 CONC M proof | Sync/Mailbox L10 CONC M proof |
Sync/RwLock L11 CONC L proof | Sync/RwLockSnapshotPair L11 CONC M proof | Threadsync/WaitGroup L11 CONC L proof |
Conc/Own L12 CONC M lib | Conc/Csl L12 CONC L lib | Conc/TlsLemmas L12 CONC M lib | Conc/Witness L7 TOOL S lib |
Witnesses/Conc L7 TOOL S tool | Witnesses/Sep L7 TOOL S tool | Sep/Witness L7 TOOL S lib |
Sep.lean L13 NONE S lib | Sep/{Triple,Total,Loop,Block} L13 STAY L/M lib | Sep/{Step,Automation} L6/L13 NONE S lib | Sep/{Try,TryAlias,Discard,Mmap,AddrReuse} L4 NONE S lib |
Sep/{Alloc,Owned,RawAlloc,Remap,Sentinel,SentinelRealloc,ArenaClient} L5 D2 S-M lib | Sep/{Cost,Bounded} L8 TICK M lib |
Sep/AllocSpec L6 D2 S lib | AllocSpec/{Wrap,Wrappers,Dispatch} L6 D2 M/M/S lib | AllocSpec/{Region,Ops,Norm} L3 NONE M/M/S lib (kept) |
Full/{Res,Triple,Dispatch} L3 NONE S lib | Full/AllocSpec L3 NONE M lib | Full/{Ghost,Tame,Logic} L1 TOOL S lib |
tests: allocation-policy/Check, allocator-identity/{Check,Kernel}, byte-sentinel/Check, resize-remap/{Check,Kernel}, sentinel-realloc/Check L5 D2 S-M test |
alloc-fba/{Fba,Client} L6 ENG L proof | alloc-fba/Bridge L6 D2 M proof | alloc-translated/PageObstruction L6 OTHER S test |
claims/Fixture L7 TOOL M test | dispatch-templates/TokenizerProof, loop-tactics/nested/Proof, vcs/Extract L2 NONE S proof |
strength-log x8 L13 STAY - strength-log | tools/Assurance L7 TOOL M tool | tutorials/memory-safety/Controls L4 NONE M tutorial.

Handoff notes: nothing in the repo was edited. Branch order assumptions: fold-delete-bridge before L3 (Logic/Triple lose their legacy names), lists-append before L4, mig-sync-handoff4 + fsym-wp before L9-L11, arena-reset + arena-free-fsym before L5b.

## COORDINATOR DECISIONS (2026-10-14)
1. Extend LEGACY_MODULES to the Conc cluster (honest gate; +10 visible users). Fix the import-line false positives at the same time (L1).
2. Proto.WP -> target (the migrated Handoff/Counter proofs use it; WP mode is in fsym).
3. Tick-cost model: owned by a design agent now (ticks as the memory-authority mode of the generic ACell counter, as in the stack lane's PR3 design); design note first, then implementation lane L8.
4. Keep Full/Strength + Sep/{Triple,Total,Loop,Block} compiled until the final PR (only check that migrated statements are not weaker).
5. claims.py: reserved-names mechanism for legacy claim heads, approved (L7).
Start now: L1, L2, tick design. L3 (Sep/Base split, keystone) starts after merge waves 7 (csl) and 8 (fold) land, to avoid conflicts with queued branches. Group 2 after L3.

## PLANNED LANE (coordinator 2026-10-14, from L5b)
Generic session client over FAllocSpec + ResetLedger reset (replaces retired Sep/ArenaClient session_spec/session_restores/handleRequest_spec). Instances: FBA after codex/fba-reset-ledger; patched arena after its alloc proof. Start after FBA ResetLedger lands.
