<!-- Generated from assurance/engine-ledger.json by scripts/engine-ledger.py generate; edit the JSON. -->
# fsym engine ledger

Engine features and fixes that proofs and libraries needed from `fsym`, and the workarounds that stand
in for the missing ones. This is the recorded deletion plan that CLAUDE.md asks for: code cites a row as
`ledger #<id>` (or ledger `` `<id>` ``), and `scripts/engine-ledger.py check` (preflight)
fails on a citation of a row that does not exist and on a closed row cited as a workaround that is still
there. Data and rules: `assurance/engine-ledger.json`, `scripts/engine-ledger.py`. 145 rows, 57 open.

A row closes when the engine part has landed and no workaround for it is left in the tree. A PR that adds
a workaround adds or cites the row in the same PR; a PR that deletes the last workaround closes the row.
New rows use descriptive lower-case hyphenated slug ids, such as `pick-bind`; never take the next number.
Existing ids and citations stay valid, including `20a`, `21a`, `68d`, `69d`, `70d`, `P09-E1` and `T1`.
After fetching and merging `origin/main`, run `generate`, then `check`. The check rejects duplicate ids,
new numeric ids, and an id whose title differs from `origin/main` (override with `check --base REV`).
Merged id/title pairs are stable: update progress/request text to refine a row; use a fresh slug and
update its citations for a different request. Two PRs can choose slugs independently; if they choose the
same slug for different titles, preflight fails even after merging main. No shared counter is needed.

## Open rows

| Row | Title | Requester | Workaround sites | Deletion plan |
|---|---|---|---|---|
| [case-family-enrollment](#row-case-family-enrollment) | Remove transitional golden case-family enrollment markers | Task23; coordinator decision 6258258831 | `examples/threadsync/all-cases`, `examples/sync/all-cases` | When the last golden family is enrolled, remove every all-cases marker and the marker/history ratchet, derive all case families unconditionally from the full golden enumeration, and retire when_defined/if_decl with their remaining users. Preserve complete output/import coverage and exact retranslation checks. |
| [3](#row-3) | ruleConcl? recognize generic FLogic.T L … rules (FAllocSpec generic in partial/total) | coordinator for D2/allocator | - | - |
| [7](#row-7) | document/plan rule preconditions ⟪φ⟫ from context facts | one-logic-tactics | - | - |
| [9](#row-9) | engine support replacing arena_* macros, within (planner rule), unroll_solo (CTriple-backend rule) | arena lane | - | - |
| [9h](#row-9h) | unroll_solo: concrete counterexample runs | arena lane | - | - |
| [13](#row-13) | optPayload | one-logic-tactics (Lists.sum) | - | - |
| [16](#row-16) | Keep path conditions | one-logic-vc | - | - |
| [17](#row-17) | An undecided side condition φ is split by byCases | one-logic-vc | - | - |
| [18](#row-18) | Binder names | one-logic-vc | - | - |
| [21](#row-21) | fsym_arith: disjunctive goals, user Nat functions on constructors, constructor injectivity | one-logic-tactics (dispatch, PR #222) | `tests/roadmap/dispatch-templates/Template.lean`, `tests/roadmap/dispatch-templates/TokenizerProof.lean` | delete the local `attribute [local fsym_arith] rank` lines once fsym evaluates a user Nat function on a constructor (evalUserCtor covers non-Nat results only); run the two fixtures without them. |
| [21a](#row-21a) | a pure generated helper with literal args (mem_Alignment_fromByteUnits 8) is unfolded and sticks at enumOf... | alloc-param (lists destroy) | `Proofs/Lists/Append.lean`, `Proofs/Lists/Alloc.lean`, `tests/roadmap/interfaces/Interfaces/SentinelSpec.lean` | delete the manual evaluation of the pure helper on its literal once fsym evaluates pure generated helpers on literals (or uses the x.toNat fact). |
| [26](#row-26) | Side goal from an equal hypothesis up to projection and proof irrelevance | mig-tests | `tests/roadmap/try-pointers/TryPointers/AliasProofs.lean` | drop `<;> exact hd` from the `cases u <;> fsym` steps; if fsym closes the side goal up to structure projection and proof irrelevance, delete them and close the row. |
| [27](#row-27) | Planning a user rule whose precondition holds an if-guarded grant (I.owned 0 s.ptr bs = if bs.size = 0 then... | one-logic-alloc | `tests/roadmap/alloc-fba/AllocFba/Wrappers.lean` | state realloc_spec through reallocAdvanced_spec once fsym plans an if-guarded grant against the opened state; delete the inlined walk. |
| [55](#row-55) | Planning and facts whnf-evaluate concrete byte arrays | arena (codex/arena-reset) | - | - |
| [57](#row-57) | Rule order for a store into an owned atomic word | arena | - | - |
| [59](#row-59) | A rule's precondition fact that is an implication | arena | - | - |
| [61](#row-61) | A rule whose precondition has an if the facts do not decide | arena | `ZigLean/Sep/Full/Dispatch.lean`, `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete `CAllocSpec.resize_shrink` and `CAllocSpec.resize_grow` (Dispatch.lean) and pass `CAllocSpec.resize` with `FitsUpTo.fits` in the arena's `loop66` proofs (ArenaSpec*.lean) once a rule whose precondition has an undecided `if` (`relBytes`) is applied with the `if` split as a side condition. |
| [64](#row-64) | An update at a return against a state with an undecided if | fba-reset | `tests/roadmap/alloc-fba/AllocFba/Full.lean`, `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete the `by_cases hc : n.toNat < s.len.toNat` split in `fresize_spec` and the arena's `rcases Nat.lt_trichotomy n.toNat s.len.toNat` in each `resize_ct` (the latter also needs #return-bool-split) once the walk splits the state's undecided `if` before the caller's updates (replaced by the P09-E5 ghost-update registry). |
| [65](#row-65) | An update's Q₀ is compared with library atoms only | fba-reset | `tests/roadmap/alloc-fba/AllocFba/Full.lean` | restate Q0 with the library definitions (`allocPost`, `pshare`, `epFee`) once tryUpd unfolds Q0's user definitions; delete the explicit-atom form. |
| [66](#row-66) | The planner cannot produce an empty region | fba-reset | `tests/roadmap/alloc-fba/AllocFba/Full.lean` | split `alloc_upd` back into carve and grant once the planner produces an empty region and carves at an exact start with a different alignment. |
| [67](#row-67) | updHeads keeps a user head folded only at Qv's top level | fba-reset | `tests/roadmap/alloc-fba/AllocFba/Full.lean` | write `fown` with `fbody` once updHeads keeps a nested user head folded. |
| [68](#row-68) | WP walk: a side goal whose unknown is fixed by a LATER conjunct is not re-solved | L9 | `Proofs/Sync/Mutex.lean`, `Proofs/Threadsync/Mutex.lean` | reorder `workInv` / `workPost` back (the conjunct that fixes k last) once the WP walk retries deferred side goals after their unknowns are assigned. |
| [69](#row-69) | WP rules are tried on a command with a different head; the failed unification unfolds both generated functions | L9 | `Proofs/Threadsync/Mutex.lean` | drop `attribute [local irreducible] Thread_Mutex_lock Thread_Mutex_unlock` once WP rules are keyed by the command head (or unify generated functions at reducible transparency); then `threadMutex.lock_wp` can be passed directly. |
| [69d](#row-69d) | Conc/Spec/MutexToy: witness of the legacy MutexSpec | sync lane | - | delete Conc/Spec/MutexToy together with the legacy MutexSpec (docs/proof-framework.md row); restate the relaxed-unlock counterexample against MutexImpl if wanted. |
| [70d](#row-70d) | Conc/Returns: no client yet | csl/T-term | - | first client: a turn-counting protocol proof (T-term, research C13); if T-term is dropped, delete with Proto.cost. |
| [71](#row-71) | Conc/OsRules: premise evidence, standalone by design | os lane | - | move its futex facts into the full-state OS futex rules (ZigLean/Sep/Full/OsFutex.lean) and the FutexSpec/CTriple futex rules when those land (docs/thread-io-translation.md section 4.1), then absorb the module. |
| [76](#row-76) | Read of a read-shared io prefix in a protocol: hand copies of wp_io | critic run 15 (coordinator) | `Proofs/Sync/SemCounter.lean`, `Proofs/Sync/RwLock.lean`, `Proofs/Threadsync/WaitGroup.lean`, `Proofs/Sync/Semaphore.lean` | when each legacy-layer file migrates to the full-state logic (docs/legacy-retirement.md), replace its `wp_io` copy with `FLock.Fits.wp_readRest` and its holder copies with `FLock.Fits.wp_hold`. Keep the primitive load/record proof shared through Inv.loadRest. Close this row only when every listed legacy workaround site is gone. |
| [return-bool-split](#row-return-bool-split) | A return whose Boolean value the postcondition matches on is not split | arena-gen (arena macros -> fsym) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete `rcases Nat.lt_trichotomy n.toNat s.len.toNat` in each arena `resize_ct` (with #64) once the walk splits a return's undecided Boolean that the postcondition matches on. |
| [arena-resize-update-cost](#row-arena-resize-update-cost) | (perf) whole-state updates at every return: the arena's resize | arena-gen (arena macros -> fsym) | - | - |
| [carve-size-probes](#row-carve-size-probes) | A carve's size probes searched the case facts of other regions | arena-retain (retaining reset over wpts headers) | - | - |
| [packed-lawful-split](#row-packed-lawful-split) | LawfulPacked for vector and packed-union fields: the law split by direction | critic 32 (review of #450, packed-roundtrip) | `ZigLean/PackedLayout.lean`, `tests/roadmap/sep-auto/SepAuto/Packed.lean` | The single-direction `LawfulPacked` class of ZigLean/PackedLayout.lean becomes the two directional classes (the conjunction kept as `LawfulPacked`), and the fail-closed `Wrap` example of the bits direction in tests/roadmap/sep-auto/SepAuto/Packed.lean becomes a proved round trip (the value direction stays fail-closed for the union); a vector-field struct joins the regressions. |
| [chain-case-unfold](#row-chain-case-unfold) | A recursive list predicate unfolded by the case the loop tests | arena-retain (loop78 of the retaining reset) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | replace the per-case bullets of `loop78_step` (ArenaSpec.lean, ArenaSpecMacos.lean, ArenaSpecFixed.lean) with one uniform `fsym` walk, drop the local `fsym_atom` attribute and delete `chain_one`, `chain_cons2`, `chain_full_cons2` and `chain_head` (Reset.lean) if no other proof uses them, once fsym unfolds a recursive list predicate by the case the step tests. |
| [P09-E2](#row-p09-e2) | strongest-postcondition inference at returns for FTotalTriple/FTriple and the thread backends, as inferPost... | P09 | - | - |
| [P09-E3](#row-p09-e3) | abduction report | P09 | - | - |
| [P09-E4](#row-p09-e4) | @[fsym_inv] loop-invariant registry | P09 | - | - |
| [P09-E5](#row-p09-e5) | @[fsym_upd] ghost-update registry keyed by heads, tried at returns | P09 | - | - |
| [recursive-group-total](#row-recursive-group-total) | Generic total correctness of a recursive function group | L8b-1 tick coverage (Task 09); P03/stack | - | - |
| [T1](#row-t1) | credits n is not split for tick_credit | stack-ac lane (codex/stack-ac-ticks) | - | - |
| [fowned-bridges](#row-fowned-bridges) | Step through the WP.liftMem_fowned* / callMC_fownedS bridges | coordinator | - | - |
| [ofseq-one-liners](#row-ofseq-one-liners) | Seven remaining hand ofSeq one-liners | coordinator (critic run 9) | - | - |
| [stack-child-budget](#row-stack-child-budget) | A spawned thread's stack budget, reserve and sp token | stack-region lane (codex/stack-pr5) | - | - |
| [stack-wp-cur](#row-stack-wp-cur) | The WP walk hands cur t to a thread's segment (WP.liftMem_fownedCurS) | stack-region lane (codex/stack-pr5) | - | - |
| [allocator-creation-admissibility](#row-allocator-creation-admissibility) | Bind allocator creation admissibility to the visible instance claimed | Task10 allocator-creation soundness review | - | - |
| [admission-at-state](#row-admission-at-state) | Expose exact FAdmit side goals from the currently held full state | Task10 / coordinator PR400 comment6211941344, 2026-10-16 | - | - |
| [conc-base-owned](#row-conc-base-owned) | Direct full-state ownership facts and pure concurrency vocabulary | Codex Task 01 / L12 | `ZigLean/Conc/LockBase.lean`, `ZigLean/Conc/Lock.lean`, `ZigLean/Conc/LockRules.lean`, `ZigLean/Conc/Word.lean`, `ZigLean/Sep/Full/LockWord.lean`, `ZigLean/Conc/Csl.lean` | Retire LocsKeep through the existing FStepIn/RestStep machinery and restate its lock consumers on FStepIn without weakening their contracts. Reuse the generic Conc.Base.Threads facts in the remaining legacy Owned.fork/join proofs while that layer remains, then delete those rules with Conc.Csl. If the lock migration needs a contract change, stop and post the exact obstruction with a counterexample for the maintainer. Keep LocsKeep legacy-to-retire and every real consumer in the structural gate until actual retirement. |
| [errok-native](#row-errok-native) | WP walk of raw MemM steps in a partial protocol: the error leaf (Proto.ErrOk) from library *_native facts | S4 (audit soundness-2026-10-14) / critic run 15 | `Proofs/Atomics/Relaxed.lean`, `Proofs/Cancel/Group.lean`, `tests/roadmap/futures/Futures/Proofs.lean`, `tests/roadmap/thread-locals/ThreadLocals/Leak.lean` | when fsym walks raw liftMem steps of a protocol main and discharges `Proto.ErrOk` from the library `*_native` facts, replace the hand `WP.bind (WP.liftM (ErrOk.of_run rfl …))` chains in the workaround sites with `fsym` and delete the explicit `ErrOk.of_run` arguments; the invariant facts (`flag_single`, `flag_vals`, `status_bytes`) stay as the proofs' invariant. |
| [premise-runtime-fallback](#row-premise-runtime-fallback) | Conservative runtime-source premise fallback | Task 04 premise attribution / coordinator | `scripts/premises.py`, `tutorials/allocation-failure/README.md`, `tutorials/concurrent-clients/README.md`, `tutorials/cross-target/README.md`, `tutorials/external-contracts/README.md`, `tutorials/first-proof/README.md`, `tutorials/generic-containers/README.md`, `tutorials/memory-safety/README.md`, `tutorials/mutable-arrays/README.md` | Track replacement in https://github.com/riventic/air2lean/pull/418 and its fresh-main precision split. Remove broad runtime-source token attribution and the corresponding conservative tutorial additions only as reviewed family-complete declaration attribution replaces them, with fresh kernel-checked dependency graphs and source fingerprints. Every modeled semantic route needing a removed premise must reach an authenticated carrier; unresolved, new or changed routes retain fallback. A reachable carrier absent from the coarse baseline is a hard error. Regenerate the index through the official pipeline, update the exact tutorial premise lists and run scripts/tutorials.py lint, validate retained-premise and dropped-premise controls, and remove resolved workaround sites. Keep this row open while the broad fallback remains. |
| [current-thread-subst](#row-current-thread-subst) | A substituted `m.current = t` breaks the caller's rule terms (kernel type mismatch) | STD-05 step A (codex/std-retire-futex-rules, PR #437) | `tests/roadmap/sep-auto/SepAuto/WPOsFutex.lean` | when fsym re-elaborates or maps the caller's rule terms through its substitutions, delete the `subst hc` before `fsym` in `WPOsFutex.event_wait` and pass `hc` to the rule again. |
| [word-family-views](#row-word-family-views) | A word's plain rules are reached only under the word's own head | arena-retain (coordinator review of #446) | `ZigLean/Sep/Full/AtomicPlain.lean` | once `viewAtoms` prefers the views that lose nothing (regression: the offset cases `store_beside_*`/`load_beside_*` of `tests/roadmap/sep-auto/SepAuto/AtomicPlain.lean` pass with only the `tptsE_*` rules registered), register `tptsE_load`, `tptsE_storeBytes`, `tptsE_store`, `tptsE_loadPacked`, `tptsE_storePacked` as `@[fsym]`, add the views word ↔ `tptsE` (`@[fsym_view]`), register `tptsE_view`, a `facts_tptsE` and `OwnsPtr.tptsE` as a provider, and delete the 14 instances and `wptsE_of`. |
| [fold-recursive-pred](#row-fold-recursive-pred) | Fold a recursive user predicate to match a call rule's precondition instead of unfolding the callee | chore/l4-controls (PR #449, critic 27) | - | - |
| [seen-floor-sync-retirement](#row-seen-floor-sync-retirement) | Finish sync multi-waiter contracts and retire retained old Word exports | Task06 / PR #397 | `ZigLean/Conc/Word.lean`, `ZigLean/Sep/Full/LockWord.lean`, `ZigLean/Sep/Full/Word.lean`, `ZigLean/Sep/Full/WordRules.lean`, `ZigLean/Sep/Full/Event.lean`, `ZigLean/Sep/Full/Cond.lean`, `Proofs/Handoff/Protocol.lean` | Before PR397 is READY, remove the obsolete Word.Op/LocsKeep/BlkStep dependency from every actual new native producer and consumer path, including the shared Fits.stable -> Full.LockWord.Step boundary. Cover preparation, load, all signed/unsigned RMW orders, strong and weak CAS including spurious failure, wait and OS-wait, every WordRules/Event/Cond consumer and retained Handoff result. Check every changed root's actual body and full type, including inherited dependencies, against fixed source/artifact bindings. The inline native Step.locs field must retain both former obligations; retained producers prove its stronger actual array equation. No AMap-to-LocsKeep conversion is allowed. The six unused Word/Protocol preservation exports identified in6277249661 are removed now, rather than deferred as frozen compatibility wrappers. Remaining Word.BlkStep/Op projections and FLock.Inv.wordOp are reported as the old Word-contract family, never as native; retire that family together with its shared legacy producer contracts after their other old consumers migrate. This boundary does not close the row: remove Event/Cond one-waiter/newest-HB workarounds only after general contracts, singleton/owned-ledger instances and multi-waiter regressions are kernel checked. Close only when all listed workarounds and retained old exports are gone and the applicable strict new-fact graph passes. |
| [final-match-greedy](#row-final-match-greedy) | The planner's final match takes the first atom that unifies, also for an existential a later atom fixes | arena-retain (reset's retaining modes) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | drop `attribute [local fsym_atom] FreeList` of `reset_retain_capacity_ct`/`reset_retain_with_limit_ct` and pass `count_spec` for `count_free` (delete `count_free`) in each ArenaSpec*.lean once the final match does not commit to an atom that a later atom's match contradicts. |
| [undecided-eq-branch-cost](#row-undecided-eq-branch-cost) | (perf) A walk through an undecided equality branch of a computed value exceeds the budget | arena-retain (loop66 of the retaining reset) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete the `by_cases hsm : v.toNat < 2` before `fsym` in `loop66_c0` and `loop66_c1` of each ArenaSpec*.lean once one walk of the body with the undecided branch stays within the budget. |
| [per-translation-walks](#row-per-translation-walks) | The same std code translated for several targets is proved once per translation | coordinator (critic run 31, arena retaining reset) | `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | state once, in a shared module over the generic translation, the defs and theorems that ArenaSpecMacos.lean and ArenaSpecFixed.lean repeat from ArenaSpec.lean (main's 24: `free_ct`/`free_spec`, `resize_ct`/`resize_granted_ct`/`remap_ct`/`resize_spec`/`remap_spec`, `al`, `tables`, `child_decode`, `count_loop`/`count_spec`, `Inv19`/`Exit19`/`loop19_step`/`loop19_ct`, `Lists9`/`Inv9`/`Exit9`/`loop9_step`/`loop9_ct`, `deinit_ct`, `reset_free_all_ct`/`reset_free_all_spec`; and the retaining reset's 15: `count_free`, `Inv78`/`Exit78`/`loop78_step`/`loop78_ct`, `Inv66`/`Exit66`/`loop66_c0`/`loop66_c1`/`loop66_step`/`loop66_ct`, `reset_retain_capacity_ct`/`reset_retain_with_limit_ct`/`reset_retain_capacity_spec`/`reset_retain_with_limit_spec`), and make each ArenaSpec*.lean an instance (only a walk over code that differs between translations, the patched `free` and `resize`, stays per module), once the translator emits the shared std code once or fsym walks a module-generic presentation. |
| [arena-retained-capacity](#row-arena-retained-capacity) | The retaining reset's retained capacity is not stated | coordinator (takeover review of PR #468) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | state the retained capacity in `reset_retain_capacity_spec` and `reset_retain_with_limit_spec` of each ArenaSpec*.lean (after the per-translation-walks row, once in the shared module) by linking `Kept`'s `sz` to the limit and the list's capacity, then close this row and drop the 'not stated' wording from docs/alloc-arena.md, docs/allocator-identity.md, tests/roadmap/alloc-arena/README.md and register row M01. |
| [region-end-opt-in](#row-region-end-opt-in) | The owned-region end bound is a per-file opt-in fact | coordinator (takeover review of PR #468) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete the three `attribute [local fsym_facts] MemFacts.region_end` lines (ArenaSpec.lean, ArenaSpecMacos.lean, ArenaSpecFixed.lean) once `fsym` supplies the owned-region end bound on demand (or as a default fact without a measurable cost). |
| [l10-native-lock-step-contract](#row-l10-native-lock-step-contract) | Native lock-step contract before semaphore resource-transfer walks | L10 semaphore migration (Task 07; coordinated with L11 and Task 06) | - | Close after native lock primitive producers and Full consumers preserve the original Step guarantees without registered legacy dependencies, the generic fsym resource-transfer and held/outside signal walks pass strict actual term-and-type closure, and Task 07's translated Semaphore/SemCounter/Mailbox migration is complete. This row authorizes no transitional code. |

## Closed rows

| Row | Title | How it closed |
|---|---|---|
| [1](#row-1) | Replace unsafe evalPlanner (implemented_by) by a declared planner table | READY #199 (d8c670b0) |
| [2](#row-2) | fsym [h]: elaborate rule terms in the main goal context | READY-PENDING codex/fsym-perf d65219fbd (evalFsym withMainContext) |
| [4](#row-4) | unifyKeyed: proof irrelevance and reducible types | open |
| [5](#row-5) | intCast step rule (a.toNat < 2^n → r.toNat = a.toNat) | DONE by one-logic-tactics PR2 (`@[fsym] intCast_step` added to AutoRules.lean after `divTrunc_step`; heads-up for merges) |
| [6](#row-6) | fsym_arith: toNat / width-change normal forms | READY #237 (arith lane, cd5d17f1): both pass; AutoArith.lean normal forms, intCast_step for every signedness |
| [8](#row-8) | TLogic record so fsym drives FTTriple/FTTotalTriple (no FTotalTriple rules in TLogic goals) | open |
| [9a](#row-9a) | Provider backtracking on arithmetic failure | READY #239 |
| [9b](#row-9b) | Pair facts of atoms | open |
| [9c](#row-9c) | Bool facts to constructor equations | open |
| [9d](#row-9d) | ptrEqAddr p q into possibly different blocks (O-F | READY #239 (engine wrote ptrEqAddr_live) |
| [9e](#row-9e) | Memory use of plain fsym on arena resize | open |
| [9f](#row-9f) | Returns closed by module EUpd lemmas (free_last_upd, free_other_upd, resize_shrink_upd, resize_grow_upd, re... | READY #260 |
| [9g](#row-9g) | within goals as planner goals (fsym_entail) | READY #239 (fsym_entail on Within) |
| [10](#row-10) | Full/Arr rules (arr_load/store/ptrProject, facts_arr, split/join) | not engine (library Full/Arr); note only |
| [11](#row-11) | CTriple backend on top of FTTriple (T-ctriple | open (after #1); exact request below (2026-10-12, approved design R2, docs/sep-threads.md §T-ctriple) |
| [12](#row-12) | Precondition planning: region atoms before size-dependent atoms | READY #250 |
| [14](#row-14) | One fsym entry for other front ends | Auto.run is the shared entry for evalFsym and memVc, including introductions, context preparation, run caches and the orphan-proof check; runReport adds residual attribution to that entry |
| [15](#row-15) | Quiet stop | fsym.quiet suppresses the human stop messages; memVc enables it only around Auto.run, so vc_gen refuses an unexecuted command with its own error and no duplicate fsym info (pinned by vcs/Memory.lean). Auto.runReport returns stop reasons without emitting a report message, and fsym.report emits schema-versioned JSON |
| [19](#row-19) | (same shape as 9b, second user) Pair facts from the memory | open |
| [20](#row-20) | Split a match on a symbolic Except result | DONE codex/fsym-wp (agent 13: a body's match on a variable as the command is split) |
| [20a](#row-20a) | Atoms equal up to arithmetic | READY #250 (allocSentinel + realloc drafts close) |
| [22](#row-22) | fold the open arm of an indirect call | DONE in alloc-param PR (a) (M10 library part, 2026-10-12; small Auto/AutoConc edits, heads-up for merges): `callIndirect f arms d` takes the last arm `d` (no MonadExceptOf; args α m f arms d, so indirectWalk reads a[2..4]); `callIndirect_fold_ext` registered in foldCtx; `C.callIndirect_pos/_neg` take implicit `d`, `C.callIndirect_nil f d : callIndirect f [] d = d`; `pullIndirect` pulls `g` from `d >>= g` or keeps `throw e` |
| [23](#row-23) | CTriple rule commands over interface tables | DONE in alloc-param PR (a): `reduceProjs` after `unfoldToHead` (tryRule, CTriple branch) |
| [23b](#row-23b) | row 23 for a table WITH closure arms (CVTable.dispatch (tables e) fns) | DONE on codex/iface-contracts (PR (b)): `expandMapLits` (List.map over a literal expanded, beta-reduced) between two `reduceProjs` in tryRule's CTriple branch. ACCEPTED by the coordinator 2026-10-13 as an engine edit made outside the engine lane: engine lane, review/own it (Auto.lean `expandMapLits`, `unfoldToHead` headBeta first) and fold it into the general rule-matching normalization when convenient |
| [24](#row-24) | raw Nat literal from unification (BitVec.ofNat 6 ?k =?= 3 assigns raw 3) | DONE in alloc-param PR (a): `normNatLits` on P₀i/P₀/Q₀ in tryRule |
| [25](#row-25) | @[fsym] regionStore0/regionLoadWritten0 (Full/Region, alloc-param WIP) broke sep-auto Region.sentinelAt_tot... | attribute removed (ListsSpec: `attribute [local fsym]`); question for M2: prefer the in-place rule when both apply |
| [28](#row-28) | Field access of a generated struct | open |
| [29](#row-29) | a user rule term with an explicit argument that fsym later generalizes fails | READY-PENDING codex/fsym-perf d65219fbd (refreshUser) |
| [30](#row-30) | Views of owned bytes | READY-PENDING codex/fsym-views da5df40ec: `@[fsym_view]` registry (unfold at stuck steps, fold back at returns; `regionIn_view`/`regionIn_fold` registered; per-view rule deletion left to the fold lane) |
| [31](#row-31) | G1: typed load from a region whose bytes are a value's encoding | READY-PENDING codex/fsym-views (load_reads for every load, `ReadsAt.regionInEnc`) |
| [32](#row-32) | G2: atomic words as plain bytes in a planned region | READY-PENDING codex/fsym-views (`apts_view`/`aptsE_view`, joinOnce relabel, size from the token) — repro D2 closes with `fsym [CAllocSpec.free h, toInt_step, cown_refund]` |
| [33](#row-33) | G3: update over two atoms of one head with unknown fractions | READY-PENDING codex/fsym-views (preassign: one Q atom per state atom) |
| [34](#row-34) | (perf) normPre's refine C.ex_sep _ fun x => ?_ / C.lift_sep whnf's the whole program | READY-PENDING codex/fsym-perf d65219fbd (normPre by mkAppM; exCont) |
| [35](#row-35) | Except match inside StateT.run (as 20) | DONE codex/fsym-wp (as #20) |
| [36](#row-36) | Postcondition if whose condition names an existential of the postcondition | READY-PENDING codex/fsym-perf d65219fbd (branch by branch, imp_ite_pos/neg; ordering gap = #44) |
| [37](#row-37) | CTriple.loop's step post if again r.1 then inv r.2 else post r is not decided | DONE codex/fsym-wp (evalUserCtor; arena loop19_step without Post19 verified) |
| [38](#row-38) | A precondition ⟪False⟫ from a match that reduces after a case split leaves the goal open | DONE on codex/fsym-wp a2b453ecb (walk: a fact `False` after normPre closes the step; sep-auto Walk false_pre). Arena: drop `all_goals contradiction` after it lands |
| [39](#row-39) | substCtor on a projection of a result | DONE codex/fsym-wp (etaProj, pairs) |
| [40](#row-40) | A match on a generated function of a constructor | DONE codex/fsym-wp (evalUserCtor; verified on arena) |
| [41](#row-41) | No rule for Zig.vindex | DONE on codex/fsym-wp a2b453ecb (`@[fsym] Zig.Full.Auto.vindex_step`, framed over any P; sep-auto Walk vindex_item). Arena: delete Core's vindex_step and the `fsym [.., vindex_step]` mention after it lands (name clash only if both are opened) |
| [42](#row-42) | store 8 (ctx.add 16) (s : heap_ArenaAllocator_State) misfires next to a region at ctx with a size fact | DONE codex/fsym-wp (refutedSide; reset without reset_heads verified) |
| [43](#row-43) | fsym_entail does not unfold the state's definitions | DONE codex/fsym-wp (updHeads, fsym_entail unfoldLeaves; reset without local fsym_atom verified) |
| [44](#row-44) | #36's if decided before the atoms that fix the existential | DONE codex/fsym-wp (repro-alist-if green) |
| [45](#row-45) | An existential fixed only by a size fact is not assigned | not needed (#44) |
| [46](#row-46) | Heartbeats (gate assurance/heartbeat-budgets.json, measured with fsym-perf) | DONE codex/fsym-wp (append_pos 855k → 49k, precise_pos 175k → 39k) |
| [47](#row-47) | (was agent 9's "#37", a number collision with the arena row #37) solveBlock of a pointer value | READY-PENDING codex/fsym-perf d65219fbd |
| [48](#row-48) | fsym_entail: bytes → region | DONE codex/fsym-wp (viewAtoms + stateFacts in fsym_entail; bytesAt bound lemma is the witness lane's) |
| [49](#row-49) | fsym_entail: extent lending off the authority | DONE codex/fsym-wp |
| [50](#row-50) | fsym_entail: p.add 0 | DONE codex/fsym-wp (by unification) |
| [51](#row-51) | WP: rules about CM steps vs the normal form | open |
| [51b](#row-51b) | Status of the WIP after the Counter run | — |
| [52](#row-52) | WP: ghost choices in protocol rules | note |
| [53](#row-53) | (perf) arith proves a conjunction hypothesis of an update by one omega over every fact | DONE codex/fsym-wp (1.07M → 245k) |
| [54](#row-54) | unifyKeyed compares proof arguments by their head | DONE codex/fsym-wp (regression Walk loop_rule; arena count_spec verified) |
| [56](#row-56) | A match on a loop exit variable under StateT.run is not split | DONE by #20/#35 (fsym-wp); regression sep-auto Conc exit_match on codex/fsym-rows e7538f52a. NOTE: the loop rule must be stated at the generated monad (`CM`/`MM`), not `StateT σ MemM` (#4) |
| [58](#row-58) | fsym_entail panics | open |
| [60](#row-60) | (perf) The child's free of a node inside a large state | open |
| [62](#row-62) | A struct access over several parts in a thread | DONE PR #322 (ownsJoin); the hand lemmas were deleted by PR #350 |
| [63](#row-63) | planShares' split ignores tags | DONE codex/fsym-share-tags: split keyed by (block, tag); regression sep-auto Walk.tags_apart |
| [68d](#row-68d) | Full/ThreadCall (WP.call_fowned): used by fsym's WP backend | DONE PR2; PR #354 merged |
| [70](#row-70) | Holder field steps as one library rule (coordinator item (a)) not landed yet | DONE codex/fsym-wp-hold: the `WP` walk applies `FLock.Fits.wp_hold` itself (`fsym [hF.wp_hold (g' := gH x'), …]`, one term per place the walk reaches): a rule for every `MemM` step is tried after the others and applies only completely; the segment's precondition comes from `hpa`, the side goals from the first one about the segment's post on (`hR`, `hg'`, `hU`) are solved after the segment; `hR` by the post's atoms (`assnByHyp`: equal or provably equal values, AC), `hU` by the protocol's lemma applied backwards (`wpChain`), arithmetic facts of the protocol's shape forwards (`wpForward`); ghost values of products normalized (`upd_snd`, `upd_ne`, data fields of user values). All per-field instances are deleted; the walks of SnapshotCache (`update_spec`, `main`'s snapshot to the free), MutexCounter (both versions' `loop4_body`), Iogroup (`add_spec`) and Handoff (both versions' producer, `ready` loop and `main`'s tail from the spawn) are `fsym` calls. Regression sep-auto WPHold. |
| [72](#row-72) | PageAllocator as an environment of an open std.mem.Allocator | DONE: part 1 #369 (CTriple.toSoloThread: no Tgt map needed; alloc/free/resize thread triples); part 2 codex/l4-page-env (remap thread triple after #368, PageThread.cAllocSpec); the page-backed Lists.Open env chore/l4-controls (tests/roadmap/alloc-translated/ListsPage.lean: ext, env_runs, page_spec) |
| [73](#row-73) | Run-level adequacy to .illegal | DONE: part 1 #364 (KFact.dead, free_dead, munmapWhole_dead, Holds.dead); part 2 codex/l4-page-env (FAllocInv.freed in free's post, coordinator decision B; the page allocator's freed = dead, PageThread.fthread_free). The Controls restatement (chore/l4-controls) needs no run-level theorem: with #77 fixed the kernel evaluates the runs (`.illegal` and the leak) from the start memory |
| [74](#row-74) | PLAN (legacy-to-retire) | DONE chore/l4-controls: tutorials/memory-safety/Controls.lean is deleted; its refuted clients are restated over Proofs/Lists/Open.lean and the translated PageAllocator in tests/roadmap/alloc-translated/ListsPage.lean (`controls`: unconditional refutations of Main.lean's properties from the program's start memory, the runs evaluated by the kernel after #77), and it left `legacy_users` |
| [75](#row-75) | Thread backend: undecided side condition blocks a sequential rule's ofSeq | DONE codex/fsym-thread-split (solveSides: a provider hypothesis with unknowns waits for the later provider goal that fixes them; one equal to an undecided goal of the rule is that goal, so the walk splits); regression sep-auto Threads resizeTo_thread; the PageAllocator's remap is a thread triple by plain fsym |
| [update-result-unknowns](#row-update-result-unknowns) | An update's result unknowns and the bundle projections of its postcondition | DONE: landed with the arena (#279) and its macro replacement (#388) (Auto.lean `tryUpd`, `reduceCtorProjs`) |
| [update-plan-views](#row-update-plan-views) | An update's precondition planned through views of the atoms the planner did not find | DONE on codex/arena-engine (Auto.lean `closePre`); regression `tests/roadmap/sep-auto/SepAuto/Updates.lean` (`upd_view`) |
| [arith-implications](#row-arith-implications) | The arithmetic solver on implications | DONE on codex/arena-engine (Auto.lean `arithGoals`, `arithSimpCtx`, `arithCore`); regressions `tests/roadmap/sep-auto/SepAuto/Arith.lean` (`implies_refuted`, `implies_fact`, `implies_fact_target`, `implies_post`) |
| [rule-instances-first](#row-rule-instances-first) | A rule whose instance arguments have no instance is planned anyway | DONE on codex/arena-engine (Auto.lean `instArgsMissing`, before the precondition's plan); regression `tests/roadmap/sep-auto/SepAuto/AtomicPlain.lean` (`ptr_beside_word` within 250k heartbeats; without the check it hits the limit in `wpts_loadPacked`) |
| [probe-case-budget](#row-probe-case-budget) | A probe's search through the case facts is unbounded | DONE on codex/arena-engine (Auto.lean `omegaFacts (budget)`, `probeCaseBudget`, `withBudget`; probes: `quick` arith, the discharger's side conditions, the offsets of two pointers in `proveEqGoal`). Follow-up on fix/fsym-probe-budget: `withBudget` catches the heartbeat exception wherever in the probe the budget is hit (`mkAppM`, the split-term rewrite, not only `omega`) and fails the probe; it binds within the context's `maxHeartbeats` (the smaller limit; past that one the exception is rethrown); one rule for every cache of the run: nothing obtained under a limit (the heartbeat limit, `heartbeatsOut`, or a search's fuel, `outOfFuel`) is cached as a failure (`limitedRun`: `probe`, `detProbe`, `encFieldOf?`, `structLayoutOf?`, `lawfulEncOf?`, `lawfulPackedOf?`), so a later query with more room (an unbudgeted obligation, another query order) retries it. Regressions `tests/roadmap/sep-auto/SepAuto/Arith.lean` (`budget_outside_omega`, `budget_no_failure_cache`, `budget_within_limit`: the budget spent at once), `tests/roadmap/sep-auto/SepAuto/Structs.lean` (a field of `N2` after `N9`'s, past the nesting budget) and `tests/roadmap/sep-auto/SepAuto/Packed.lean` (`nested_inner_after_outer`); the end-to-end probe (two nodes in blocks of unknown addresses among 27 disjointness facts) arises in the retaining reset's reallocation path, whose proof adds it |
| [thread-local-exlift](#row-thread-local-exlift) | The locality of a rule over a region carved to a size | DONE on codex/arena-engine (AutoThread.lean `ThreadLocal.exLift`, `@[fsym_provider]`); regression `tests/roadmap/sep-auto/SepAuto/Threads.lean` (`headerWord`; without the provider: `fsym: no rule for the command store 8 p x`) |
| [packed-bits-steps](#row-packed-bits-steps) | A packed struct's bits: fromInt steps and the size of its encoding | DONE on codex/arena-engine (AutoRules.lean `packedOfBits_step`, AutoArith.lean `reduceEncodeVia`); regressions `tests/roadmap/sep-auto/SepAuto/AtomicPlain.lean` (`packed_encode_size`, `packed_ofBits`) |
| [packed-roundtrip](#row-packed-roundtrip) | A packed struct's bits read back: toBits (ofBits b) = b | DONE on codex/packed-roundtrip (ZigLean/PackedLayout.lean `LawfulPacked`, `PackedLayout.lawful`, `EnumTags.lawful`; Auto.lean `lawfulPackedOf?`, simproc `packedRoundTrip`, and the other direction `packedValRoundTrip`/`packedValidToBits`, by which the per-type round trips of `Proofs/Layout/Proofs.lean` and `Proofs/Threads/Proofs.lean` are proved); regression `tests/roadmap/sep-auto/SepAuto/Packed.lean` (bool/int/enum/signed-enum/non-exhaustive/float/nested/empty packed structs, a stored `fromInt`, both directions, a packed union field fails closed; the round trips fail on the previous engine: `fsym_arith: not proved`). Review follow-ups on fix/fsym-probe-budget: the context's instance first (`trySynth?` before the closed-type check, as `lawfulEncOf?`: a generic client over `[LawfulPacked T n]`, regressions `generic_bits`, `generic_val`); a derivation past the nesting budget caches no failure for the types inside it (`limitedRun`, ledger #probe-case-budget; regression `nested_inner_after_outer`). The fuel stays: a Lean structure may be recursive and an instance family may nest without end, so termination does not follow from the type. Vector and packed-union fields: ledger #packed-lawful-split |
| [77](#row-77) | Kernel evaluation of runs over a page-sized block: deep recursion / >11 GB | DONE (one form shared by PR #392 and chore/l4-controls, coordinator decision 2026-10-18): `writeBytes` (ZigLean/Mem/Basic.lean) is irreducible and shares the unchanged list suffix (`take` ++ bytes ++ `drop`), which the kernel reduces lazily; the unconditional `writeBytes_eq` keeps the array-splice equation for the lemmas and a checked `@[csimp]` keeps native array execution. The cause was the array form: `Array.extract`/`++` build each part by repeated `push`, a nested `List.concat` chain the kernel unfolds by deep recursion. Open's `push` with the page env now decides from the program's start memory in under a second (tests/roadmap/alloc-translated/ListsPage.lean) |
| [78](#row-78) | LawfulEnc instances for generated structs | DONE codex/eng-78-79: no translator change. One generic theorem `StructLayout.lawfulEnc` (ZigLean/Sep/Full/Struct.lean: a struct whose encoding holds its fields' encodings, all lawful, reads back) and the engine's `lawfulEncOf?` (Auto.lean: the layout from the decoding, `structLayoutOf?`; the parts of the encoding, `encParts?`/`fields_extract_sz`; each field's instance synthesized or derived again), used where `fsym` synthesizes instances (`synthInstArgs`, `solveSides`). The folds `pts_fold_encode`/`pts_fold_write` (`@[fsym_view]`) turn owned bytes of a lawful value's encoding into its `pts`. Packed structs, unions, storage-wrapped fields and encodings that do not write each field where the decoding reads it get none (fail closed). Global `LawfulEnc Slice`. A store piece by piece that applies now beats a split on another rule's undecided side condition (a region store that the derived instance enables). Regression: sep-auto Structs. |
| [79](#row-79) | Struct pts to field words entailment | DONE codex/eng-78-79: `StructLayout.split` and `StructLayout.join` (ZigLean/Sep/Full/Struct.lean: a struct's `pts` is its fields' `pts` and its padding's bytes `padBytes`, the join reading the pieces' labels from the memory) for every struct with a layout; `fsym` takes them as views at a stuck step (`viewAtoms`: `splitFor` for a wanted field of a struct atom's block, `joinView?` for a wanted struct whose pieces are in the state). `ListsFba.struct_words` is deleted (its use is `fsym_entail`). Regression: sep-auto Structs. |
| [P09-E1](#row-p09-e1) | residual-goal attribution | AutoReport collects each residual's program point, judgment, rule, condition and stop reason in schema-versioned JSON; Report.lean checks incomplete sequential, thread, concurrent and protocol proofs, exact ordinary/reporting parity and speculative rollback |
| [T2](#row-t2) | plain atom: tick_plain receipt dropped (bare fsym) | see request text (tick rows, plans/tick-cost.md) |
| [T3](#row-t3) | credits 1 consumed by tick (bare fsym) | see request text (tick rows, plans/tick-cost.md) |
| [T4](#row-t4) | ticks in the CTriple backend (not attempted) | The existing rules walk callMC Zig.tick in sep-auto/Ticks.cbody_spec and its loop in cloop_spec, in the plain mode; no backend-specific tick rule was needed (a historical probe against 958596cfc, 2026-10-16, first showed it; sep-auto/check.sh now checks Ticks). The CTriple evidence covers the plain mode only: a metered (credits) tick under CTriple has no control yet. |
| [T5](#row-t5) | tick_run kept opaque in fsym_norm | see request text (tick rows, plans/tick-cost.md) |
| [pick-bind](#row-pick-bind) | Pick-bind rules: bind rules over pick >>= op >>= g | DONE: PR #352 (merged 2026-10-15) registered `CTriple.weakCasPtr_bind` as `@[fsym]` (AutoConc.lean ~363); `publishWeak_spec` and `publishWeak_frame` are a bare `unfold publishWeak; fsym` |
| [thread-loop](#row-thread-loop) | Loop rule for a Zig.loop in a thread (FTTriple) | DONE PR #319 (codex/fsym-thread-loop: Full/ThreadLoop) |
| [thread-store-sized](#row-thread-store-sized) | A store of a packed struct into an owned word in a thread | DONE on codex/arena-reset-retain: provider `ThreadLocal.store_sized` (AutoThread.lean); regression `tests/roadmap/sep-auto/SepAuto/Threads.lean` (`packedWord`, `packedAtomicWord`: both fail without the provider) |
| [typed-region-release](#row-typed-region-release) | Release a complete block from typed fields while preserving the native stack refund | Native typed-region/extent/release lemmas and approved size-aware matching use data-only hints, witness rollback, shared bounded substitution refresh, unresolved-token inference and independent original side premises. Comments6279182210/6279202049 approved active-path view progress and applied explicit-frame unification. Actual fallback whole Structs, including free_fields_stack with its exact original goal, and the full29-file official sep-auto suite PASS on f9505e4e/main578aa3b2, Auto5614ed37, guards b8bf14f3/e6cbb205. The five unchanged Proofs callers retain their earlier afc52032a/Auto f13fb21a PASS binding69afbe3b; an accepted fixed-size causal audit supports reuse, not a fresh current-source claim. Isolated A/B proved the added ordinary size attempt caused the large-state regression, so Claude6280049836 dropped fix3 and restored the whole carve function exactly to main. The separate case-fact positive remains an explicit expected failure tracked by open carve-size-probes. Fixes1-2 and all other controls remain; no cap increase, broader planner or weakened production statement. Reproduce with tests/roadmap/sep-auto/check.sh; actual report6280488414. |
| [region-memset-read](#row-region-memset-read) | Infer a region read after a defined-value memset | Implemented by ReadsAt.regionMemset/regionMemset0 through the existing region/extraction/decode lemmas. Reproduce with tests/roadmap/sep-auto/check.sh: Region.memset_read and Region.memset_word_reads cover byte and multibyte initial/interior loads. No new provider kind or engine change. |
| [known-bytes-on-demand](#row-known-bytes-on-demand) | Derive requested block-address knowledge from raw bytes without changing global store results | The original storeBlock/storeBlock_finite posts are restored; one requested-knowledge planner precedes region planning and uses known_of_bytesAt. Approved committed-descendant retry, snapshots/fallbacks, source-first determined-block address selection, unknown-block matching and direct-update shape checks remain. Whole actual Structs, including concrete/existential/idempotence/no-request/fail-closed controls, and the full29-file official sep-auto suite PASS on f9505e4e/main578aa3b2, Auto5614ed37, guards b8bf14f3/e6cbb205. The five actual unchanged Proofs callers PASS at their original afc52032a/Auto f13fb21a binding69afbe3b; the accepted causal audit supports retaining that evidence after the final change only restores main's carve. The isolated A/B and Claude6280049836 removed the ordinary size probe while preserving fixes1-2 and the explicit case-fact expected failure. No current-source fresh-five claim or blanket full-build repeat for a head move. Reproduce with tests/roadmap/sep-auto/check.sh; actual report6280488414. |
| [wp-local-hypothesis-application](#row-wp-local-hypothesis-application) | Apply current local proof functions during bounded WP side proofs | Qualified in PR529: at2f1b/main737, Auto/AutoWP fe270e1f/b9839887, whole canonical WP100 jobs, both actual condition modules161 jobs and exact407-target ROOT pass. Guardf07c262a/unit16d97d42 binds1005 unchanged source/command rows; physical ROOT8e2f1fa3/logdc09702f is reused for inventory. Official SepAuto31 builds206 jobs and replays203 modules/2111 theorems with standard axioms; OneLogic8 builds132 jobs and replays129 modules/108 theorems. SepAuto's general assurance output retains3 unchanged-class float-key/test-opaque policy findings; its documented fixture gate passes, not general policy. Currentnessfc737e7a renews only3 supported stale swap recipes, retains13 runs/49 qualified artifacts, and passes official inventory write/check. At a3a634ab8/main737, focused preflight and independent framework both pass (guardb3e8ad24, logs3b2b8c45/d4af7583), fixed inputs/artifacts unchanged. Final review/simple find no actionable issue. One structural walk retains raw/normalized evidence, forwarding priority, proof-local Eq substitution and exact-type own-equation exclusion; observable controls check actual substituted data. Assigned-update/global-definition controls compile; actual fresh FBA Full/no-PANIC evidence retains its35d8 binding. All original failures/source/artifacts remain archived; no new premise, cap, provider or manual walk is introduced. |

## Shared mechanisms

Planning units of the engine lane (one PR each, regressions from every requester); the rows list what each closes.

- **M0** declared range-law table (planner without evalConst): #1 (+ arena range split/join hook). PR #199 MERGED.
- **M1** facts from the memory over atom combinations: `MemFacts X φ` (one atom or a pair `X₁ ⋆ X₂`), `@[fsym_facts]`, addFacts tries atoms and ordered pairs, applied by `pre_mfact` (every backend); plus constructor equations of optional tests in `destruct` (opt_* lemmas). Closes 9b, 19, 9c. READY #213 (990524e4, branch codex/fsym-arena-rows). Arena free plain fsym: none-branch closes; repro /tmp/fsym-eng/arena/{Free.lean,build.sh,run.sh} (~50 s, 96k hb).
- **M2** planning order and re-unification after state updates: provider backtracking on arithmetic failure (retry with facts / next candidate), region atoms before size-dependent ones, re-unify after updates. Closes 9a, 12; supports 9e.
- **M3** pointer comparison across blocks: `ptrEqAddr` rule decided by blocks/offsets with a liveness provider kind. Closes 9d; 9e (resize memory) measured after M1–M3.
- **M4** user updates as planner steps: `EUpd P Q` lemmas in `fsym [u]` applied when `P` frames out and `Q` matches; `Within X P` goals as `fsym_entail` without the update. Closes 9f, 9g.
- **M5** judgment-generic backends via records: rules over `FLogic.T L` (instantiate L), `TLogic` for FTTriple/FTTotalTriple, CTriple on FTTriple; `fsym [h]` with local hypotheses (withMainContext). Closes 2, 3, 8, 11.
- **M6** unification modulo reducible definitions and proof irrelevance (unifyKeyed). Closes 4.
- **M7** one shared entry + quiet stop reason (Auto.run, stop flag, path conditions, unsplit side conditions, binder names). Closes 14–18.
- **M8** (OWNED BY engine-arith agent, new module ZigLean/Sep/Full/AutoArith.lean) arithmetic normal forms: `(a-b).toNat` under `b ≤ a`, `toInt` of nonnegatives, intCast step rule. Closes 5, 6; 7 documented with M2.
- **M9** counterexample runs (`unroll_solo` → term-level expand/decide). Closes 9h (decide with arena lane).
- **M10** (coordinator 2026-10-12, CLAUDE.md #216 "build generic, prove individual items") ONE fsym dispatch rule set for calls through any vtable/interface value under a registered contract (Allocator, Io, Random, Writer, user vtables, callbacks). Coordinate with the interface-contract lane (docs/interfaces.md, handoff codex__alloc-param.md — neither existed yet at 2026-10-12 evening). Today: CAllocSpec.dispatch + indirectWalk (Auto.lean) are allocator-shaped; M10 generalizes them to a contract registry. Providers (Active/Live) are stated generically over tags/blocks (no allocator-specific provider kinds).

## Rows

<a id="row-case-family-enrollment"></a>
### #case-family-enrollment Remove transitional golden case-family enrollment markers

Status: **open**. Requester: Task23; coordinator decision 6258258831.

Progress: Enroll complete golden families through existing retranslation cases; Threadsync and Sync use no per-case selector.

Request: Every supported golden family becomes an unconditional case family, built side by side with disjoint generated APIs.

Workaround sites: `examples/threadsync/all-cases`, `examples/sync/all-cases`

Deletion plan: When the last golden family is enrolled, remove every all-cases marker and the marker/history ratchet, derive all case families unconditionally from the full golden enumeration, and retire when_defined/if_decl with their remaining users. Preserve complete output/import coverage and exact retranslation checks.

<a id="row-1"></a>
### #1 Replace unsafe evalPlanner (implemented_by) by a declared planner table

Status: **closed**. Requester: coordinator (kernel-escape check).

Progress: READY #199 (d8c670b0)

Request: Replace unsafe evalPlanner (implemented_by) by a declared planner table

<a id="row-2"></a>
### #2 fsym [h]: elaborate rule terms in the main goal context

Status: **closed**. Requester: coordinator for D2/allocator.

Note: merged with PR #289 (fsym-perf)

Progress: READY-PENDING codex/fsym-perf d65219fbd (evalFsym withMainContext)

Request: `fsym [h]`: elaborate rule terms in the main goal context (local `have`s)

<a id="row-3"></a>
### #3 ruleConcl? recognize generic FLogic.T L … rules (FAllocSpec generic in partial/total)

Status: **open**. Requester: coordinator for D2/allocator.

Progress: open

Request: ruleConcl? recognize generic `FLogic.T L …` rules (FAllocSpec generic in partial/total)

<a id="row-4"></a>
### #4 unifyKeyed: proof irrelevance and reducible types

Status: **closed**. Requester: one-logic-tactics.

Note: merged with PR #303

Progress: open

Request: unifyKeyed: Prop-typed args by proof irrelevance; unfold reducible types (MM σ vs StateT σ MemM)

<a id="row-5"></a>
### #5 intCast step rule (a.toNat < 2^n → r.toNat = a.toNat)

Status: **closed**. Requester: one-logic-tactics (Lists.sum).

Progress: DONE by one-logic-tactics PR2 (`@[fsym] intCast_step` added to AutoRules.lean after `divTrunc_step`; heads-up for merges)

Request: intCast step rule (`a.toNat < 2^n → r.toNat = a.toNat`)

<a id="row-6"></a>
### #6 fsym_arith: toNat / width-change normal forms

Status: **closed**. Requester: one-logic-tactics.

Progress: READY #237 (arith lane, cd5d17f1): both pass; AutoArith.lean normal forms, intCast_step for every signedness

Request: fsym_arith: `(a-b).toNat = a.toNat-b.toNat` given b ≤ a now PASSES (2026-10-12). Still fails: `(x.setWidth 64).toNat = x.toNat` (x : BitVec 32, widening); `a.toInt = (a.toNat : Int)` given `a.toNat < 100` (a : BitVec 16)

<a id="row-7"></a>
### #7 document/plan rule preconditions ⟪φ⟫ from context facts

Status: **open**. Requester: one-logic-tactics.

Progress: open

Request: document/plan rule preconditions ⟪φ⟫ from context facts

<a id="row-8"></a>
### #8 TLogic record so fsym drives FTTriple/FTTotalTriple (no FTotalTriple rules in TLogic goals)

Status: **closed**. Requester: one-logic-csl.

Note: row status was not updated: the TLogic record and the thread backend landed with PR #289

Progress: open

Request: TLogic record so fsym drives FTTriple/FTTotalTriple (no FTotalTriple rules in TLogic goals)

<a id="row-9"></a>
### #9 engine support replacing arena_* macros, within (planner rule), unroll_solo (CTriple-backend rule)

Status: **open**. Requester: arena lane.

Note: umbrella of 9a-9h; closes with 9h

Progress: open

Request: engine support replacing arena_* macros, `within` (planner rule), `unroll_solo` (CTriple-backend rule)

<a id="row-9a"></a>
### #9a Provider backtracking on arithmetic failure

Status: **closed**. Requester: arena lane.

Progress: READY #239

Request: (detail of #9, measured 2026-10-12 by arena lane: plain `fsym` on arena `free` (ArenaLinux, CTriple) gets through the prefix, loadFirstNode and the end_index load in 50 s.) Provider backtracking on ARITHMETIC failure: at `ptrProject (x.add 24) (elem 1 ei)` fsym takes `Reaches` from `apts (x.add 8)` (K = off+16) and leaves the false side goals `(x.add 24).off ≤ (x.add 8).off+8` to the caller; `Reaches.region` of `up (regionIn (x.add (24+ei)) … tail)` (fact tail.size = sz-24-ei) proves them. Try the next provider when the side goals fail

<a id="row-9b"></a>
### #9b Pair facts of atoms

Status: **closed**. Requester: arena lane.

Progress: open

Request: Pair facts of atoms: `gauthP γ e M p ⋆ gfrag γ e i g ⇒ M i = some g` (library `gfrag_mem`, Ghost.lean) as a fact source (`@[fsym_facts]` over two atoms, or a `pre_fact` hook taking a lemma `Holds m r rF → (X ⋆ Y ⋆ R) r → φ`). Arena `free`: the `loadFirstNode = none` panic is unreachable only via `M i = some g` and `w.first = none → M = empty`

<a id="row-9c"></a>
### #9c Bool facts to constructor equations

Status: **closed**. Requester: arena lane.

Progress: open

Request: Bool facts to constructor equations: `¬ o.isSome = true` / `o.isSome = true` should substitute `o = none` / `o = some _` (substCtor), so a precondition `match w.first with …` reduces (arena free, `inr` branch)

<a id="row-9d"></a>
### #9d ptrEqAddr p q into possibly different blocks (O-F

Status: **closed**. Requester: arena lane.

Progress: READY #239 (engine wrote ptrEqAddr_live)

Request: `ptrEqAddr p q` into possibly different blocks (O-F: arena free/resize compare `buf_ptr + end_index` with `memory.ptr + memory.len`): result `decide (b = b' ∧ p.off = q.off)` when both blocks are LIVE and `0 < p.off ≤ size_b`, `0 < q.off ≤ size_b'` (`Mem.LiveDisjoint.addr_ne`). Needs a liveness provider: a tagged `bshare … t` is live while `t` is active (`Holds.bshare` + `Act`; arena shares are tagged `CI.tag`/`(γ,e)`, activity from `gauthP`/`CI.act_within`). Arena lane writes the library rule (Ops, `FTotalTriple.ptrEqAddr_live`) once the engine has a provider kind for it — say which shape (`Live b K X`, or `Reaches` with an `Act` side goal)

<a id="row-9e"></a>
### #9e Memory use of plain fsym on arena resize

Status: **closed**. Requester: arena lane.

Progress: open

Request: Memory: plain `fsym` on arena `resize` (refined contract, CTriple) hits the 10 GB RSS guard after 75 s with no result. Likely the undecided ptrEqAddr (9d) plus the `relBytes` `if`, both walked with full contexts. Repro: a file in tests/roadmap/alloc-arena importing AllocArena.ArenaLinux, AllocArena.Core, ZigLean.Sep.Full.AutoConc, AutoClaims with Core's `resize_ct` statement and body `fsym`

<a id="row-9f"></a>
### #9f Returns closed by module EUpd lemmas (free_last_upd, free_other_upd, resize_shrink_upd, resize_grow_upd, re...

Status: **closed**. Requester: arena lane.

Progress: READY #260

Request: Returns closed by module `EUpd` lemmas (`free_last_upd`, `free_other_upd`, `resize_shrink_upd`, `resize_grow_upd`, `resize_other_upd`, Core.lean): accept an `EUpd P Q` lemma in `fsym [u]` as a planner step (applied when its `P` frames out of the state and `Q` matches the post), so the entries become `fsym [loadBuf_ct, free_last_upd, …]` with no hand steps

<a id="row-9g"></a>
### #9g within goals as planner goals (fsym_entail)

Status: **closed**. Requester: arena lane.

Progress: READY #239 (fsym_entail on Within)

Request: `within` → planner: a `Within X P` goal is `fsym_entail`'s `EUpd P (X ⋆ ?R)` without the update (accept `Within` as a goal kind); then delete the `within` macro (Extent.lean:727)

<a id="row-9h"></a>
### #9h unroll_solo: concrete counterexample runs

Status: **open**. Requester: arena lane.

Progress: open

Request: `unroll_solo` (Unroll.lean:56; users ArenaObstruction.lean:162, tests/roadmap/proof-tools/Unroll.lean): concrete counterexample runs, not program proofs. Proposal: a term-level use of `Unroll.expand` + `Sched.soloRun_apply_le` + `decide`, or a CTriple-backend mode; engine lane decides

<a id="row-10"></a>
### #10 Full/Arr rules (arr_load/store/ptrProject, facts_arr, split/join)

Status: **closed**. Requester: one-logic-tactics.

Note: library change (Full/Arr), not an engine feature

Progress: not engine (library Full/Arr); note only

Request: Full/Arr rules (arr_load/store/ptrProject, facts_arr, split/join)

<a id="row-11"></a>
### #11 CTriple backend on top of FTTriple (T-ctriple

Status: **closed**. Requester: coordinator / CSL.

Note: row status was not updated: the CTriple backend over thread rules landed with CSL S4 (PR #299/#304)

Progress: open (after #1); exact request below (2026-10-12, approved design R2, docs/sep-threads.md §T-ctriple)

Request: CTriple backend on top of FTTriple (T-ctriple; CSL lane puts exact request here) — with #8

<a id="row-12"></a>
### #12 Precondition planning: region atoms before size-dependent atoms

Status: **closed**. Requester: coordinator for allocator lane.

Progress: READY #250

Request: precondition planning: plan region atoms before size-dependent atoms (`I.tok p ?bs.size` fixes ?bs to stale bytes after @memset) or re-unify after updates

<a id="row-13"></a>
### #13 optPayload

Status: **open**. Requester: one-logic-tactics (Lists.sum).

Progress: open

Request: optPayload: after `optPayload_step` the fact `s.p = some x` plus precondition fact `s.p = some p` give `some x = some p`, which is not injected/substituted; a later `ptrProject x (·.add 8)` then finds no provider (facts are about `p`). Workaround: state the step on locals `⟨t, some p⟩`. Request: Option.some injectivity (`some a = some b → a = b`, subst) in fact normalisation

<a id="row-14"></a>
### #14 One fsym entry for other front ends

Status: **closed**. Requester: one-logic-vc.

Note: ZigLean/VC/Extract.lean now calls Auto.run; tests/roadmap/sep-auto/SepAuto/Report.lean checks ordinary/reporting proof and residual identity

Progress: Auto.run is the shared entry for evalFsym and memVc, including introductions, context preparation, run caches and the orphan-proof check; runReport adds residual attribution to that entry

Request: One fsym entry for other front ends: expose `Zig.Full.Auto.run (g) (user : Array Expr) (extra : Array Syntax) : TacticM (List MVarId)` = what `evalFsym` does after elaborating its args (intros, `reduceProjs` of hyps, `withRunCaches`, `arithSimpCtx`, `walk … 400`); `evalFsym` calls it. `vc_gen` (ZigLean/VC/Extract.lean `memVc`) then calls it instead of re-doing `withRunCaches`/`arithSimpCtx`/`walk` and missing intros/reduceProjs

<a id="row-15"></a>
### #15 Quiet stop

Status: **closed**. Requester: one-logic-vc.

Progress: fsym.quiet suppresses the human stop messages; memVc enables it only around Auto.run, so vc_gen refuses an unexecuted command with its own error and no duplicate fsym info (pinned by vcs/Memory.lean). Auto.runReport returns stop reasons without emitting a report message, and fsym.report emits schema-versioned JSON

Request: Quiet stop: at "no rule for the command" the walk `logInfo`s and returns the `FLogic.T` goal; `vc_gen` detects that goal and refuses with its own error, so the info is duplicated (pinned in tests/roadmap/vcs/Memory.lean). A flag or a returned stop reason

<a id="row-16"></a>
### #16 Keep path conditions

Status: **open**. Requester: one-logic-vc.

Progress: open

Request: (nice) Keep path conditions: an `if b` on a `Bool` variable is split and `destruct` substitutes `b`, so a VC under it (reachable panic `⊢ False`) shows no `b = true`

<a id="row-17"></a>
### #17 An undecided side condition φ is split by byCases

Status: **open**. Requester: one-logic-vc.

Progress: open

Request: (nice) An undecided side condition `φ` is split by `byCases`; the negative case leaves `hc : ¬φ ⊢ φ` (vc_gen clears `hc`, equivalent). A mode that leaves `φ` unsplit gives one obligation and one walk

<a id="row-18"></a>
### #18 Binder names

Status: **open**. Requester: one-logic-vc.

Progress: open

Request: (nice) Binder names: command results are `x✝` in residual goals; use the generated local's name (`i2`, …) of the continuation lambda

<a id="row-19"></a>
### #19 (same shape as 9b, second user) Pair facts from the memory

Status: **closed**. Requester: one-logic-alloc (D2).

Progress: open

Request: (same shape as 9b, second user) Pair facts from the memory: allocator lane (D2) supplies `MemFacts (X ⋆ Y) φ` (`MemFacts P φ := ∀ m r rF, Holds m r rF → P r → m.FSeq → φ`) in `ZigLean/Sep/Full/Region.lean`: `MemFacts.regions_apart`: two separately owned nonempty `up (regionIn …)` lie at disjoint address ranges (`A+p.off+ | bs | ≤ A'+q.off ∨ …`, same block by separation, different blocks by `Holds.apart`). Needed for the `@memcpy` aliasing check `ptrLe(src+n,dst) or ptrLe(dst+n,src)` in the generated `dupe` and `realloc` wrappers. Engine: `addFacts` also tries ordered pairs of distinct atoms against `@[fsym_facts]` `MemFacts (X ⋆ Y) φ` lemmas, applied via the backend's `pre_mfact` (FTotalTriple/FTriple/CTriple: `EUpd (X⋆Y⋆R) (⟪φ⟫⋆X⋆Y⋆R)` then `eupd`). One mechanism for 9b and 19

<a id="row-20"></a>
### #20 Split a match on a symbolic Except result

Status: **closed**. Requester: alloc-param (lists push).

Progress: DONE codex/fsym-wp (agent 13: a body's match on a variable as the command is split)

Request: split `match x with | .error _ => … | .ok v => …` on a symbolic `Except` result (after a callee rule; pre has the matching `match x`); today manual `cases x <;> fsym`

<a id="row-20a"></a>
### #20a Atoms equal up to arithmetic

Status: **closed**. Requester: one-logic-alloc (D2).

Note: the handoff numbered two rows #20 (this one in the first table, the Except match in the alloc-param table); this one is 20a

Progress: READY #250 (allocSentinel + realloc drafts close)

Request: **Atoms equal up to arithmetic** (return/planner matching): a state atom `up (regionIn p A S K a B)` with `B = writeBytes (Array.replicate x.toNat .undef) (1 * ↑n.toNat).toNat (Enc.encode 7#8)` (x opaque, fact `x.toNat = n.toNat + 1`) must match the postcondition's `up (regionIn p A S K a (writeBytes (Array.replicate (n.toNat + 1) .undef) n.toNat (Enc.encode 7#8)))`. Today `unifyAtom` fails and the return is left open. Request: when two atoms have the same head and differ only in subterms, accept them with side goals of the differing first-order arguments (`congr` decomposition down to Nat/Int/BitVec equalities) solved by `arith`; same for a fact goal `t = t'` of a non-arithmetic type. Users: the generated `allocSentinel` wrapper (D2; byte array sized by the checked `n + 1`), `realloc` (copy of `min(old,new)` bytes). Repro: `tests/roadmap/alloc-fba/AllocFba/Wrappers.lean` `allocSentinel_spec` on branch codex/one-logic-alloc-w4 Second shape, same mechanism: a hypothesis `hfit : I.fits (n.toNat + 1) 0` must prove the side goal `I.fits x.toNat 0` (fact `x.toNat = n.toNat + (1#64).toNat`): an assumption up to arithmetic in its arguments

<a id="row-21"></a>
### #21 fsym_arith: disjunctive goals, user Nat functions on constructors, constructor injectivity

Status: **open**. Requester: one-logic-tactics (dispatch, PR #222).

Progress: open

Request: fsym_arith: (a) disjunctive goals are not proved (`n < n ∨ 1 < 2`, `m ≤ n → m < n ∨ m = n ∧ 1 < 2`): `omega` handles them, the pipeline does not; (b) a user Nat function on a constructor (`rank Phase.count`, a `match` on a constructor) is not evaluated unless tagged `attribute [local fsym_arith] rank`; (c) `machExit.ret acc = machExit.ret N` with `acc = N` in context is not closed (constructor injectivity in the return entailment; same family as #13). Workarounds in PR #222: `loop_dispatch` takes the measure `B * data + rank` (no Prod.Lex disjunction), local fsym_arith tags, unfold the invariant before `cases`

Workaround sites: `tests/roadmap/dispatch-templates/Template.lean`, `tests/roadmap/dispatch-templates/TokenizerProof.lean`

Deletion plan: delete the local `attribute [local fsym_arith] rank` lines once fsym evaluates a user Nat function on a constructor (evalUserCtor covers non-Nat results only); run the two fixtures without them.

<a id="row-21a"></a>
### #21a a pure generated helper with literal args (mem_Alignment_fromByteUnits 8) is unfolded and sticks at enumOf...

Status: **open**. Requester: alloc-param (lists destroy).

Note: the handoff numbered two rows #21 (fsym_arith in the first table, this one in the alloc-param table); this one is 21a

Progress: open

Request: a pure generated helper with literal args (`mem_Alignment_fromByteUnits 8`) is unfolded and sticks at `enumOf (E.ofInt? (val false x))` with x opaque (fact `x.toNat = 3`); either evaluate pure helpers on literals, or use the `x.toNat` fact to reduce `val false x`; also: a user step rule `FTotalTriple P (StateT.lift (f 8)) …` logs "command unified" but is not applied

Workaround sites: `Proofs/Lists/Append.lean`, `Proofs/Lists/Alloc.lean`, `tests/roadmap/interfaces/Interfaces/SentinelSpec.lean`

Deletion plan: delete the manual evaluation of the pure helper on its literal once fsym evaluates pure generated helpers on literals (or uses the x.toNat fact).

<a id="row-22"></a>
### #22 fold the open arm of an indirect call

Status: **closed**. Requester: alloc-param (mixed closure/env dispatch).

Progress: DONE in alloc-param PR (a) (M10 library part, 2026-10-12; small Auto/AutoConc edits, heads-up for merges): `callIndirect f arms d` takes the last arm `d` (no MonadExceptOf; args α m f arms d, so indirectWalk reads a[2..4]); `callIndirect_fold_ext` registered in foldCtx; `C.callIndirect_pos/_neg` take implicit `d`, `C.callIndirect_nil f d : callIndirect f [] d = d`; `pullIndirect` pulls `g` from `d >>= g` or keeps `throw e`

Request: fold the open arm of an indirect call

<a id="row-23"></a>
### #23 CTriple rule commands over interface tables

Status: **closed**. Requester: alloc-param.

Progress: DONE in alloc-param PR (a): `reduceProjs` after `unfoldToHead` (tryRule, CTriple branch)

Request: CTriple rule commands over interface tables: `(CVTable.env (env e) fns).alloc ctx ?n ?k ?ra` unfolds to `extCall ((env e).alloc f (ctx, ?n, …))`; isDefEq against `Ext.call0 f ctx 16#64 …` assigned `?n` the WHNF of the literal (`{toFin := Fin.Internal.ofNat …}`), which arith cannot read

<a id="row-23b"></a>
### #23b row 23 for a table WITH closure arms (CVTable.dispatch (tables e) fns)

Status: **closed**. Requester: alloc-param (Mix create/make).

Progress: DONE on codex/iface-contracts (PR (b)): `expandMapLits` (List.map over a literal expanded, beta-reduced) between two `reduceProjs` in tryRule's CTriple branch. ACCEPTED by the coordinator 2026-10-13 as an engine edit made outside the engine lane: engine lane, review/own it (Auto.lean `expandMapLits`, `unfoldToHead` headBeta first) and fold it into the general rule-matching normalization when convenient

Request: row 23 for a table WITH closure arms (`CVTable.dispatch (tables e) fns`): `Table.callOr`'s arms `t.map fun g => (g.1, g.2 (ctx, ?n, …))` stayed a `List.map`/beta-redex, so isDefEq met `(ctx, ?n, …).2.1 =?= 4#64` and assigned `?n` the literal's WHNF

<a id="row-24"></a>
### #24 raw Nat literal from unification (BitVec.ofNat 6 ?k =?= 3 assigns raw 3)

Status: **closed**. Requester: alloc-param.

Progress: DONE in alloc-param PR (a): `normNatLits` on P₀i/P₀/Q₀ in tryRule

Request: raw Nat literal from unification (`BitVec.ofNat 6 ?k =?= 3` assigns raw `3`): `2 ^ ?k` in the rule's precondition no longer matched the state's `2 ^ 3` ("no region of the state holds")

<a id="row-25"></a>
### #25 @[fsym] regionStore0/regionLoadWritten0 (Full/Region, alloc-param WIP) broke sep-auto Region.sentinelAt_tot...

Status: **closed**. Requester: alloc-param.

Progress: attribute removed (ListsSpec: `attribute [local fsym]`); question for M2: prefer the in-place rule when both apply

Request: `@[fsym] regionStore0`/`regionLoadWritten0` (Full/Region, alloc-param WIP) broke sep-auto Region.sentinelAt_total (a carve instead of regionStoreAdd's in-place update)

<a id="row-26"></a>
### #26 Side goal from an equal hypothesis up to projection and proof irrelevance

Status: **open**. Requester: mig-tests.

Note: agent 3 reported the arith side-goal part handled by PR #250; the workaround is still in the tree

Progress: open

Request: (was the mig-tests "#21" row below the NEXT list; renumbered, the ledger already had #21) Side goal not closed from an equal hypothesis up to structure projection + proof irrelevance: goal `{ names := #["Bad","Other"], unique := TryPointers.cleanup._proof_1, .. }.names.contains e = true` (domain literal of generated code), hypothesis `Option.all domain.names.contains (errTagOf (.error e)) = true` (or `domain.names.contains e = true` with the test's own `domain` abbrev: other aux proofs). fsym leaves it; `exact h` closes it (defeq). Request: reduce `{..}.field` projections of structure instances in fsym_arith/side goals, and try `assumption` up to defeq (default transparency, proof irrelevance) — same family as #4. Workaround: `cases u <;> fsym <;> exact hd` (tests/roadmap/try-pointers/TryPointers/AliasProofs.lean)

Workaround sites: `tests/roadmap/try-pointers/TryPointers/AliasProofs.lean`

Deletion plan: drop `<;> exact hd` from the `cases u <;> fsym` steps; if fsym closes the side goal up to structure projection and proof irrelevance, delete them and close the row.

<a id="row-27"></a>
### #27 Planning a user rule whose precondition holds an if-guarded grant (I.owned 0 s.ptr bs = if bs.size = 0 then...

Status: **open**. Requester: one-logic-alloc.

Progress: open

Request: Planning a user rule whose precondition holds an `if`-guarded grant (`I.owned 0 s.ptr bs` = `if bs.size = 0 then emp else I.granted …`) against the same, already-normalized state: "state if: split on bs.size = 0", then "entailment: the state has no atom for `bshare ?b q (s.ptr.off.toNat + bs.size) I.tag`" → "no plan for its precondition" (the `pshare`'s block `?b` is not fixed by the fact `s.ptr.block = some b` of the opened state). Repro: `fsym [fun ra => reallocAdvanced_spec ctx vtp I s n ra bs hlen hfit hA hM hF]` on `mem_Allocator_reallocAdvanced… >>= pure` with pre `I.own ⋆ (I.owned 0 s.ptr bs ⋆ vtR …)` (tests/roadmap/alloc-fba Wrappers, branch codex/one-logic-alloc-w10). Workaround: realloc_spec walks the inlined reallocAdvanced with the same rules (no composition)

Workaround sites: `tests/roadmap/alloc-fba/AllocFba/Wrappers.lean`

Deletion plan: state realloc_spec through reallocAdvanced_spec once fsym plans an if-guarded grant against the opened state; delete the inlined walk.

<a id="row-28"></a>
### #28 Field access of a generated struct

Status: **closed**. Requester: interface lane.

Progress: open

Request: **Field access of a generated struct.** `std.ArrayListUnmanaged(u32)` code (Proofs/Lists/Open.lean: `array_list_Aligned_u32_null_{addOne,ensureTotalCapacity,ensureTotalCapacityPrecise,addOneAssumeCapacity}`) reads and writes its header both whole (`load array_list_Aligned_u32_null 8 p`, `load Slice 8 p`) and by field (`load (BitVec 64) 8 (p.add 8/16)`, `load debug_SafetyLock 8 (p.add 24)`, `store Ptr 8 p`, `store (BitVec 64) 8 (p.add 8/16)`). Neither representation is walkable: (a) header as one typed value `up (pts p 8 (hdr : array_list_Aligned_u32_null))`: "no rule for the command `load (BitVec 64) 8 (p.add 8)`" (`FTotalTriple.field_load` exists but needs the field value `v` and the decode side condition by hand, so it is not `@[fsym]`); (b) header as field atoms (`pts p 8 (s : Slice) ⋆ pts (p.add 16) 8 cap ⋆ pts (p.add 24) 8 lock`): "no rule for the command `load array_list_Aligned_u32_null 8 p`" (no whole-struct load from adjacent field atoms), and no `@[fsym]` store into a stored slice's `ptr`/`len` (only `load_slice_ptr/len`). Request: one general mechanism for generated structs (any `Enc` instance built by the translator from fields): field loads/stores on `pts q a s` with the value `s.f` / `{ s with f := w }` (needs per-field decode facts: translator-emitted lemmas or a generic theorem over the generated `Enc` shape), or folding/unfolding a struct atom into its field atoms on demand. Repro: ~/.cache/air2lean/scratch-iface/lt/A1.lean (a) and A2.lean (b) on branch codex/lists-alloc-contract. Blocks: Proofs/Lists/Append (append for every allocator), hence Container/container-contracts/tutorials/generic-containers

<a id="row-29"></a>
### #29 a user rule term with an explicit argument that fsym later generalizes fails

Status: **closed**. Requester: interface lane.

Progress: READY-PENDING codex/fsym-perf d65219fbd (refreshUser)

Request: (minor) a user rule term with an explicit argument that fsym later generalizes fails: `fsym [destroy_fields ctx vtp fns I e p z q h]` logs "command unified" then "unknown free variable `_fvar…`" (q is replaced by the loaded value). Workaround: leave the argument to unification (`destroy_fields … (h := h)`). Same family as the stale-local note under 9f

<a id="row-30"></a>
### #30 Views of owned bytes

Status: **closed**. Requester: fold lane.

Progress: READY-PENDING codex/fsym-views da5df40ec: `@[fsym_view]` registry (unfold at stuck steps, fold back at returns; `regionIn_view`/`regionIn_fold` registered; per-view rule deletion left to the fold lane)

Request: **Views of owned bytes.** `up (region q a bs)`, `up (regionIn …)`, `up (pts q a v)`, `up (ptsR …)`, `up (arr p vs)` are labels and facts over `up (bytesAt q A S K bs)`, but fsym treats each as its own atom, so every view needs its own `@[fsym]` byte rules (Region regionStore/Add/LoadWritten*, Typed region_store/0, Try region_loadBytes/storeBytes, AutoPrim storeBytes_region, Ops pts load/store, Dispatch ptsR_load, Arr arr_*). Library side done: all of them are now instances of one lemma `FTotalTriple.up_view`/`up_view'` (Full/Ops) over the Ops rules (`load_bytesAt`, `storeBytes_bytesAt`, …). Request: a registry of view equations (e.g. `@[fsym_view] up V ↔ ∃ i, ⟪F i⟫ ⋆ up (bytesAt …)`): unfold a view atom of the precondition when no rule applies to it, run the Ops rule, and fold back at returns in the planner (the post names the view). Then the per-view @[fsym] rules become thin corollaries only where callers name them, or go

<a id="row-31"></a>
### #31 G1: typed load from a region whose bytes are a value's encoding

Status: **closed**. Requester: arena (deinit/reset, countListCapacity).

Progress: READY-PENDING codex/fsym-views (load_reads for every load, `ReadsAt.regionInEnc`)

Request: **G1: typed load from a region whose bytes are a value's encoding.** `load (Option Ptr) 8 (N.add 16)` with `up (regionIn (N.add 16) A S K 8 (Enc.encode nxt))` in the state: "no rule". The region rules want `writeBytes bs o (Enc.encode v)`; `FTotalTriple.load_reads` (+ `ReadsAt.regionInAll`, `Enc.decode (encode v) = pure v`) would do it but is only tried for struct loads (`RunCaches.structs`). Either try `load_reads` for every load whose precondition has a `ReadsAt` provider, or an `@[fsym]` `regionLoadEnc` (scratch: from `regionLoadWritten0` + `writeBytes bs 0 bs = bs`).

<a id="row-32"></a>
### #32 G2: atomic words as plain bytes in a planned region

Status: **closed**. Requester: arena.

Progress: READY-PENDING codex/fsym-views (`apts_view`/`aptsE_view`, joinOnce relabel, size from the token) — repro D2 closes with `fsym [CAllocSpec.free h, toInt_step, cown_refund]`

Request: **G2: atomic words as plain bytes in a planned region.** The child's `free` takes `I.granted N 3 φ bs` = `up (regionIn N ?A ?S ?K 8 ?bs) ⋆ tok ⋆ pshare ⋆ pclaim`; the node holds `apts N sz ⋆ apts (N.add 8) ei ⋆ up (regionIn (N.add 16) A S K 8 …) ⋆ up (regionIn (N.add 24) A S K 1 buf)`. Planner: "no region of the state holds up (regionIn N …)". Needed: view `apts p v`/`aptsE p v` ⊢ `∃ A S K bs, ⟪(A + p.off) % 8 = 0 ∧ bs.size = 8 ∧ intOfBytes 64 bs = pure v⟫ ⋆ up (regionIn p A S K 8 bs)` (one-way: `up` does not assert the tag; `abytesAt_bytesAt`), then the labels from the adjacent region (`facts_regions_labels`-like MemFacts for apts × region: same block ⇒ same A, K.norm; `EUpd.relabel` for S/K) and the join (`up_region_join`). Instance of #30 (view registry) with a one-way view, or a `@[fsym_plan]` law. Same need in reset's retaining modes (kept node's header).

<a id="row-33"></a>
### #33 G3: update over two atoms of one head with unknown fractions

Status: **closed**. Requester: arena (deinit; reset's child alloc pays half the reservoir).

Progress: READY-PENDING codex/fsym-views (preassign: one Q atom per state atom)

Request: **G3: update over two atoms of one head with unknown fractions.** At the loop body's return the state has `CI.fee φ ⋆ CI.fee φc` (refund + reservoir, facts `0 < φ`, `0 < φc` in context) and Q wants `∃ χ, ⟪0 < χ⟫ ⋆ CI.fee χ`. User update `cown_refund : EUpd ((⟪0<u⟫ ⋆ CI.fee u) ⋆ (⟪0<v⟫ ⋆ CI.fee v)) (∃ χ, ⟪0<χ⟫ ⋆ CI.fee χ)` (`fsym [cown_refund]`): "the state has no atom for CI.fee φ … update cown_refund: no plan for its precondition" (both `?u`, `?v` seem to go to the same atom). Same with explicit hypotheses `0 < u`, `0 < v`.

<a id="row-34"></a>
### #34 (perf) normPre's refine C.ex_sep _ fun x => ?_ / C.lift_sep whnf's the whole program

Status: **closed**. Requester: interface lane (Proofs/Lists/Append `ensureTotalCapacityPrecise`).

Progress: READY-PENDING codex/fsym-perf d65219fbd (normPre by mkAppM; exCont)

Request: **(perf) `normPre`'s `refine C.ex_sep _ fun x => ?_` / `C.lift_sep` whnf's the whole program.** After `casesWalk` splits a result `x : Option Slice` (the post of a callee rule mentions `x`; program `if x.isSome = true then …`), the `none` goal's program starts with `if none.isSome = true then … else …`. Each `refine` in `normPre` (elabAppArgs of `Auto.C.ex_sep`/`lift_sep`, `Tgt` as `_`) whnf's the expected type `CTriple P prog Q` → `FTriple … (soloRun n prog)` → `match` on the program and evaluates it symbolically (`none.isSome` decides, then the callee bodies down to `math_mul`'s `BitVec.umulOverflow` by `Nat.rec`): ~24 s per `refine`, 8 of them (the opened grant's `A S K q` and facts) = 6M heartbeats in one `pre` step (`trace.profiler`: `Non-easy whnf: match … Sched.soloTree … if none.isSome`). Fix: build `ex_sep`/`lift_sep` with `mkAppOptM` (no elaboration against the expected type), or simplify the program (`simpProg`) before `normPre` after a split. Repro: `fsym-engine-scratch/lists-append/R34_precise.lean` (`precise_spec`, 200 s with 30M heartbeats; the `fsym` total is 6.0M of which 5.97M is this step).

<a id="row-35"></a>
### #35 Except match inside StateT.run (as 20)

Status: **closed**. Requester: interface lane (Append).

Progress: DONE codex/fsym-wp (as #20)

Request: (#20 again) `match x with | .error | .ok` on a symbolic `Except` inside `StateT.run (match x with …) default` (a generated body after a callee rule, `alignedAlloc` in `ensureTotalCapacityPrecise`): "no rule for the command `StateT.run (match x with …)`"; workaround `all_goals (cases x <;> fsym [..])`.

<a id="row-36"></a>
### #36 Postcondition if whose condition names an existential of the postcondition

Status: **closed**. Requester: interface lane (Append).

Progress: READY-PENDING codex/fsym-perf d65219fbd (branch by branch, imp_ite_pos/neg; ordering gap = #44)

Request: **Postcondition `if` whose condition names an existential of the postcondition.** `closeEntail` decides an assertion-level `ite` of the state (`decideIte`) and splits an undecided `ite` of the postcondition only when its condition has no mvars (`!c.hasExprMVar`). `Lists.Append.alist` = `∃ ptr len cap bs, ⟪…bs.size = 4*cap…⟫ ⋆ hdr ⋆ buf I ptr bs` with `buf := if bs.size = 0 then addrKnown ptr else I.granted ptr 2 bs`: at a return the condition `?bs.size = 0` names the existential, so the goal `EUpd (… regionIn ptr' … bs' …) (… appended … (alist …))` is left (no instantiation of `?bs` before deciding). Needed: decide the `ite` after the existential is instantiated by the atom match (match the `else`/`then` branch's atoms, then prove the condition or its negation by arith), or split the state atoms first. Workaround (in Proofs/Lists/Append.lean): `append_pos`/`append_zero` end in `alistG` (no `if`), `append_spec` joins them by `alist_of_G` and a manual case split on `bs.size = 0`.

<a id="row-37"></a>
### #37 CTriple.loop's step post if again r.1 then inv r.2 else post r is not decided

Status: **closed**. Requester: arena.

Progress: DONE codex/fsym-wp (evalUserCtor; arena loop19_step without Post19 verified)

Request: **`CTriple.loop`'s step post `if again r.1 then inv r.2 else post r` is not decided** when `r.1` is a constructor (`again19 (.rep19, s).fst = true`): the generated `again` is a def by `match` (not reducible), `decideIte` → `arith` fails (closed-term `decide` only without fvars; `isDefEq` reducible). Needed: evaluate such a condition (whnfD/`Meta.reduce` of a match on a constructor to `true`/`false`). Workaround: a step post `Post19 : exit × locals → FAssn` by `match`, converted by `rcases r; cases e <;> exact hr`.

<a id="row-38"></a>
### #38 A precondition ⟪False⟫ from a match that reduces after a case split leaves the goal open

Status: **closed**. Requester: arena.

Progress: DONE on codex/fsym-wp a2b453ecb (walk: a fact `False` after normPre closes the step; sep-auto Walk false_pre). Arena: drop `all_goals contradiction` after it lands

Request: **A precondition `⟪False⟫` from a match that reduces after a case split leaves the goal open** (`Chain CI true [] (some p)`): goals with `h : False` in context are returned. Workaround `all_goals contradiction`.

<a id="row-39"></a>
### #39 substCtor on a projection of a result

Status: **closed**. Requester: arena.

Progress: DONE codex/fsym-wp (etaProj, pairs)

Request: **`substCtor` on a projection of a result**: a callee rule's post `⟪r.1 = .br18 ∧ …⟫` leaves `match p.fst with` unreduced. Workaround: posts `⟪r = (.br18, s)⟫` / `∃ s', ⟪r = (.br8, s')⟫` (equation of the variable).

<a id="row-40"></a>
### #40 A match on a generated function of a constructor

Status: **closed**. Requester: arena.

Progress: DONE codex/fsym-wp (evalUserCtor; verified on arena)

Request: **A `match` on a generated function of a constructor** (`match heap_ArenaAllocator_ResetMode.tag .free_all with …`): "no rule". Workaround `fsym [heap_ArenaAllocator_ResetMode.tag.eq_def]`.

<a id="row-41"></a>
### #41 No rule for Zig.vindex

Status: **closed**. Requester: arena.

Progress: DONE on codex/fsym-wp a2b453ecb (`@[fsym] Zig.Full.Auto.vindex_step`, framed over any P; sep-auto Walk vindex_item). Arena: delete Core's vindex_step and the `fsym [.., vindex_step]` mention after it lands (name clash only if both are opened)

Request: **No rule for `Zig.vindex`** (vector item). Workaround `vindex_step` in alloc-arena Core (belongs in AutoPrim: `vindex a i` with `i.toNat < n` returns `a[i.toNat]`).

<a id="row-42"></a>
### #42 store 8 (ctx.add 16) (s : heap_ArenaAllocator_State) misfires next to a region at ctx with a size fact

Status: **closed**. Requester: arena.

Progress: DONE codex/fsym-wp (refutedSide; reset without reset_heads verified)

Request: **`store 8 (ctx.add 16) (s : heap_ArenaAllocator_State)` misfires next to a region at `ctx` with a size fact** (`up (regionIn ctx … 8 CI.bytes)`, `CI.bytes.size = 16` by `fsym_arith`; the words at +16/+24 are `aptsE`): `regionStoreAdd` (a store outside the region) is taken, `fsym` then **splits on its class side condition `LawfulEnc heap_ArenaAllocator_State`** and fails / times out at `whnf`. Without the size fact (sep-auto Parts `reset_state`) or without the region it works. Needed: never split on an instance side goal; reject a region rule whose extent side goal is false. Workaround: rule `reset_heads` proved by `fsym` over the two words only.

<a id="row-43"></a>
### #43 fsym_entail does not unfold the state's definitions

Status: **closed**. Requester: arena.

Progress: DONE codex/fsym-wp (updHeads, fsym_entail unfoldLeaves; reset without local fsym_atom verified)

Request: **`fsym_entail` does not unfold the state's definitions** (`CI.cown` in P vs its unfolded atoms in Q: "no atom for CI.own"); and Q's `own CI γ (e+1) ctx` (∃ `w : OV`, atoms over projections `w.Ac …`) is unfolded instead of closed by the caller's update `own_empty` ("no region holds regionIn ctx (OV.Ac ?w) …"). Workarounds: `own_empty` by hand; `attribute [local fsym_atom] own`.

<a id="row-44"></a>
### #44 #36's if decided before the atoms that fix the existential

Status: **closed**. Requester: iface.

Progress: DONE codex/fsym-wp (repro-alist-if green)

Request: **#36's `if` on an existential is decided before the atoms that determine the existential.** Q = `alist I p (xs ++ [v])` = `∃ ptr len cap, ⟪…⟫ ⋆ (up (pts p 8 (hdrVal ptr len cap)) ⋆ (if cap.toNat = 0 then addrKnown ptr else ∃ bs, … ⋆ I.granted ptr 2 bs))`; the state holds `up (pts p 8 {…, capacity := addSat false c g})`. The planner assigns `?cap` to the *old* capacity (a fact of the context) while deciding the `if`, then fails: "no atom for `up (pts p 8 (hdrVal ?ptr ?len c))`". Needed: plan the atoms that bind an `if`'s existentials (here `pts`) before deciding the `if`.

<a id="row-45"></a>
### #45 An existential fixed only by a size fact is not assigned

Status: **closed**. Requester: iface.

Progress: not needed (#44)

Request: **An existential fixed only by a size fact is not assigned** (`buf` keyed by `bs`: Q `∃ bs, ⟪bs.size = 4 * cap.toNat⟫ ⋆ (if bs.size = 0 then addrKnown ptr else …)` with `cap.toNat = 0`): "undetermined witness". Needed: assign `#[]` for `bs.size = 0` (or report it so a caller update can). Avoided by #44's representation once #44 is fixed.

<a id="row-46"></a>
### #46 Heartbeats (gate assurance/heartbeat-budgets.json, measured with fsym-perf)

Status: **closed**. Requester: iface.

Progress: DONE codex/fsym-wp (append_pos 855k → 49k, precise_pos 175k → 39k)

Request: **Heartbeats (gate `assurance/perf-budgets.json` section `heartbeats`, measured with fsym-perf):** `append_pos` 861k, `append_zero` 794k, `precise_pos` 284k (default budget 200k); every other list proof fits the default. `append_*` are dominated by the `precise_*` callee rule application and the `cases x <;> fsym` re-walks of #20/#35.

<a id="row-47"></a>
### #47 (was agent 9's "#37", a number collision with the arena row #37) solveBlock of a pointer value

Status: **closed**. Requester: engine / CSL.

Progress: READY-PENDING codex/fsym-perf d65219fbd

Request: (was agent 9's "#37", a number collision with the arena row #37) `solveBlock` of a pointer value: `(⟨some b, o⟩ : Ptr).block = some ?b` (also through `Ptr.add`) by evaluation; lets CSL delete `ThreadLocal.mremapShrink_at` (Full/Mmap.lean)

<a id="row-48"></a>
### #48 fsym_entail: bytes → region

Status: **closed**. Requester: lists (witness).

Progress: DONE codex/fsym-wp (viewAtoms + stateFacts in fsym_entail; bytesAt bound lemma is the witness lane's)

Request: **`fsym_entail`: bytes → region.** Plan `up (regionIn …)` from `up (bytesAt …)` (a view: register `@[fsym_view]` bytes→region and let the planner use it, #30 registry). Repro: codex/lists-fba-witness tests/roadmap/lists-fba/ListsFba/Witness.lean (hand library steps)

<a id="row-49"></a>
### #49 fsym_entail: extent lending off the authority

Status: **closed**. Requester: lists (witness).

Progress: DONE codex/fsym-wp

Request: **`fsym_entail`: extent lending off the authority** (a share/extent lent from `bauth`-like authority in an entailment, not only at rule preconditions); same repro

<a id="row-50"></a>
### #50 fsym_entail: p.add 0

Status: **closed**. Requester: lists (witness).

Progress: DONE codex/fsym-wp (by unification)

Request: **`fsym_entail`: `p.add 0`** not normalized to `p` in atoms/planning; same repro

<a id="row-51"></a>
### #51 WP: rules about CM steps vs the normal form

Status: **closed**. Requester: engine (Counter).

Progress: open

Request: **WP: rules about CM steps vs the normal form.** fsym_norm (AutoConc CNorm.run_callC/MC/RC/liftR, `liftM` unfold + StateT.run_lift) turns `(callMC x).run s`/`(liftM x).run s` into `ConcM.liftMem x >>= fun a => pure (a, s)` before the WP walk sees it, so rules stated on CM steps (Lemmas WP.callC/callRC/callMC_*/liftM, AutoWP WP.liftM_fowned(T)/callMC_fowned(T), client wp_io/wp_cnt) never apply. Erasing the step lemmas in wpCtx did not keep `liftM` (reducible: run_lift/run_monadLift still match; tried, reverted). Decide ONE form: (a) state WP rules on `ConcM.liftMem x` (library: WP.liftMem_fowned/_liftR/_pure exist; delete the CM-form duplicates in AutoWP; clients restate), or (b) an adapter applying a CM-step rule to its normal form (needs WP bind/pure inversion lemmas, not in Conc/Logic). Recommend (a).

<a id="row-51b"></a>
### #51b Status of the WIP after the Counter run

Status: **closed**. Requester: engine.

Note: status line of the Counter run, kept for the record

Progress: —

Request: (status of the WIP after the Counter run) gate w3 GREEN on 091c8b898 (full, 4 suites, others, thread-locals, spawn-failure); then a2b453ecb (+#38, #41, Walk tests; sep-auto green; full gate not re-run)

<a id="row-52"></a>
### #52 WP: ghost choices in protocol rules

Status: **closed**. Requester: engine (Counter).

Note: by design: the client supplies the ghost transition; note only

Progress: note

Request: **WP: ghost choices in protocol rules.** `wp_cnt`'s `p₁` (the thread's next place) and its `hR`/`hsh` (counter value at p₁) are not fixed by unification; the caller passes `wp_cnt (p₁ := …)` with `hR`/`hsh` lemma terms. By design (the client supplies the ghost transition); note only

<a id="row-53"></a>
### #53 (perf) arith proves a conjunction hypothesis of an update by one omega over every fact

Status: **closed**. Requester: arena.

Progress: DONE codex/fsym-wp (1.07M → 245k)

Request: **(perf) `arith` proves a conjunction hypothesis of an update by one `omega` over every fact.** Arena `free_ct` (`fsym [toInt_step, free_other_upd, free_last_upd]`, codex/arena-reset after merging arena-free-fsym): the updates' `hv : FV.Facts ctx s` (a conjunction whose parts are facts in context: `w.Facts`, block equations, `M i = some …`) costs 344k + 78k heartbeats of `omegaT`, with ~15 pairwise disjointness disjunctions of the node's atoms (`bs.size = 0 ∨ … ∨ …`) in the fact set; `x = BitVec.ofNat 64 (w.ei - s.len.toNat)` another 208k. Total ~1.07M (default budget 200k; the same on a830e4ee5 with the current library: was 62k when measured on fsym-resize). Needed: close each conjunct by assumption / `fsym_facts` before `omega`, and give `omega` only the facts whose atoms the goal mentions (disjunctions of unrelated atoms out). Workaround: `set_option maxHeartbeats 2000000 in` on `free_ct` (Core, named). Repro: scratch arena-reset5/Free1.lean (`trace.fsym.prof`).

<a id="row-54"></a>
### #54 unifyKeyed compares proof arguments by their head

Status: **closed**. Requester: arena.

Progress: DONE codex/fsym-wp (regression Walk loop_rule; arena count_spec verified)

Request: **`unifyKeyed` compares proof arguments by their head.** A sequential rule about a loop (`(Zig.loop body again).run s`, `FTotalTriple`) never unifies with the same loop inside a generated function: `Zig.loop`'s `[MonoBind m]` argument is a proof, `heap_…_countListCapacity._proof_1` in the code and the statement's own instance proof in the rule; different heads, not a value type → `unifyKeyed` returns false (the `CTriple` path uses `isDefEq`, so `deinit`'s `loop9_ct` works). Also: a `have`-introduced local named in `fsym [..]` is an "unknown identifier" (theorem binders work). Needed: treat `Prop`-typed arguments as equal (proof irrelevance) in `unifyKeyed`. Workaround: `count_loop` is generic over the loop's instance (`[hm : MonoBind …]`, `@Zig.loop _ _ _ hm _ …`) and passed as `@count_loop CI free`, so the instance is a rule argument (alloc-arena spec files, named). Repro: scratch arena-reset5/Count2.lean history (count_run with `count_loop CI true`).

<a id="row-55"></a>
### #55 Planning and facts whnf-evaluate concrete byte arrays

Status: **open**. Requester: arena (codex/arena-reset).

Note: a synthetic repro does not reproduce; needs the arena case

Progress: open; a synthetic repro does NOT reproduce (agent 14 /tmp/fsym-eng/f14/E55.lean: store/load next to a region over `Enc.encode (some q)`, 10 s). Needs the arena's own case: scratch arena-reset6/L78.lean loop78_step without the `generalize hbs` (needs that file's Reset defs, not on arena-reset)

Request: **Planning and facts whnf-evaluate concrete byte arrays**: a region over `Enc.encode (some p)` or over a user definition of bytes (`Child.bytes = Enc.fields 16 [...]`) next to other regions: `whnf` timeout (4M heartbeats; `Enc.encode`/`Array.map` unfolded ~4M times) in the pair facts/joins. Needed: keep byte arrays opaque (sizes by `LawfulEnc.size_encode`/`fsym_arith` lemmas, never by evaluation). Workaround (arena `reset`, arena-reset-6, scratch arena-reset6/L78.lean): the struct's child bytes are a variable `cb` with `Enc.decode cb = …` and `cb.size = 16` hypotheses (`Cm`), a node's `next` bytes generalized with a decode fact before `fsym`.

<a id="row-56"></a>
### #56 A match on a loop exit variable under StateT.run is not split

Status: **closed**. Requester: arena.

Progress: DONE by #20/#35 (fsym-wp); regression sep-auto Conc exit_match on codex/fsym-rows e7538f52a. NOTE: the loop rule must be stated at the generated monad (`CM`/`MM`), not `StateT σ MemM` (#4)

Request: **A `match` on a loop exit variable under `StateT.run` is not split**: a `CTriple` loop rule with post `∃ e s', ⟪r = (e, s')⟫ ⋆ P (e, s')` leaves `StateT.run (match e with …) s'` and "no rule" (`casesWalk` fires only when the command itself is a matcher). Needed: split a matcher under `StateT.run`. Workaround: one rule per head value with a constructor exit (`loop78_some`: `⟪r = (.br77 N, s')⟫`, `loop78_none`: `⟪r = (.br68, s')⟫`), the head split before `fsym`.

<a id="row-57"></a>
### #57 Rule order for a store into an owned atomic word

Status: **open**. Requester: arena.

Note: not reproduced on fsym-wp; stays open until the arena lane confirms the workaround is gone

Progress: NOT REPRODUCED on fsym-wp (agent 14 /tmp/fsym-eng/f14/T57.lean: word after/before regions over `Enc.encode`, plain fsym, <1 s); likely fixed by #42 refutedSide. Arena lane: drop the workaround and report

Request: **Rule order for a store into an owned atomic word**: `regionStoreAdd` is planned before `aptsE_store`/`wpts_store`; its planning joins neighbouring regions (one over `Enc.encode none`) and runs into #55's timeout. Needed: try the word rules of an atom that owns the target first (or #55). Workaround: `fsym [@FTotalTriple.aptsE_store, @FTotalTriple.wpts_store, …]`.

<a id="row-58"></a>
### #58 fsym_entail panics

Status: **closed**. Requester: arena.

Progress: open

Request: **`fsym_entail` panics** (`PANIC at Lean.Expr.appFn!`, "Unknown constant `_inhabitedExprDummy`") on `EUpd (wpts N … ⋆ wpts (N+8) … ⋆ up (regionIn (N+16) …) ⋆ up (regionIn (N+24) …) ⋆ CI.tok … ⋆ pshare … ⋆ pclaim …) (∃ bs, ⟪bs.size = sz⟫ ⋆ CI.granted N 3 φ bs)`. Repro: scratch arena-reset6/NF.lean history (`node_granted`). Workaround: the same as a `CTriple` rule proved by `fsym [CAllocSpec.free h]` (`node_free`, Core).

<a id="row-59"></a>
### #59 A rule's precondition fact that is an implication

Status: **open**. Requester: arena.

Note: plain case works; needs the arena loop78 case

Progress: open; the plain case WORKS on fsym-wp (agent 14 /tmp/fsym-eng/f14/T59.lean: the implication from a hypothesis, from the state's fact, or instantiated `none → …`). Needs the arena's loop78 case (locals `s.it` after `modify`) to reproduce

Request: **A rule's precondition fact that is an implication** (`⟪s.it = none → x0 = none⟫`) is never planned ("no plan for its precondition"). Workaround: state the rule from the loop's start state (`loop78_ct`, the fact discharged inside).

<a id="row-60"></a>
### #60 (perf) The child's free of a node inside a large state

Status: **closed**. Requester: arena.

Progress: open

Request: **(perf) The child's `free` of a node inside a large state** costs ~1.1M heartbeats (the planner's entailment and `omega` over ~46 facts with `regions_apart` disjunctions), against ~100k in a small context. Workaround: `node_free` (Core), a rule whose precondition is the node's atoms.

<a id="row-61"></a>
### #61 A rule whose precondition has an if the facts do not decide

Status: **open**. Requester: arena.

Note: plain case works; the arena case REPRODUCED on codex/arena-reset-retain (2026-10-19): `loop66_c0` with the plain refined `resize` under `FitsUpTo` in place of `resize_shrink`/`resize_grow` walks the dispatch arms inline and stops with "no rule for the command ConcM.liftMem (Os.munmap …)" (scratch arena-retain9/exp/E14.lean). Workaround site: the arena's `reset` (`loop66`, ArenaSpec*.lean) resizes a kept node through `CAllocSpec.resize_shrink`/`resize_grow`.

Progress: open; the plain case WORKS on fsym-wp (agent 14 /tmp/fsym-eng/f14/T61.lean: a rule with `if n < len then … else …` in its pre, against the same undecided `if` in the state, framed). Needs the arena's resize (`relBytes`, a `callIndirect` rule) to reproduce

Request: **A rule whose precondition has an `if` the facts do not decide** (`relBytes s.ptr … n len tl`: `if n < len`) is not applied; `fsym` then walks the `callIndirect` arms inline (into the page allocator's `munmap`) and stops with "no rule". Needed: split on the undecided condition, as for side conditions. Workaround: `resize_shrink`/`resize_grow` (Core), the condition a side goal of each.

Workaround sites: `ZigLean/Sep/Full/Dispatch.lean`, `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean`

Deletion plan: delete `CAllocSpec.resize_shrink` and `CAllocSpec.resize_grow` (Dispatch.lean) and pass `CAllocSpec.resize` with `FitsUpTo.fits` in the arena's `loop66` proofs (ArenaSpec*.lean) once a rule whose precondition has an undecided `if` (`relBytes`) is applied with the `if` split as a side condition.

<a id="row-62"></a>
### #62 A struct access over several parts in a thread

Status: **closed**. Requester: arena.

Progress: DONE PR #322 (ownsJoin); the hand lemmas were deleted by PR #350

Request: **A struct access over several parts in a thread** (`CTriple` after S4): the sequential rules `load_reads` / `storeBytes_parts` apply through `FTTotalTriple.ofSeq`, whose `ThreadLocal` side goal needs `OwnsPtr P p n` for the whole struct. `fsym` composes a struct's `ReadsAt` from its parts (Auto.lean) but not its `OwnsPtr`, so the arena struct's 32-byte load (region + two `aptsE`) and the 16-byte store of the list heads fail (`reset(.free_all)` timed out at 2M). Library part DONE on codex/arena-reset: `@[fsym_provider] OwnsPtr.apts`/`OwnsPtr.aptsE` and the plain lemma `OwnsPtr.join` (adjacent ranges), in `Full/AtomicPlain.lean`. WORKAROUND: per spec file `state_load`/`heads_store` (FTTotalTriple.ofSeq (by fsym) (ThreadLocal.load/store (OwnsPtr.join …))), passed to fsym. Engine: compose `OwnsPtr` from the parts as for `ReadsAt` (or `OwnsPtr.join` as a provider with the split at a part's end), then drop the two lemmas.

<a id="row-63"></a>
### #63 planShares' split ignores tags

Status: **closed**. Requester: fba-reset.

Progress: DONE codex/fsym-share-tags: split keyed by (block, tag); regression sep-auto Walk.tags_apart

Request: **planShares' split ignores tags**: "split, per block" groups state shares by block only, so a block carrying an allocator's untagged share and a grant's tagged share (`some (γ,e)`), both wanted with unknown fractions, counts want=2 against one share and halves the first (q becomes q.half; FBA ledger free/resize/alloc posts fail).

<a id="row-64"></a>
### #64 An update at a return against a state with an undecided if

Status: **open**. Requester: fba-reset.

Progress: open

Request: **An update at a return against a state with an undecided `if`** (FBA `resize`: the spec's `relBytes … n len tl` = `if n < len then region ⋆ claim else emp`): the walk keeps the `if` to the return; `closeEntail` splits it, but `tryUpd` plans the update's P₀ in the unsplit state, so an update that applies in one branch (resize of the last grant: the released region joins the tail) applies in neither. Needed: split the state's undecided `if` before trying the caller's updates (each branch with its own update). WORKAROUND: `by_cases hc : n.toNat < s.len.toNat <;> fsym [...]` in tests/roadmap/alloc-fba/AllocFba/Full.lean `fresize_spec` (codex/fba-reset-ledger).

Workaround sites: `tests/roadmap/alloc-fba/AllocFba/Full.lean`, `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean`

Deletion plan: delete the `by_cases hc : n.toNat < s.len.toNat` split in `fresize_spec` and the arena's `rcases Nat.lt_trichotomy n.toNat s.len.toNat` in each `resize_ct` (the latter also needs #return-bool-split) once the walk splits the state's undecided `if` before the caller's updates (replaced by the P09-E5 ghost-update registry).

<a id="row-65"></a>
### #65 An update's Q₀ is compared with library atoms only

Status: **open**. Requester: fba-reset.

Progress: open

Request: **An update's Q₀ is compared with library atoms only**: `tryUpd` does not unfold Q₀'s user definitions, so a Q₀ written with a library definition (`allocPost`, `pshare`, `epFee`) does not close against Qv. WORKAROUND (FBA Full.lean): Q₀ written with explicit library atoms (`bshare`, `epTok ⋆ ⟪0 < φ⟫`, explicit tuples).

Workaround sites: `tests/roadmap/alloc-fba/AllocFba/Full.lean`

Deletion plan: restate Q0 with the library definitions (`allocPost`, `pshare`, `epFee`) once tryUpd unfolds Q0's user definitions; delete the explicit-atom form.

<a id="row-66"></a>
### #66 The planner cannot produce an empty region

Status: **open**. Requester: fba-reset.

Progress: open

Request: **The planner cannot produce an empty region** (a padding of size 0) nor carve a region at its exact start with a different alignment (`2^k ∣ 1`). WORKAROUND (FBA `alloc_upd`): the update takes the whole tail and outputs the grant region and the new tail.

Workaround sites: `tests/roadmap/alloc-fba/AllocFba/Full.lean`

Deletion plan: split `alloc_upd` back into carve and grant once the planner produces an empty region and carves at an exact start with a different alignment.

<a id="row-67"></a>
### #67 updHeads keeps a user head folded only at Qv's top level

Status: **open**. Requester: fba-reset.

Progress: open

Request: **`updHeads` keeps a user head folded only at Qv's top level**: a head nested under another definition (`fbody`) is unfolded. WORKAROUND: FBA `fown` written out (no `fbody`).

Workaround sites: `tests/roadmap/alloc-fba/AllocFba/Full.lean`

Deletion plan: write `fown` with `fbody` once updHeads keeps a nested user head folded.

<a id="row-68"></a>
### #68 WP walk: a side goal whose unknown is fixed by a LATER conjunct is not re-solved

Status: **open**. Requester: L9.

Progress: open

Request: **WP walk: a side goal whose unknown is fixed by a LATER conjunct is not re-solved**: post `∃ k, s.local1.toNat = k ∧ k ≤ 2 ∧ P.inv (upd G t (gOut k)) m` — the walk defers `s.local1.toNat = ?k` / `?k ≤ 2`, `P.inv` fixes `k` by unification, and the deferred goals (`s.local1.toNat = 2` from `¬ lt false a 2 = true`, `0 = 0`, `0 ≤ 2`) are left unsolved although `fsym_arith` proves each in the same context. Needed: retry deferred side goals with the arithmetic solver once their unknowns are assigned. WORKAROUND (deletion plan: reorder back once fixed): Proofs/Sync/Mutex.lean (and Threadsync/Mutex) `workInv`/`workPost` state the conjunct that fixes `k` (`P.inv …`) first. Repro: swap the conjunct order in `Sync.MutexCounter.workInv`.

Workaround sites: `Proofs/Sync/Mutex.lean`, `Proofs/Threadsync/Mutex.lean`

Deletion plan: reorder `workInv` / `workPost` back (the conjunct that fixes k last) once the WP walk retries deferred side goals after their unknowns are assigned.

<a id="row-68d"></a>
### #68d Full/ThreadCall (WP.call_fowned): used by fsym's WP backend

Status: **closed**. Requester: engine.

Note: dead-module row 68 of agent 17; the handoff also numbered the L9 row 68; this one is 68d

Progress: DONE PR2; PR #354 merged

Request: `Full/ThreadCall` (`WP.call_fowned`): USED — fsym's WP backend applies it as a caller rule (`fsym [WP.call_fowned hf …]`); regression sep-auto WP `call_contract` (every protocol meeting hinv/hloc, f known only by CTriple). Next: real client (CAllocSpec entry in a thread protocol)

<a id="row-69"></a>
### #69 WP rules are tried on a command with a different head; the failed unification unfolds both generated functions

Status: **open**. Requester: L9.

Progress: open

Request: **WP rules are tried on a command with a different head; the failed unification unfolds both generated functions**: in `Threadsync.MutexCounter.loop4_body` the rule `ThreadMutex.lock_wp …` (conclusion on `Thread_Mutex_lock p`) is tried on `Thread_Mutex_unlock cPtr` (and other rules on other commands); `isDefEq` unfolds the big generated loops and every rule hits the heartbeat limit (passes only with maxHeartbeats 2M). Needed: key WP rules by the command's head constant / unify generated functions at reducible transparency. WORKAROUND (deletion plan: drop it once keyed): `attribute [local irreducible] Thread_Mutex_lock Thread_Mutex_unlock` in Proofs/Threadsync/Mutex.lean (2.5 s at default heartbeats). Also: the contract form `threadMutex.lock_wp` (`threadMutex.lock p io`) does not match `Thread_Mutex_lock cPtr`, so the walk passes `ThreadMutex.lock_wp`/`unlock_wp` (the instance's proofs on the program's names).

Workaround sites: `Proofs/Threadsync/Mutex.lean`

Deletion plan: drop `attribute [local irreducible] Thread_Mutex_lock Thread_Mutex_unlock` once WP rules are keyed by the command head (or unify generated functions at reducible transparency); then `threadMutex.lock_wp` can be passed directly.

<a id="row-69d"></a>
### #69d Conc/Spec/MutexToy: witness of the legacy MutexSpec

Status: **open**. Requester: sync lane.

Note: dead-module row 69 of agent 17; L9 row 69 keeps 69; this one is 69d

Progress: plan recorded PR2

Request: `Conc/Spec/MutexToy`: witness/counterexample of legacy `MutexSpec` (legacy-to-retire). PLAN: delete together with MutexSpec (docs/proof-framework.md row); restate relaxed-unlock counterexample against MutexImpl if wanted

Deletion plan: delete Conc/Spec/MutexToy together with the legacy MutexSpec (docs/proof-framework.md row); restate the relaxed-unlock counterexample against MutexImpl if wanted.

<a id="row-70"></a>
### #70 Holder field steps as one library rule (coordinator item (a)) not landed yet

Status: **closed**. Requester: L9.

Progress: DONE codex/fsym-wp-hold: the `WP` walk applies `FLock.Fits.wp_hold` itself (`fsym [hF.wp_hold (g' := gH x'), …]`, one term per place the walk reaches): a rule for every `MemM` step is tried after the others and applies only completely; the segment's precondition comes from `hpa`, the side goals from the first one about the segment's post on (`hR`, `hg'`, `hU`) are solved after the segment; `hR` by the post's atoms (`assnByHyp`: equal or provably equal values, AC), `hU` by the protocol's lemma applied backwards (`wpChain`), arithmetic facts of the protocol's shape forwards (`wpForward`); ghost values of products normalized (`upd_snd`, `upd_ne`, data fields of user values). All per-field instances are deleted; the walks of SnapshotCache (`update_spec`, `main`'s snapshot to the free), MutexCounter (both versions' `loop4_body`), Iogroup (`add_spec`) and Handoff (both versions' producer, `ready` loop and `main`'s tail from the spawn) are `fsym` calls. Regression sep-auto WPHold.

Request: **Holder field steps as one library rule (coordinator item (a)) not landed yet**: `Proofs/Sync/SnapshotCache.lean` needs the holder's load/store of the lock's resource for its two fields, so it carries one more hand copy of the `wp_cnt` family: `wp_hold` (generic holder step, as `MutexCounter.wp_cnt` / `Iogroup.wp_cnt`) and its four instances `wp_ldA`, `wp_ldB`, `wp_stA`, `wp_stB` (the ghost transition `wk k false → wk k true → wk (k+1) false` passed as the rule's place, #52). `update_spec` is one `fsym` call over them and `MutexImpl.lock_wp`/`unlock_wp`. Also `main_spec` (hand walk, as `Sync.MutexCounter.main_spec`) rewrites `(liftM x).run s` to `ConcM.liftMem x >>= …` with a local `rfl` equation to apply `wp_ldA`/`wp_ldB`. DELETION PLAN: when the engine lane's single `@[fsym]` holder rule lands, delete `wp_hold` and the four instances (state the field transitions as that rule's ghost argument) together with `MutexCounter.wp_cnt`/`wp_load`/`wp_store` and Iogroup's copies; the `liftM` rewrite goes when `main_spec` is walked by `fsym`.

<a id="row-70d"></a>
### #70d Conc/Returns: no client yet

Status: **open**. Requester: csl/T-term.

Note: dead-module row 70 of agent 17; L9 row 70 keeps 70; this one is 70d

Progress: plan

Request: `Conc/Returns` (`Proto.returnsWithin`, turn-cost adequacy, ROADMAP current goal text): target leaf result, no client yet. PLAN: first client = a turn-counting protocol proof (T-term, research C13); if T-term is dropped, delete with `Proto.cost`

Deletion plan: first client: a turn-counting protocol proof (T-term, research C13); if T-term is dropped, delete with Proto.cost.

<a id="row-71"></a>
### #71 Conc/OsRules: premise evidence, standalone by design

Status: **open**. Requester: os lane.

Progress: plan; the full-state rules of the OS futex rows landed in `ZigLean/Sep/Full/OsFutex.lean` (STD-05 step A, PR #437), the target for OsRules' futex facts

Request: `Conc/OsRules`: proof-only premise evidence for OSF-01/02, OST-01/02, OSG-01 (docs/premises.md "Derived from", docs/os-threads.md); standalone by design (not dead). PLAN: its facts move into the FutexSpec/CTriple futex rules when those land (docs/thread-io-translation.md §4.1), then the module is absorbed

Deletion plan: move its futex facts into the full-state OS futex rules (ZigLean/Sep/Full/OsFutex.lean) and the FutexSpec/CTriple futex rules when those land (docs/thread-io-translation.md section 4.1), then absorb the module.

<a id="row-72"></a>
### #72 PageAllocator as an environment of an open std.mem.Allocator

Status: **closed**. Requester: L4 (Controls).

Progress: DONE: part 1 #369 (CTriple.toSoloThread: no Tgt map needed; alloc/free/resize thread triples); part 2 codex/l4-page-env (remap thread triple after #368, PageThread.cAllocSpec); the page-backed Lists.Open env chore/l4-controls (tests/roadmap/alloc-translated/ListsPage.lean: ext, env_runs, page_spec)

Request: **PageAllocator as an environment of an open `std.mem.Allocator`**: the translated PageAllocator's entries as thread triples (FTTriple, the FBA `fthread_*` pattern), `alloc` generic over the program's `Tgt` (PageLinux's alloc is a `CTriple` over `ConcM PageLinux.Tgt`; its RawVTable form wraps it in `Sched.soloRun 16`), then `CAllocSpec.ofRaw`/`env_ofRaw` → `CAllocSpec (CVTable.env (Lists.Alloc.env e) fns)` for a page-backed `Lists.Open.Ext`. Library + alloc-translated, no new judgment

<a id="row-73"></a>
### #73 Run-level adequacy to .illegal

Status: **closed**. Requester: L4 (Controls).

Progress: DONE: part 1 #364 (KFact.dead, free_dead, munmapWhole_dead, Holds.dead); part 2 codex/l4-page-env (FAllocInv.freed in free's post, coordinator decision B; the page allocator's freed = dead, PageThread.fthread_free). The Controls restatement (chore/l4-controls) needs no run-level theorem: with #77 fixed the kernel evaluates the runs (`.illegal` and the leak) from the start memory

Request: **Run-level adequacy to `.illegal`**: a library theorem over the existing judgments that reads a `CTriple` run (soloRun) down to "the block the client gave back with `munmapWhole'` is dead", so that a later access/munmap is `.illegal` (`Os.munmap_whole_then_illegal`, `access_illegal`, ZigLean/Os/MmapRun.lean). Kernel evaluation is not an option: `decide +kernel`/`unroll_solo` on `soloRun (setup; Open.push …)` with a page env exceeds maxRecDepth and, raised, 11 GB RSS as soon as a memory op follows `mem_Allocator_create`. If this needs a new judgment: stop and report

<a id="row-74"></a>
### #74 PLAN (legacy-to-retire)

Status: **closed**. Requester: L4.

Progress: DONE chore/l4-controls: tutorials/memory-safety/Controls.lean is deleted; its refuted clients are restated over Proofs/Lists/Open.lean and the translated PageAllocator in tests/roadmap/alloc-translated/ListsPage.lean (`controls`: unconditional refutations of Main.lean's properties from the program's start memory, the runs evaluated by the kernel after #77), and it left `legacy_users`

Request: PLAN (legacy-to-retire): `tutorials/memory-safety/Controls.lean` stays a legacy user (imports `Proofs.Lists.Cost`, std heap model) until #72 + #73 + #77; then its three refuted clients are restated over `Proofs/Lists/Open.lean` with the page-backed env (existential refutations: an admissible start memory in which push succeeds, from #77, and the double free / use after free `.illegal` there via `freeAll_freed`, `PageTok.deadOf`, `Holds.dead`, `Os.munmap_dead`/`access_illegal`) and it leaves `legacy_users`

<a id="row-75"></a>
### #75 Thread backend: undecided side condition blocks a sequential rule's ofSeq

Status: **closed**. Requester: L4.

Progress: DONE codex/fsym-thread-split (solveSides: a provider hypothesis with unknowns waits for the later provider goal that fixes them; one equal to an undecided goal of the rule is that goal, so the walk splits); regression sep-auto Threads resizeTo_thread; the PageAllocator's remap is a thread triple by plain fsym

Request: **Thread backend: undecided side condition blocks a sequential rule's `ofSeq`** (blocks L4 #72). `fsym` proves the translated PageAllocator's `free` and `resize` as thread triples (`FTTotalTriple`, plain `fsym`), but not `remap`: at `Os.mremap … MAYMOVE` the sequential walk (`PageSpec.remap_spec`) tries `FTotalTriple.mremapMoveC`, gets the side goal `S - lo < newLen` left and **splits on it**; the thread walk tries the same rule through `ofSeq`, and its `ThreadLocal` side goal (provider `ThreadLocal.mremapMove_of`, which needs that same `hn`) fails first, so the rule fails. Repro: branch `scratch/l4-remap-thread`, `scratch-l4/RemapThread.lean`. A provider without `hn` (`ThreadLocal.mremap_of`) was not picked up either. Request: in the thread backend, split on the undecided arithmetic side goals before solving the `ThreadLocal` goal, or try providers after the split

<a id="row-76"></a>
### #76 Read of a read-shared io prefix in a protocol: hand copies of wp_io

Status: **open**. Requester: critic run 15 (coordinator).

Progress: PARTLY DONE: `FLock.Inv.loadRest` (ZigLean/Sep/Full/LockSteps.lean) proves the exact plain-load/read-record fact once, from invariant-rest bytes and the caller's NoRace premise. `FLock.Fits.wp_readRest` derives its existing shared-reader statement from that fact with ReadShared.noRace_read; its duplicated primitive proof is removed. The full-state copies in Iogroup/Counter, Handoff/Ops and MutexCounter/Protocol are deleted; their walks pass the protocol's obligations to the rule. LEFT: the copies in the legacy-layer files RwLock and SemCounter (`ZigLean.Conc` logic, legacy_users), and the legacy holder copies WaitGroup `wp_cntLoad`/`wp_cntStore` and Semaphore `wp_cnt`.

Request: **`wp_io` has hand copies**: the read of the `io` prefix (read-shared bytes in the protocol's rest, `FLock.Inv.recordX`, no race by `ReadShared.noRace_read`) is proved by hand once per protocol: `Proofs/Iogroup/Counter.lean`, `Proofs/Handoff/Ops.lean`, `Proofs/MutexCounter/Protocol.lean`, `Proofs/Sync/SemCounter.lean`, `Proofs/Sync/RwLock.lean`. Needed: one `@[fsym]` library rule over every protocol with a lock whose rest keeps read-shared bytes, each protocol discharging only its obligations (the bytes in the rest, the invariant kept by a read record).

Workaround sites: `Proofs/Sync/SemCounter.lean`, `Proofs/Sync/RwLock.lean`, `Proofs/Threadsync/WaitGroup.lean`, `Proofs/Sync/Semaphore.lean`

Deletion plan: when each legacy-layer file migrates to the full-state logic (docs/legacy-retirement.md), replace its `wp_io` copy with `FLock.Fits.wp_readRest` and its holder copies with `FLock.Fits.wp_hold`. Keep the primitive load/record proof shared through Inv.loadRest. Close this row only when every listed legacy workaround site is gone.

<a id="row-return-bool-split"></a>
### #return-bool-split A return whose Boolean value the postcondition matches on is not split

Status: **open**. Requester: arena-gen (arena macros -> fsym).

Progress: open; an update now takes its result unknowns from the return's value (ledger #update-result-unknowns), so only the split is missing

Request: **A return of an undecided Boolean expression that the postcondition matches on is not split**: the arena's `resize` returns `pure (le false n len)` on the path of a grant that is not the first node's last; the postcondition `rresizePost … (le false n len)` matches on it, and with `n` against `len` undecided (`n ≥ len` known, `n = len` or `n > len` not) no update closes the return (`resize_other_upd` needs `n ≤ len`, `resize_false_upd` needs `n > len`). Needed: at a return, split on an undecided `Bool`/`Prop` that the postcondition matches on, as on an `if` of the program.

Workaround sites: `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean`

Deletion plan: delete `rcases Nat.lt_trichotomy n.toNat s.len.toNat` in each arena `resize_ct` (with #64) once the walk splits a return's undecided Boolean that the postcondition matches on.

<a id="row-arena-resize-update-cost"></a>
### #arena-resize-update-cost (perf) whole-state updates at every return: the arena's resize

Status: **open**. Requester: arena-gen (arena macros -> fsym).

Progress: open

Request: **(perf)** the arena's `resize_ct` takes ~160 s and 8M heartbeats per module (free ~40 s), against ~13 s with the hand tactics it replaces: four whole-state updates (a 30-atom state) are planned at each return until one closes it, and a failed plan costs seconds. Candidates: try only the updates whose postcondition head matches the return's (P09-E5's registry keyed by heads), and reject a precondition early when an atom head of `P₀` is missing from the state.

<a id="row-update-result-unknowns"></a>
### #update-result-unknowns An update's result unknowns and the bundle projections of its postcondition

Status: **closed**. Requester: arena-gen (arena macros -> fsym).

Progress: DONE: landed with the arena (#279) and its macro replacement (#388) (Auto.lean `tryUpd`, `reduceCtorProjs`)

Request: **`tryUpd` solved an update's side goals before it compared `Q₀` with the return's postcondition**, so an unknown that only `Q₀` names (the result `r` of the arena's `rresizePost … r`, constrained by `r = true`) was taken from any fact of the side goal's shape (`Rat.blt 0 φ.val = true`), and the projections of an expanded bundle (`v.A'` of `v : FV`) were reduced in `P₀` and the side goals but not in `Q₀`, so `acEq` with the return's postcondition failed. Fixed: `Q₀` (projections of constructor applications reduced, `reduceCtorProjs`) is unified with the return's postcondition (same head, reducible) before the side goals.

<a id="row-update-plan-views"></a>
### #update-plan-views An update's precondition planned through views of the atoms the planner did not find

Status: **closed**. Requester: arena-retain (retaining reset over wpts headers).

Progress: DONE on codex/arena-engine (Auto.lean `closePre`); regression `tests/roadmap/sep-auto/SepAuto/Updates.lean` (`upd_view`)

Request: **An update's precondition was planned without views of its own**: `tryUpd` gave up where the planner did not find an atom of the update's precondition, and only a stuck return viewed the state, by the atoms that every plan of the return had missed. So where another update's plan (or a branch of an `if`) had missed a region of the same block, the `apts` that an atomic op left was viewed as the bytes of a region (`apts_view`), and the update that names the word as a `wpts` (the arena's node headers, any tag constraint) no longer applied (the arena's `resize` over `wpts` headers). Fixed: `closePre` plans the precondition, views the state's atoms as the atom that plan missed last (`viewAtoms`, the wanted cache scoped to the plan: `apts_wpts_view`) and plans again.

<a id="row-carve-size-probes"></a>
### #carve-size-probes A carve's size probes searched the case facts of other regions

Status: **open**. Requester: arena-retain (retaining reset over wpts headers).

Progress: PR481's isolated A/B confirms the added ordinary size attempt regressed unchanged Region.free_large_sized at its original800000 cap: current attempt times out; disabling only that attempt passes the identical control. Demand n can equal the partial24-byte header under24<=n, so failed equality search explores unrelated region-disjointness cases. Claude6280049836 approved dropping fix3: the entire carve function is restored byte-for-byte to integrated main, including protected cases=false probes; fixes1-2 remain. The new small case-fact positive goal is retained unchanged inside an explicit expected-failure control in Structs, with its original hypotheses and default cap. That obstruction remains open; no new search heuristic, budget increase or production theorem weakening. The fallback whole Structs and full29-file official sep-auto suite PASS on f9505e4e/main578aa3b2 with Auto5614ed37; guards b8bf14f3/e6cbb205 bind current source and artifacts. Earlier passes/failures keep their original bindings. Reproduce with tests/roadmap/sep-auto/check.sh; discussion6280040941, ruling6280049836 and actual report6280488414 record the bounded stop.

Request: **The planner's size probes of a carve (`n = sz`, `n ≤ sz`, `sz ≤ n`) ran `omega` through the case facts** (the pairwise disjointness of the owned regions, disjunctions). Those facts never bound a region's size, and a failed search through them is exponential: a node of `n ≥ 24` bytes given back against its 24 joined header bytes in a state of three blocks took 1.8M heartbeats per probe (the arena's `loop78`, a node given back to the child while the next node is in the state). Fixed: the probes run the solver without the case facts (`cases := false`); the plain facts still decide them.

<a id="row-arith-implications"></a>
### #arith-implications The arithmetic solver on implications

Status: **closed**. Requester: arena-retain (retaining reset over wpts headers).

Progress: DONE on codex/arena-engine (Auto.lean `arithGoals`, `arithSimpCtx`, `arithCore`); regressions `tests/roadmap/sep-auto/SepAuto/Arith.lean` (`implies_refuted`, `implies_fact`, `implies_fact_target`, `implies_post`)

Request: **A fact that is an implication was not proved, and not used.** A loop invariant's `⟪s.it = none → x0 = none⟫` at the next iteration (`some N = none → x0 = none`, the arena's `loop78`) was left to the caller, and at an exit (`none = none → x0 = none` among the facts, the target `x0 = none`) the fact was not reduced to its conclusion, and a target that is no arithmetic was not closed by the fact. Fixed: an implication's premise becomes a fact for its conclusion (`arithGoals`, all or nothing); `true_implies`, `false_implies`, `implies_true` in the normal form; a fact in normal form that is the target closes it before `omega` (`arithCore`).

<a id="row-rule-instances-first"></a>
### #rule-instances-first A rule whose instance arguments have no instance is planned anyway

Status: **closed**. Requester: arena-retain (retaining reset over wpts headers).

Progress: DONE on codex/arena-engine (Auto.lean `instArgsMissing`, before the precondition's plan); regression `tests/roadmap/sep-auto/SepAuto/AtomicPlain.lean` (`ptr_beside_word` within 250k heartbeats; without the check it hits the limit in `wpts_loadPacked`)

Request: **A rule was planned before its instance arguments were synthesized**: the packed load rule (`wpts_loadPacked`, `[Packed T 64]`) on a pointer load (`T := Ptr`, no instance) planned its precondition through views (26k heartbeats per vtable load in the arena's `reset`) and failed only at `synthInstArgs`. Fixed: the instance arguments that the unified command determines are synthesized first; a missing instance rejects the rule.

<a id="row-probe-case-budget"></a>
### #probe-case-budget A probe's search through the case facts is unbounded

Status: **closed**. Requester: arena-retain (retaining reset over wpts headers).

Progress: DONE on codex/arena-engine (Auto.lean `omegaFacts (budget)`, `probeCaseBudget`, `withBudget`; probes: `quick` arith, the discharger's side conditions, the offsets of two pointers in `proveEqGoal`). Follow-up on fix/fsym-probe-budget: `withBudget` catches the heartbeat exception wherever in the probe the budget is hit (`mkAppM`, the split-term rewrite, not only `omega`) and fails the probe; it binds within the context's `maxHeartbeats` (the smaller limit; past that one the exception is rethrown); one rule for every cache of the run: nothing obtained under a limit (the heartbeat limit, `heartbeatsOut`, or a search's fuel, `outOfFuel`) is cached as a failure (`limitedRun`: `probe`, `detProbe`, `encFieldOf?`, `structLayoutOf?`, `lawfulEncOf?`, `lawfulPackedOf?`), so a later query with more room (an unbudgeted obligation, another query order) retries it. Regressions `tests/roadmap/sep-auto/SepAuto/Arith.lean` (`budget_outside_omega`, `budget_no_failure_cache`, `budget_within_limit`: the budget spent at once), `tests/roadmap/sep-auto/SepAuto/Structs.lean` (a field of `N2` after `N9`'s, past the nesting budget) and `tests/roadmap/sep-auto/SepAuto/Packed.lean` (`nested_inner_after_outer`); the end-to-end probe (two nodes in blocks of unknown addresses among 27 disjointness facts) arises in the retaining reset's reallocation path, whose proof adds it

Request: **A probe searched the case facts without bound**: `val.off ≠ nd.N.off` (a node the child just granted against the old node, blocks of unknown addresses: no fact decides it) took 303k–1.4M heartbeats in one `omega` over 27 disjointness disjunctions, in the arena's `reset` (retaining modes, reallocation path). Fixed: a probe (a quick `arith`, a rewrite's side condition in the discharger, the offsets' equation of a pointer comparison) searches the case facts within `probeCaseBudget` heartbeats of its own; past them it fails, which is sound (a probe that fails only withholds a step). Obligations (rule side goals, `fsym_arith`) are not bounded.

<a id="row-thread-local-exlift"></a>
### #thread-local-exlift The locality of a rule over a region carved to a size

Status: **closed**. Requester: arena-retain (retaining reset over wpts headers).

Progress: DONE on codex/arena-engine (AutoThread.lean `ThreadLocal.exLift`, `@[fsym_provider]`); regression `tests/roadmap/sep-auto/SepAuto/Threads.lean` (`headerWord`; without the provider: `fsym: no rule for the command store 8 p x`)

Request: **A sequential rule whose precondition is `∃ bs, ⟪bs.size = n⟫ ⋆ up (regionIn p … bs)` had no locality in a thread** (`region_store_wpts`, `region_storePacked_wpts`, `region_storeAll`: a node header over the bytes the child granted, in the arena's `reset`): no provider looked through the existential and the fact. Fixed: `ThreadLocal.exLift` (local if local for each witness, with its fact).

<a id="row-packed-bits-steps"></a>
### #packed-bits-steps A packed struct's bits: fromInt steps and the size of its encoding

Status: **closed**. Requester: arena-retain (retaining reset over wpts headers).

Progress: DONE on codex/arena-engine (AutoRules.lean `packedOfBits_step`, AutoArith.lean `reduceEncodeVia`); regressions `tests/roadmap/sep-auto/SepAuto/AtomicPlain.lean` (`packed_encode_size`, `packed_ofBits`)

Request: **`Packed.ofBits?` of valid bits had no step rule** (`Node.Size.fromInt` in the arena's `reset`: "no rule"), and **the size of a packed value's encoding** (`(Enc.encode s).size`, an `Enc` through `Packed.toBits`, no `LawfulEnc`) stayed an atom of `omega`. Fixed: `packedOfBits_step` (`valid b` a side goal); `reduceEncodeVia` unfolds an `encode` that the instance defines by another type's (`unfoldProjInst?`), whose size applies.

<a id="row-packed-roundtrip"></a>
### #packed-roundtrip A packed struct's bits read back: toBits (ofBits b) = b

Status: **closed**. Requester: arena-retain (retaining reset over wpts headers).

Progress: DONE on codex/packed-roundtrip (ZigLean/PackedLayout.lean `LawfulPacked`, `PackedLayout.lawful`, `EnumTags.lawful`; Auto.lean `lawfulPackedOf?`, simproc `packedRoundTrip`, and the other direction `packedValRoundTrip`/`packedValidToBits`, by which the per-type round trips of `Proofs/Layout/Proofs.lean` and `Proofs/Threads/Proofs.lean` are proved); regression `tests/roadmap/sep-auto/SepAuto/Packed.lean` (bool/int/enum/signed-enum/non-exhaustive/float/nested/empty packed structs, a stored `fromInt`, both directions, a packed union field fails closed; the round trips fail on the previous engine: `fsym_arith: not proved`). Review follow-ups on fix/fsym-probe-budget: the context's instance first (`trySynth?` before the closed-type check, as `lawfulEncOf?`: a generic client over `[LawfulPacked T n]`, regressions `generic_bits`, `generic_val`); a derivation past the nesting budget caches no failure for the types inside it (`limitedRun`, ledger #probe-case-budget; regression `nested_inner_after_outer`). The fuel stays: a Lean structure may be recursive and an instance family may nest without end, so termination does not follow from the type. Vector and packed-union fields: ledger #packed-lawful-split

Request: **`Packed.toBits (Packed.ofBits b : T) = b` (for valid `b`) has no rule.** The arena's `reset` stores a node's size as `Node.Size.fromInt(adjusted)` (`store 8 N (Packed.ofBits adj)`), so the word is `wpts N (Packed.toBits (Packed.ofBits adj))`; the next epoch's invariant (`Kept`, `Header`) names it `wpts N (BitVec.ofNat 64 sz)` with `sz` the node's size. The arithmetic normal form unfolds the instance to its fields (`setWidth 64 (if b.toNat >>> 0 % 2 = 1 then 1#1 else 0#1) <<< 0 ||| setWidth 64 (extractLsb' 1 63 b) <<< 1`), which `omega` cannot read (`|||`); a failed search costs 727k heartbeats. Needed: the round-trip law for every packed struct (fields tile the backing integer; enums by `valid`), as a law the translator emits with each `Packed` instance (a `LawfulPacked` class) or one the engine derives per type (as `lawfulEncOf?` derives `LawfulEnc`), then a conditional `fsym_arith` rewrite. The retired per-module rule was `size_toBits_ofBits` (Core, 45b83ccf5).

<a id="row-packed-lawful-split"></a>
### #packed-lawful-split LawfulPacked for vector and packed-union fields: the law split by direction

Status: **open**. Requester: critic 32 (review of #450, packed-roundtrip).

Progress: OPEN: plan recorded on fix/fsym-probe-budget; nothing implemented

Request: **A packed struct with a vector field or a packed-union field gets no `LawfulPacked`** (`lawfulPackedOf?` derives enums, structs and types whose bits are their value; `tests/roadmap/sep-auto/SepAuto/Packed.lean` `Wrap` fails closed in both directions). The two directions of the law differ for a packed union: `toBits (ofBits b) = b` holds for every `b` (`ofBits` writes the bits as integer bytes, `bitsOf` reads them back), but `ofBits (toBits u) = u` with every bit of `u` determined does not: a byte whose bits are all defined in a form other than `.int` (`.mask 0xFF x`) reads as `x` and is rebuilt as `.int x`. Plan: split `LawfulPacked` (ZigLean/PackedLayout.lean) into the bits direction (`toBits_ofBits`, which `packedRoundTrip` needs) and the value direction (`ofBits_toBits`, which `packedValRoundTrip`/`packedValidToBits` need), `LawfulPacked` their conjunction; a packed union gets the bits direction by definition; a struct gets each direction its fields all have (`PackedLayout.lawful` per direction); a `Vector`/`Vec` of lanes gets each direction of its lanes by one generic instance, proved once.

Workaround sites: `ZigLean/PackedLayout.lean`, `tests/roadmap/sep-auto/SepAuto/Packed.lean`

Deletion plan: The single-direction `LawfulPacked` class of ZigLean/PackedLayout.lean becomes the two directional classes (the conjunction kept as `LawfulPacked`), and the fail-closed `Wrap` example of the bits direction in tests/roadmap/sep-auto/SepAuto/Packed.lean becomes a proved round trip (the value direction stays fail-closed for the union); a vector-field struct joins the regressions.

<a id="row-chain-case-unfold"></a>
### #chain-case-unfold A recursive list predicate unfolded by the case the loop tests

Status: **open**. Requester: arena-retain (loop78 of the retaining reset).

Progress: open

Request: **A loop over a linked list whose invariant names the rest of the list as one recursive predicate is not walked uniformly.** The arena's `loop78` keeps the last node: its invariant is `Chain CI true (ns.map NodeV.full) s.it` (`Chain` recursive over the list, its next pointer null at the last node). `fsym` needs the list's cases split by hand (`rcases ns with _ | ⟨nd, _ | ⟨nd2, ns⟩⟩ <;> cases it`), `Chain` kept folded (`attribute [local fsym_atom] Chain FreeCl`) and, per case, a hand unfolding of the first node and the folded rest (`chain_one`, `chain_full_cons2`, Reset.lean) with its own rule list. Needed: unfold a recursive predicate of the state by one constructor at the step that tests its pointer (the `if next == null` of the body), keeping the rest folded where the invariant names it again; then `loop78_step` takes the shape of `loop19_step` (one `cases … <;> simp only … <;> fsym`).

Workaround sites: `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean`

Deletion plan: replace the per-case bullets of `loop78_step` (ArenaSpec.lean, ArenaSpecMacos.lean, ArenaSpecFixed.lean) with one uniform `fsym` walk, drop the local `fsym_atom` attribute and delete `chain_one`, `chain_cons2`, `chain_full_cons2` and `chain_head` (Reset.lean) if no other proof uses them, once fsym unfolds a recursive list predicate by the case the step tests.

<a id="row-77"></a>
### #77 Kernel evaluation of runs over a page-sized block: deep recursion / >11 GB

Status: **closed**. Requester: L4 (Controls).

Progress: DONE (one form shared by PR #392 and chore/l4-controls, coordinator decision 2026-10-18): `writeBytes` (ZigLean/Mem/Basic.lean) is irreducible and shares the unchanged list suffix (`take` ++ bytes ++ `drop`), which the kernel reduces lazily; the unconditional `writeBytes_eq` keeps the array-splice equation for the lemmas and a checked `@[csimp]` keeps native array execution. The cause was the array form: `Array.extract`/`++` build each part by repeated `push`, a nested `List.concat` chain the kernel unfolds by deep recursion. Open's `push` with the page env now decides from the program's start memory in under a second (tests/roadmap/alloc-translated/ListsPage.lean)

Request: **The kernel cannot evaluate a run that writes into a block of 4096 bytes.** `decide +kernel` on `do let p ← Zig.alloc .heap 4096 8; Zig.memset (α := BitVec 8) 1 p 16 none; Zig.store (α := BitVec 32) 4 p 7` from `{}` fails with "(kernel) deep recursion detected" (0.9 GB); the same with 16 bytes decides in 0.6 s. The L4 Controls hit it through the translated PageAllocator (every grant is a 4 KiB mapping): Open's `push` with a page-backed env (`create` -> `allocBytesAligned` memsets the 16 bytes, then `push` stores the fields) does not decide from a concrete start memory; raising `maxRecDepth` (4000 to 200000) makes `decide +kernel` and `unroll_solo` exceed 11 GB RSS (build-guard rss_limit). The page `alloc` alone decides (`PageAlloc.alloc_top`), and so do runs that only read the page or write it without a prior `memset`. Needed: one concrete admissible start memory in which `push` returns `.ok p`, evaluated (kernel-checked), so that the refutations of #74 are existential (natively right: `mmap` may fail, so no triple promises `.ok`). Likely cause: the kernel's representation of the 4096-byte `Array Byte` (list-backed; `writeBytes`/`extract`/`append` are linear recursions) under `memset` + `store`. Options: a bytes representation the kernel reduces with bounded depth (e.g. chunked or `ByteArray`-like with kernel-friendly ops), or a run lemma family that rewrites the memset/store effect on a symbolic block (`simp`/`fsym_norm` equations) instead of evaluating the array. Repro files: `~/.cache/air2lean/scratch/l4/T36.lean` (minimal), `T32.lean` (Open push with the page env from a precomputed memory, rss_limit), `T34.lean` (page alloc + memset + store).

<a id="row-78"></a>
### #78 LawfulEnc instances for generated structs

Status: **closed**. Requester: L6 (FBA client).

Progress: DONE codex/eng-78-79: no translator change. One generic theorem `StructLayout.lawfulEnc` (ZigLean/Sep/Full/Struct.lean: a struct whose encoding holds its fields' encodings, all lawful, reads back) and the engine's `lawfulEncOf?` (Auto.lean: the layout from the decoding, `structLayoutOf?`; the parts of the encoding, `encParts?`/`fields_extract_sz`; each field's instance synthesized or derived again), used where `fsym` synthesizes instances (`synthInstArgs`, `solveSides`). The folds `pts_fold_encode`/`pts_fold_write` (`@[fsym_view]`) turn owned bytes of a lawful value's encoding into its `pts`. Packed structs, unions, storage-wrapped fields and encodings that do not write each field where the decoding reads it get none (fail closed). Global `LawfulEnc Slice`. A store piece by piece that applies now beats a split on another rule's undecided side condition (a region store that the derived instance enables). Regression: sep-auto Structs.

Request: **The translator's generated structs have no `LawfulEnc` instance** (`Enc` only), so `decode (encode w) = pure w` and `(encode w).size = Enc.size T` are not available for them. Effect: after `FTotalTriple.storeBlock` stores a struct into a stack block (`store 8 s1 (sv : heap_FixedBufferAllocator)`), the state holds `up (bytesAt s1 A 24 .stack (writeBytes undef 0 (encode sv)))`, and `fsym` cannot fold it back into `up (pts s1 8 sv)` at a return (the fold needs the decode equation). The legacy FBA client proved `slice_decode_encode` and the struct's field decodes by hand. Needed: the translator emits a `LawfulEnc` instance for each generated struct (or a generic theorem for the struct `Enc` shape it builds), and an `@[fsym_view]` fold `bytesAt` -> `pts` for a `LawfulEnc` value. Repro: tests/roadmap/alloc-fba/wip/ClientStart.lean on codex/l6-client-wip.

<a id="row-79"></a>
### #79 Struct pts to field words entailment

Status: **closed**. Requester: L6 (FBA client).

Progress: DONE codex/eng-78-79: `StructLayout.split` and `StructLayout.join` (ZigLean/Sep/Full/Struct.lean: a struct's `pts` is its fields' `pts` and its padding's bytes `padBytes`, the join reading the pieces' labels from the memory) for every struct with a layout; `fsym` takes them as views at a stuck step (`viewAtoms`: `splitFor` for a wanted field of a struct atom's block, `joinView?` for a wanted struct whose pieces are in the state). `ListsFba.struct_words` is deleted (its use is `fsym_entail`). Regression: sep-auto Structs.

Request: **No entailment from a struct's `pts` to its field words.** `fsym_entail` leaves `EUpd (up (pts s1 8 (sv : heap_FixedBufferAllocator))) (up (pts s1 8 sv.end_index) ⋆ up (pts (s1.add 8) 8 sv.buffer))` open (FBA's invariant holds the struct as two words, `wEnd`/`wBuf`). lists-fba proves the same split by hand from the bytes (`ListsFba.struct_words`, via `bytesAt_split` and per-field decodes). Needed: one library rule (`@[fsym_view]` or planner step) that cuts a generated struct's `pts` into its fields' `pts` and joins them back, for any struct the translator generates (the field offsets and decodes from `structFields?`, as the field load/store rules of row 28 do). Then `struct_words` goes. Repro: tests/roadmap/alloc-fba/wip/ClientStart.lean on codex/l6-client-wip.

<a id="row-p09-e1"></a>
### #P09-E1 residual-goal attribution

Status: **closed**. Requester: invariant-synthesis (P09).

Progress: AutoReport collects each residual's program point, judgment, rule, condition and stop reason in schema-versioned JSON; Report.lean checks incomplete sequential, thread, concurrent and protocol proofs, exact ordinary/reporting parity and speculative rollback

Request: residual-goal attribution: each goal fsym leaves names its origin (postcondition conjunct, side condition of rule r); stop reasons machine-readable from `Auto.run` (extends #14, #15)

<a id="row-p09-e2"></a>
### #P09-E2 strongest-postcondition inference at returns for FTotalTriple/FTriple and the thread backends, as inferPost...

Status: **open**. Requester: P09.

Progress: pending maintainer approval (note: agent 17's single-step post work on codex/fsym-bridge-ofseq touches inferPost for thread goals; keep compatible)

Request: strongest-postcondition inference at returns for FTotalTriple/FTriple and the thread backends, as `inferPost` does for WP segments

<a id="row-p09-e3"></a>
### #P09-E3 abduction report

Status: **open**. Requester: P09.

Progress: pending maintainer approval

Request: abduction report: at "no plan for its precondition", return the missing atom with its unknowns

<a id="row-p09-e4"></a>
### #P09-E4 @[fsym_inv] loop-invariant registry

Status: **open**. Requester: P09.

Progress: pending maintainer approval

Request: `@[fsym_inv]` loop-invariant registry: apply the backend's loop rule with a registered invariant and measure; parameters by the planner, frame inferred

<a id="row-p09-e5"></a>
### #P09-E5 @[fsym_upd] ghost-update registry keyed by heads, tried at returns

Status: **open**. Requester: P09.

Progress: pending maintainer approval

Request: `@[fsym_upd]` ghost-update registry keyed by heads, tried at returns; generalizes caller updates (9f); replaces #64–#67 workarounds with the bump-ledger family

<a id="row-recursive-group-total"></a>
### #recursive-group-total Generic total correctness of a recursive function group

Status: **open**. Requester: L8b-1 tick coverage (Task 09); P03/stack.

Note: Decision: https://github.com/riventic/air2lean/pull/393#issuecomment-6211327766 . The displayed goal identifies the missing generic entry point. The exploratory input containing per-program inductions elaborated, but that is not generic total-recursion coverage and no bare-fsym failure is claimed. The rejected scaffolding was removed. The separately scheduled feature closes the P03 memory-recursion/stack-budget gap.

Progress: Coordinator confirmed the missing API on 2026-10-16 (PR #393 comment 6211327766) and will schedule it separately. L8b-1 covers straight-line code and loops, not total recursion.

Request: One general library rule per emitted recursive partial_fixpoint group: a contract for each member and a well-founded measure on the arguments. fsym must discharge each recursive call through the callee's contract at a smaller measure, with recursive frames charged to the stack-depth token (#402, STK-01). The same full-state framework must support sequential, thread and protocol clients without a new judgment, tactic, proof template or per-program induction. Exact exploratory goal: for `def recur (n : Nat) : MemM Unit := do Zig.tick; if n == 0 then pure () else recur (n - 1)` with `partial_fixpoint`, prove `FTTotalTriple (R ⋆ plain) (recur n) (fun _ => R ⋆ plain)` from a supplied invariant/contract and argument measure, with fsym walking the body. The existing `FTriple.admissible_fun` supplies partial correctness only; `FTotalTriple.loop_ghost`/`loop_measure` and their thread forms apply to Zig.loop, not recursive call groups. Per-instance `Nat.strongRecOn; rw [recur.eq_def]; fsym [ih]` is explicitly not the required API and is not retained as a workaround.

<a id="row-t1"></a>
### #T1 credits n is not split for tick_credit

Status: **open**. Requester: stack-ac lane (codex/stack-ac-ticks).

Progress: see request text (tick rows, plans/tick-cost.md)

Request: HIT (open): `FTotalTriple (R ⋆ credits 2) (tick; tick) (fun _ => R)` -> fsym leaves the goal unsolved: the planner does not split `credits 2` into `credits 1 ⋆ credits 1` for `FTotalTriple.tick_credit`. Needs counted atoms (`credits`, `spent`: `spent_add`/`spent_zero`, `credits_add`/`credits_zero` exist in Full/Ghost + Full/Tick). Leftover `spent n`/`credits n` drop already works (`@[fsym_drop] EUpd.spent_drop`, `EUpd.credits_drop`).

<a id="row-t2"></a>
### #T2 plain atom: tick_plain receipt dropped (bare fsym)

Status: **closed**. Requester: stack-ac lane (codex/stack-ac-ticks).

Progress: see request text (tick rows, plans/tick-cost.md)

Request: OK: `plain` is `attribute [fsym_atom] plain`; `FTotalTriple (R ⋆ plain) (tick; tick) (fun _ => R ⋆ plain)` is a bare `fsym` (tick_plain gives `plain ⋆ spent 1`, the receipt is dropped). Also one-logic Block.stackCycle_spec (`allocStack` + `free` under `R ⋆ plain`) is a bare `fsym`. No `@[fsym_persistent]` was needed because the rules return `plain` in their post.

<a id="row-t3"></a>
### #T3 credits 1 consumed by tick (bare fsym)

Status: **closed**. Requester: stack-ac lane (codex/stack-ac-ticks).

Progress: see request text (tick rows, plans/tick-cost.md)

Request: OK: `FTotalTriple (R ⋆ credits 1) tick (fun _ => R)` is a bare fsym (tick_plain/tick_unmetered are skipped).

<a id="row-t4"></a>
### #T4 ticks in the CTriple backend (not attempted)

Status: **closed**. Requester: stack-ac lane (codex/stack-ac-ticks).

Progress: The existing rules walk callMC Zig.tick in sep-auto/Ticks.cbody_spec and its loop in cloop_spec, in the plain mode; no backend-specific tick rule was needed (a historical probe against 958596cfc, 2026-10-16, first showed it; sep-auto/check.sh now checks Ticks). The CTriple evidence covers the plain mode only: a metered (credits) tick under CTriple has no control yet.

Request: not attempted (CTriple backend, phase 2).

<a id="row-t5"></a>
### #T5 tick_run kept opaque in fsym_norm

Status: **closed**. Requester: stack-ac lane (codex/stack-ac-ticks).

Progress: see request text (tick rows, plans/tick-cost.md)

Request: OK so far: `tick_run` is `@[zig_unfold]` (Mem/Lemmas) but fsym's rule match on `Zig.tick` fires first in the repro; keep `tick` opaque in fsym_norm when the emitter (L8b) inserts `callM tick`.

<a id="row-fowned-bridges"></a>
### #fowned-bridges Step through the WP.liftMem_fowned* / callMC_fownedS bridges

Status: **open**. Requester: coordinator.

Progress: part 1 (codex/fsym-fowned): the WP walk takes a thread's own stack block before its spawn through the registered `WP.liftMem_fowned` segments: allocation, field pointers (`Reaches.bauth`: the block's size from its extent), stores at byte offsets (`FTotalTriple.storeBytesAt`, Int offsets as generated code writes them), closed sizes of encodings (`reduceClosedSize`, kernel evaluation; closed side goals by `decide +kernel`); regression sep-auto WP `block_fields`; on Sync/Mutex `main` the walk reaches the spawn. Part 2 (codex/fsym-fowned2): the protocol's start at the spawn, so each `main` is one `fsym` call from `FOwned.start0_facts`: facts of a step's run (`@[fsym_run]`, `wpRunFacts`: `store_runFacts`, `alloc_runFacts`, `allocStack_runFacts`, `ptrProject_runFacts`, `load_runFacts`, `load_clocksLe`; a caller's run lemma such as `inv_spawn`), `inv_start` backwards with unknowns (`assnByHyp` unifies atoms up to unfolding), the child's ghost value from the protocol's `init` (a projection reduced, an equation that assigns the unknown), `inv_of_box` forwards (`wpForwardEx`: an `∃` conclusion at a stop), `wpAssumptionArgs`, `numAliases` (ThreadId), Boolean facts in `fieldEqs`, a conjunction's first part again after its second fixed an unknown; the hand bridges of Sync/{Mutex,Handoff,SnapshotCache} and Threadsync/{Mutex,Handoff} `main` are gone; regressions sep-auto WP `run_facts`, `thread_bound`, `same_pred`, `bool_case`, `and_retry`, `main_start`, `main_start_ex`. Open: the hand bridge sites of the other clients (Atomics/{MessagePassing,Relaxed,Stack}, Cancel/Group, Detach/Worker, Iogroup/Counter, Sync/{Cond,RwLock,RwLockSnapshotPair,SemCounter,Semaphore}, Threads/{Counter,Disjoint}, Threadsync/{Cond,WaitGroup}, tests sep-auto Threads, spawn-failure Group/Pair, thread-locals Counters), then the CM-form bridges and the alloc FTT ofSeq forms in Block.lean. Task 18 library follow-up (2026-10-19, change PR #461; approval PR #390 https://github.com/riventic/air2lean/pull/390#issuecomment-6259257096 and https://github.com/riventic/air2lean/pull/390#issuecomment-6260745106): the existing allocation/store run facts now expose the returned old block index, one-block allocation growth, store block-count preservation, and unchanged current/threads/atomics/waiters/woken/groups/clock count. All 19 positive sep-auto WP controls pass, including strengthened run_facts, two_blocks and two_blocks_loop through the existing WP.loop body inference; no engine change or missing generic-loop rule is claimed. Iogroup/Counter remains open: its unchanged main_spec diagnostic walks both allocations, owned projections 16/20 and all four initialization stores, then stops before the initial protocol invariant is admitted. wpForwardEx needs the invariant constructor's resource atom up (bytesAt gPtr ?A' 16 .stack ?bg), but the current atom uses the allocated pointer with block m_after_first.blocks.size, whose equality to 1 uses FOwned.start0_facts (no blocks at start), allocation growth and store block-count preservation together; the allocation facts alone allow arbitrary initial block counts. assnByHyp attempts only definitional matching when an atom contains any unknown witnesses; it uses proveEq only for a fully determined atom, so the known pointer equality is not used while inferring address/bytes. This mixed-atom match is the exact remaining step; later fixed-body matching is not isolated. The full extent is preserved (bext is bauth with Frac.one). The remaining clients, bridges and retirement conditions stay open; this library follow-up retires none. Follow-up from coordinator review https://github.com/riventic/air2lean/pull/461#issuecomment-6265159666 (not implemented in this PR): registered WP.liftMem_fowned in ZigLean/Sep/Full/ThreadOwned.lean currently forwards only current and threads from FStepIn. A load after alloc/store loses the groups equality in the coordinator's control; load_runFacts forwards only blocks. Forward the groups, woken, clocks.size and waiters equalities, plus the existing FStepIn.atomics AMap relation, through the generic wrapper for every MemM step, rather than adding per-primitive copies. This does not assert atomics equality for arbitrary steps: atomic stores can change that state. Keep operation-specific atomics equalities where their semantics justify them; the per-primitive current/threads conjuncts are redundant and can be removed with the generic follow-up. The two_blocks/two_blocks_loop controls and private Counter diagnostic select the final allocation with FTriple.allocStackDrop 16 8: this size/alignment hint is layout-sensitive, so review its generic mode-selection boundary before relying on it in migrated clients. These wrapper and hint follow-ups remain open and add no code to this PR.

Request: fsym should step through the WP.liftMem_fowned*/callMC_fownedS bridges (~20 hand call sites) so the 4 remaining alloc FTT ofSeq forms in Block.lean can be deleted (#329 body has details).

<a id="row-ofseq-one-liners"></a>
### #ofseq-one-liners Seven remaining hand ofSeq one-liners

Status: **open**. Requester: coordinator (critic run 9).

Progress: PR #352 (merged 2026-10-15) deleted the term-level copies in Block.lean and Local.lean; one remains: `FTTotalTriple.storeBytes_bytesAt` (ZigLean/Sep/Full/Ops.lean ~729, `ofSeq` plus `ThreadLocal.storeBytes`)

Request: 7 remaining hand ofSeq one-liners (Block.lean:378/383/391, Local.lean:164/169, Ops.lean:664/671) -> AutoThread providers, then delete.

<a id="row-stack-child-budget"></a>
### #stack-child-budget A spawned thread's stack budget, reserve and sp token

Status: **open**. Requester: stack-region lane (codex/stack-pr5).

Progress: main's budget, the token rules, cur t and its thread rules are done (Full/Stack, Full/Init run_init_stack, FOwned.noCur); open: the model side

Request: `Thread.forkWith`/`Os.Linux.clone` give a child no budget (MM-18 step 5): a spawned thread has no stack token, so its stack pushes are plain-mode only. Needed: the child's budget at fork (environment parameter first, `SpawnConfig.stack_size` later) with its reserve (`Mem.reserveAt?`; no fit: `SystemResources` where the spawn policy allows a failure, else `.stackOverflow`), the reserve released at thread end, the lifetime cells reserved up front; then a spawn rule that hands the child `sp c S_c k_c` (with `StackAuth` of the forked memory) and `FOwned.start` with a budgeted main (`sp 0 S 0` in main's part).

<a id="row-stack-wp-cur"></a>
### #stack-wp-cur The WP walk hands cur t to a thread's segment (WP.liftMem_fownedCurS)

Status: **open**. Requester: stack-region lane (codex/stack-pr5).

Progress: the rule exists (Full/ThreadOwned `WP.liftMem_fownedCurS`), not registered

Request: fsym's WP backend applies `WP.liftMem_fowned` (@[fsym], AutoWP) with the segment's precondition the thread's part; a segment that pushes a stack block from a budget needs `cur t` (`FTTriple (Pa ⋆ cur t) x (fun a => Qa a ⋆ cur t)`). Register `WP.liftMem_fownedCurS` (or a `liftMem_fowned` form of it) once a protocol client has a budgeted thread (needs row stack-child-budget for any thread but main), and walk such a segment.

<a id="row-pick-bind"></a>
### #pick-bind Pick-bind rules: bind rules over pick >>= op >>= g

Status: **closed**. Requester: CSL (#19, #20) / coordinator.

Progress: DONE: PR #352 (merged 2026-10-15) registered `CTriple.weakCasPtr_bind` as `@[fsym]` (AutoConc.lean ~363); `publishWeak_spec` and `publishWeak_frame` are a bare `unfold publishWeak; fsym`

Request: fsym pick branch (Auto.lean ~4410) should also try @[fsym] CTriple rules stated on a pick-bind sequence `pick f >>= fun c => liftMem (op c ..) >>= g` (needed for weak cmpxchg choice 1). Coordinate with the CSL lane, which may write the rule first.
- CSL #20 (2026-10-14): the rule exists on codex/csl-s4-followups: `CTriple.weakCasPtr_bind` (ZigLean/Sep/Full/AtomicRules.lean,
  end): `CTriple (aptsE p v) (pick (weakCasPtrCount 8 p v) >>= fun c => liftMem (cmpxchgWeakPtrAt c succ fail 8 p v new) >>= g) S`
  from `hn : CTriple (aptsE p new) (g none) S` and `hs : CTriple (aptsE p v) (g (some v)) S` (side triples, not facts). Not
  @[fsym] yet. Regression sep-auto/Conc publishWeak_spec applies it by hand (WORKAROUND comment); when the pick branch tries
  pick-bind rules, register it and make the regression a bare `fsym`.
- CSL #20 (2026-10-14) CORRECTION: NOT a flake. The one failure of sep-auto Views `fact_left` ("unknown metavariable"
  at `fsym_entail`) in the S4 gate ran against a stale Auto.olean right after a merge (check.sh does not build);
  green once built. No engine issue. (Lesson: build before running checks after a merge.)

<a id="row-allocator-creation-admissibility"></a>
### #allocator-creation-admissibility Bind allocator creation admissibility to the visible instance claimed

Status: **open**. Requester: Task10 allocator-creation soundness review.

Note: Existing family/proof-binder controls remain in Fixture.lean. AllocatorApplications.lean now kernel-checks225theorems and passes actual extraction assertions for exact/mismatched dependent arguments, False/Holds/scoped lets, local type aliases, higher-order/polymorphic forwarding, direct projections, type/conclusion indices, raw recursor branches and unknown callbacks. Named foreign creation diagnostics identify zero-based contract argument positions, including the [2,0,1] visible-role mapping; a direct admitted spec0 cannot mask hidden spec1. Memo identity retains exact local scope, closed expression and pending arguments/projection context. Full proposition-alias arity and checked projection-lambda authentication prevent speculative premises and duplicate holder scans. Unsupported parameterized type-valued projector cases conservatively reject; fresh applications remain unbound until actual created-result binding. Dynamic acceptance still requires the real fsym-produced FAdmit exact-argument versus differing-argument pair (coordinator PR400 comment6214104509); arbitrary local Holds/False cannot bind it. The independent Page constant-precondition companion does not implement that future engine hook. No new judgment or tactic. Arena creation remains a subsequent instance obligation.

Progress: Maintainer chose exact applied-argument admission (PR400 comment6209913710, 2026-10-16). Only an exact original root FAdmit hypothesis or closed checked let binds parameter-dependent admission; False/Holds contexts do not suffice. Native sequential/concurrent Page creation and actual PageLinux.mem0 admission compile for every placement and arbitrary input stream. The preserved183-theorem/73-module audit and missing-companion controls retain their original source bindings; the main3d4 changed-root refresh passes197theorems and clean complete proof/type closures for all new native/Page helpers. Unused per-start wrappers were removed after PR434 MAIN. An actual187-theorem application audit exposed a draft memo collision that skipped let/lambda bodies; original evidence is preserved. The repaired scope/context-aware collector passes a fresh225-theorem kernel audit and all application controls, including exact direct/let/projection positives and mixed admitted-zero/unadmitted-one rejection. These are metadata controls, not kernel-unsoundness evidence or real FBA acceptance. After actual PR477/397 MAIN, native existing FStepIn.bumpAllocs/push bodies preserve both original statements. Source8f1eff842 on main68b8 passes fresh9/17-root kernel audits, raw sequential/concurrent Page complete BODY+TYPE closures9128/9232nodes with no legacy judgment, Strength or step adapter, exact companion positive/absence controls and strict17nonruntime/zero skips/source gaps. All direct Mmap importers compile; historical failing raw-closure evidence remains separately bound. Real FBA creation, exact fresh-result binding, ListsPage client-root coverage and the paired real producer/checker gate remain open. F2 require-fixed remains nonzero until real positive FBA AND Page acceptance are wired. No Auto/registry change, hand seed or per-FBA facts lemma; F2 is not fixed.

Request: Keep the existing FTotalTriple/FAdmit framework. An existential nonvacuity witness for a parameterized creation theorem does not establish admissibility for every visible instance: admissionFamilySpec n has own = lift(n=0), a total creation triple from lift(n=0), and a valid witness choosing zero, while FAdmit(lift(1=0)) is impossible. Retain the actual applied visible contract arguments and require checked FAdmit of the creation precondition at those exact arguments. A parameterized client carries that same admission predicate, not a second hand-stated domain. Derive actual arguments/resources from translated initialization with general fsym and start-memory rules; PR409 owns generic struct encoding/splitting support. Do not require admission for invalid raw pointers, silently select one convenient family member, erase impossible or dependent premises, hand-write client admission walks/seeds, or weaken the contract.

<a id="row-admission-at-state"></a>
### #admission-at-state Expose exact FAdmit side goals from the currently held full state

Status: **open**. Requester: Task10 / coordinator PR400 comment6211941344, 2026-10-16.

Note: Coordinator decision https://github.com/riventic/air2lean/pull/400#issuecomment-6211941344. Current memFactsOf considers single atoms and ordered pairs and atomFacts matches exact head keys; pre_mfact is only an ordinary rule. The approved target-aware feature reuses the existing state planner instead of changing that registry. Keep unbound_admissibility fail closed until real instance evidence verifies.

Progress: APPROVED general engine feature; no existing hook. PR409, fsym part2 and arena-retain are on main3d4. Implement as a separate fresh-main small engine PR, without stacking/copying those branches. The independent native Page global-start companion uses existing Init/At rules and a constant precondition, so it does not supply this target-aware side-goal feature. Dynamic FBA initializer/fresh-result admission and the real paired producer/checker regression remain pending. Source/API analysis is not a new kernel-checked failure of a translated FBA proof; no Auto edit has been made.

Request: Add ordinary library lemma FAdmit.of_holds with exact goal Holds m r rF -> (P ⋆ R) r -> m.FSeq -> FAdmit P. When existing fsym encounters FAdmit X as a contract-use side goal, plan X ⋆ ?R against the CURRENT held assertion using the existing planner and frame rule, retaining the actual dependent arguments and context. Add a sep-auto regression with actual state/frame and mismatched-argument rejection. After this feature reaches main, require a paired real contract-call regression: fsym-produced FAdmit(P actualArgs) through FAdmit.of_holds must be accepted by the existing extractor at exactly those arguments, while admission for differing arguments and arbitrary local Holds/False contexts must reject. This producer/checker integration gate is required for dynamic initializer-dependent instance acceptance (coordinator PR400 comment6214104509); an independent constant-precondition Page global-start proof does not discharge it. No wildcard MemFacts, new registry, judgment, tactic, proof template, per-allocator facts lemma, fabricated seed or permissive claim-gate fallback. Implement only on main after PR409, fsym part2 and arena-retain have landed; do not stack or copy those branches. F2 remains open until real FBA/Page acceptance and all binding controls pass.

<a id="row-conc-base-owned"></a>
### #conc-base-owned Direct full-state ownership facts and pure concurrency vocabulary

Status: **open**. Requester: Codex Task 01 / L12.

Progress: FOwned.legacy and both applications of the legacy Owned rules are removed; full-state fork/join use generic memory, heap and access-clock facts. Conc.Base contains pure vocabulary. LocsKeep and its consumers remain legacy-to-retire in Conc.LockBase and the lock modules; BlkStep, Keep and Grows also remain legacy. The legacy Owned.fork/join proofs still duplicate facts now available from Conc.Base.Threads and should reuse them in the follow-on retirement work.

Request: Task 01 stopped because Full/ThreadOwned derived fork/join through the legacy Owned judgment from Conc.Csl. PR #390 records the coordinator's approval to replace that dependency with generic memory/heap/access-clock facts, derive the existing FOwned rules directly, and relocate pure vocabulary into Conc/Base. Owned remains in the retiring layer; WP.liftMem_setTls remains on the WP side. This is distinct from fowned-bridges, which concerns fsym stepping through WP.liftMem_fowned* and remaining ofSeq call sites.

Workaround sites: `ZigLean/Conc/LockBase.lean`, `ZigLean/Conc/Lock.lean`, `ZigLean/Conc/LockRules.lean`, `ZigLean/Conc/Word.lean`, `ZigLean/Sep/Full/LockWord.lean`, `ZigLean/Conc/Csl.lean`

Deletion plan: Retire LocsKeep through the existing FStepIn/RestStep machinery and restate its lock consumers on FStepIn without weakening their contracts. Reuse the generic Conc.Base.Threads facts in the remaining legacy Owned.fork/join proofs while that layer remains, then delete those rules with Conc.Csl. If the lock migration needs a contract change, stop and post the exact obstruction with a counterexample for the maintainer. Keep LocsKeep legacy-to-retire and every real consumer in the structural gate until actual retirement.

<a id="row-thread-loop"></a>
### #thread-loop Loop rule for a Zig.loop in a thread (FTTriple)

Status: **closed**. Requester: lists (aebd7d147de788626).

Progress: DONE PR #319 (codex/fsym-thread-loop: Full/ThreadLoop)

Request: the thread backend has no loop rule for a `Zig.loop` in MemM. The tutorial needs `FTTriple (list X hd xs) (reverse hd) (fun r => list X r xs.reverse)`; `fsym [reverse_loop]` (FTotalTriple via loop_ghost, Proofs/Lists/Linked.lean) stops at `StateT.run (loop reverse.loop6 ...)`. Wanted: FTTriple.loop / FTTotalTriple.loop_ghost (TLogic loop rules, same invariant), or ThreadLocal of `loop` from the body's locality under an invariant.

<a id="row-errok-native"></a>
### #errok-native WP walk of raw MemM steps in a partial protocol: the error leaf (Proto.ErrOk) from library *_native facts

Status: **open**. Requester: S4 (audit soundness-2026-10-14) / critic run 15.

Progress: open (workaround)

Request: Since S4 a partial protocol's step may throw only errors at which the native program stops (`Proto.ErrOk`: `nativeStops` or `.stackOverflow`). A step through an ownership bridge (`WP.liftMem_fowned*`, `callMC_fownedS`) gets this from its thread triple, so `fsym` walks need nothing new. The protocol mains that step over memory the invariant describes directly (raw `WP.liftMem`/`WP.liftM`/`WP.callMC`, no `FOwned`) are hand walks, and each step passes `ErrOk.of_run rfl <fact>` with a library outcome fact (`alloc_native`, `store_native`, `free_native`, `load_native_of_decode (Decodes.of_curBytes …)`, `atomicStoreAt_native_single`, `atomicLoadAt_native_single`, `futexWait_native_of_curBytes`, `tlsEnter_native`, …) whose premises come from the invariant. Wanted: `fsym` walks these mains (raw `liftMem` steps as WP rules), solving the error premise by `ErrOk.of_run` with the library `*_native` facts as side-condition rules and the invariant's facts as their premises. Also: `WP.liftMem_liftR` does not unify with `ConcM.liftMem (StateT.lift boom)` for a user `Result` constant (trace: `WP rule @WP.liftMem_liftR: command`), so its `herr` premise is not exercised by any walk.

Workaround sites: `Proofs/Atomics/Relaxed.lean`, `Proofs/Cancel/Group.lean`, `tests/roadmap/futures/Futures/Proofs.lean`, `tests/roadmap/thread-locals/ThreadLocals/Leak.lean`

Deletion plan: when fsym walks raw liftMem steps of a protocol main and discharges `Proto.ErrOk` from the library `*_native` facts, replace the hand `WP.bind (WP.liftM (ErrOk.of_run rfl …))` chains in the workaround sites with `fsym` and delete the explicit `ErrOk.of_run` arguments; the invariant facts (`flag_single`, `flag_vals`, `status_bytes`) stay as the proofs' invariant.

<a id="row-premise-runtime-fallback"></a>
### #premise-runtime-fallback Conservative runtime-source premise fallback

Status: **open**. Requester: Task 04 premise attribution / coordinator.

Note: Coordinator decision: https://github.com/riventic/air2lean/pull/418#issuecomment-6214104038. This records an assurance-tooling approximation, not a new proof judgment, tactic or per-client exception.

Progress: PR #419 restores conservative source estimates without premise reductions. Declaration-level precision remains separate from this repair, tracked by draft PR #418 and its future fresh-main precision split.

Request: Please add an engine-ledger row (slug id, e.g. `premise-runtime-fallback`), open, citing the precision PR as the plan, and label the tutorial additions as conservative estimates, as you propose.

Workaround sites: `scripts/premises.py`, `tutorials/allocation-failure/README.md`, `tutorials/concurrent-clients/README.md`, `tutorials/cross-target/README.md`, `tutorials/external-contracts/README.md`, `tutorials/first-proof/README.md`, `tutorials/generic-containers/README.md`, `tutorials/memory-safety/README.md`, `tutorials/mutable-arrays/README.md`

Deletion plan: Track replacement in https://github.com/riventic/air2lean/pull/418 and its fresh-main precision split. Remove broad runtime-source token attribution and the corresponding conservative tutorial additions only as reviewed family-complete declaration attribution replaces them, with fresh kernel-checked dependency graphs and source fingerprints. Every modeled semantic route needing a removed premise must reach an authenticated carrier; unresolved, new or changed routes retain fallback. A reachable carrier absent from the coarse baseline is a hard error. Regenerate the index through the official pipeline, update the exact tutorial premise lists and run scripts/tutorials.py lint, validate retained-premise and dropped-premise controls, and remove resolved workaround sites. Keep this row open while the broad fallback remains.

<a id="row-current-thread-subst"></a>
### #current-thread-subst A substituted `m.current = t` breaks the caller's rule terms (kernel type mismatch)

Status: **open**. Requester: STD-05 step A (codex/std-retire-futex-rules, PR #437).

Progress: open (workaround)

Request: `fsym [r]` elaborates the caller's rule term `r` in the goal's context, then `destruct` substitutes a hypothesis `hc : m.current = t` away (`t := m.current`). A rule term that took `hc` (e.g. `FEvent.wp_osWait hE rfl hg hgo hc hi hlive`, whose premise is `m.current = t`) is then applied at the substituted type, and the kernel rejects the proof ("application type mismatch: argument has type m.current = t but function has type m.current = m.current → …") instead of `fsym` re-elaborating the term against the substitution (`refreshUser`, `substs`) or failing cleanly. Wanted: `refreshUser` maps the caller's terms through every substitution of the run, including one that eliminates a variable a term's argument mentions.

Workaround sites: `tests/roadmap/sep-auto/SepAuto/WPOsFutex.lean`

Deletion plan: when fsym re-elaborates or maps the caller's rule terms through its substitutions, delete the `subst hc` before `fsym` in `WPOsFutex.event_wait` and pass `hc` to the rule again.

<a id="row-word-family-views"></a>
### #word-family-views A word's plain rules are reached only under the word's own head

Status: **open**. Requester: arena-retain (coordinator review of #446).

Progress: open (workaround: 14 instances)

Request: **The plain-access rules of an owned word are stated once, for `tptsE p tg v` (`AtomicPlain.lean`), but `fsym` cannot reach them from the words `aptsE`, `apts` (`tptsE` at `some (p.off.toNat, 8)`, definitionally) and `wptsE`, `wpts` (`∃ tg, tptsE p tg v`) through views.** Tried on codex/arena-engine: the five `tptsE_*` rules `@[fsym]`, the views word → `tptsE` and `tptsE` → word `@[fsym_view]` (the existential one as `FAssn.ex fun tg => tptsE p tg v`), no instances. A store at an offset next to another word of the block fails: in `aptsE p x ⋆ aptsE (p.add 8) y`, at `store 8 (p.add 8) a`, `regionStoreAdd` is tried before `tptsE_store` and notes `up (regionIn p ?A ?S ?K ?a ?bs)` as wanted before `tptsE (p.add 8) ?tg ?v`; `viewAtoms` takes the wanted atoms in that order and gives both words of the block the one-way region view (`aptsE_view`), so the store goes on over regions and the return's `aptsE p none` has no atom (the tag is lost). Probe of 15 cases: the same for a store of a value, of a packed struct and of bytes (`storeBytes_region`) at `p.add 8` into each word, a load of an `Option Ptr` from a `wptsE`, a packed load from `apts`/`wpts` (`regionLoadWrittenAdd`, heartbeat limit) and a load after a store into an `aptsE` (12 of 15 fail; only the `BitVec 64` loads from `apts`/`wpts` and a `BitVec 64` store then load into a `wpts` pass). Needed: `viewAtoms` applies a view that loses nothing (one whose converse is a registered view: word ↔ `tptsE`) before a one-way view (a word as a region), whichever wanted atom comes first; or the rules of the atom that owns the target before the region rules (#57). Workaround: each word has the family's rules under its own head, `<word>_<rule>` (`aptsE_load`, `aptsE_storeBytes`, `aptsE_store`, `apts_load`, `apts_store`, `apts_loadPacked`, `apts_storePacked`, the same for `wptsE`/`wpts`), each one to three lines from the `tptsE_*` rule.

Workaround sites: `ZigLean/Sep/Full/AtomicPlain.lean`

Deletion plan: once `viewAtoms` prefers the views that lose nothing (regression: the offset cases `store_beside_*`/`load_beside_*` of `tests/roadmap/sep-auto/SepAuto/AtomicPlain.lean` pass with only the `tptsE_*` rules registered), register `tptsE_load`, `tptsE_storeBytes`, `tptsE_store`, `tptsE_loadPacked`, `tptsE_storePacked` as `@[fsym]`, add the views word ↔ `tptsE` (`@[fsym_view]`), register `tptsE_view`, a `facts_tptsE` and `OwnsPtr.tptsE` as a provider, and delete the 14 instances and `wptsE_of`.

<a id="row-fold-recursive-pred"></a>
### #fold-recursive-pred Fold a recursive user predicate to match a call rule's precondition instead of unfolding the callee

Status: **open**. Requester: chore/l4-controls (PR #449, critic 27).

Progress: open (no workaround: ListsPage's right client is `Lists.Client.buildThenFree [7]`, proved by the library theorem)

Request: A client `match ← push a none 7 with | .error _ => pure () | .ok p => freeAll a (some p)` (from `I.own ⋆ (fees I φ 1 ⋆ vtR vtp fns.toList) ⋆ plain` back to itself) is not walked by `fsym [push_spec ctx vtp fns I e φ none 7 hfit h, freeAll_spec ctx vtp fns I e φ (h := h)]` (Proofs/Lists/Alloc.lean). After `push`, the state holds the new node `node I φ p 7 none` as its unfolded atoms (`bclaim`, `bshare`, `regionIn`, `I.tok`, `pts p 8 none`, `pts (p.add 8) 4 7`); `freeAll_spec`'s precondition is the recursive list predicate `list I φ (some p) [7]` (`Lists.Linked.list`: `∃ q, ⟪q = none⟫ ⋆ node …` for one item). `fsym` does not fold the atoms into `list I φ (some p) [7]` to apply the call rule; it unfolds `freeAll` and stops at `StateT.run (loop (freeAll.loop5 ⟨ctx, vtp⟩) freeAll.again5) { p := some p }` (unsolved goal, no loop rule chosen). Wanted: when a call's rule has a precondition that is a user predicate (a recursive `list`/`seg` instance at a concrete list, or any `abbrev`/`def` of atoms), fold the matching state atoms into it (unfold the rule's precondition to atoms for the match, as the planner does for postconditions) and apply the call rule before unfolding the callee. Reproduction: the snippet above as an `example` with `import Proofs.Lists.Alloc` and `unfold pushThenFree; fsym […]` (scratch F1.lean on chore/l4-controls).

<a id="row-seen-floor-sync-retirement"></a>
### #seen-floor-sync-retirement Finish sync multi-waiter contracts and retire retained old Word exports

Status: **open**. Requester: Task06 / PR #397.

Note: Historical foundation reports showed Zig.Full.FEvent.MStep.nextMsg, Zig.Full.FEvent.MStep.atomics, Zig.Full.FCond.MStep.nextMsg and Zig.Full.FCond.MStep.atomics reaching Zig.Conc.Word.Op, BlkStep or Conc.LocsKeep. Those reports retain their original bindings. Current source derives these helpers from actual runs and the native frame/map boundary. AMap/shapes alone cannot imply full outside-record preservation on malformed overlapping arrays; native Step.locs uses actual array equations instead. The kernel controls expand the two former obligations without importing the old record and reject changed, retired and reindexed overlapping records. Handoff invariant mathematics is factored once into native lemmas. Takeover6277249661 authorizes deleting the six unused preservation wrappers; no external retention reason was found. The residual old Word-contract roots must remain unfiltered and separately disclosed; no whole-module strict-zero claim hides them. Corrections6269584785 and6273571981 supersede after-foundation ordering6268589114: no transitional exception, native producer/consumer and shared Step/Fits retirement in this PR before READY. Source-only non-implication and ABA scenarios remain distinct from checked runtime counterexamples. Earlier decisions6264023136/6264821278 and source-only ghost-support proposal6265341146 remain recorded.

Progress: PR397 implements permanent AMap/Word floor and Fresh transport, actual native primitive producers, WordRules callbacks and Event/Cond MStep consumers. The approved joint LockWord.Step.locs cut uses its actual unchanged/first-address replacement/first-address append equation, with native first-index/full-record and new-record lemmas; every direct producer and internal locIdx result migrates together. The native modules and actual Sync/Threadsync Handoff clients compile, and malformed overlapping/duplicate-record controls check. The source/artifact-bound a0fe64d8a audit established zero registered legacy or adapter dependencies for native producer/consumer and real Handoff client paths, retaining all roots including thirteen old exports. Takeover6277249661 removed six exports with no external callers: Protocol.U_frame/U_own/keepK_of and Word.keepK_fstep/keep_lockWordStep/keep_waiters. Fresh source/artifact-bound qualification at65138df91 retains all2364 declaration roots,1703 theorem records and89 fresh kernel replays; every native producer/consumer and real Handoff client remains legacy-free, and all retained theorem statements match the prior report. Exactly seven old roots remain visible: Word.BlkStep.eq_set, Word.Op.block/fpAt/lockLoc/rest/word and FLock.Inv.wordOp. The earlier thirteen-root count is historical. Generic actual read/fork validity-history lemmas and direct FStepIn.afterAlloc fields preserve their headers. Existing Event/Cond singleton contracts and remaining old Word contracts stay open debt; this is not whole-module strict-zero, completion or reclassification.

Request: Complete the existing full-state Event/Cond multi-waiter contracts using caller-local seen floors, selected-subset wakes and sufficient actual broadcast counts. Derive general Cond admission/accounting over all en/ld/reg phases and finite ghost-admitted support. PR397 ruling6264821278 selects fewer than 2^32 epoch increments during save-to-enqueue, discharged by existing client cost/admission resources, with unconditional safety and the exact singleton instance. First kernel-check the source-only epoch-ABA one-round/iteration schedule fact; it is not a checked singleton refutation. Do not require every translated implementation to prove the rejected sleeping-thread liveness assumption. Keep existing client results and derive singleton/owned-ledger instances. Native-ID capacity, reservation and physical-exit accounting are the separately approved D2 change. Before READY, qualify the coherent native producer/consumer boundary required by corrections6269584785 and6273571981: actual primitive-run RestStep, actor-normalized AMap, counter, validity, history, result, exact-index and raw-block facts; WordRules callbacks; both Event/Cond MStep families; every affected Handoff client. Preserve exported Event/Cond/Impl/Handoff statements and strength. No client premise, weaker result, adapter, renamed record, reclassification or module-specific proof walk; do not hide capacity in Fits.

Workaround sites: `ZigLean/Conc/Word.lean`, `ZigLean/Sep/Full/LockWord.lean`, `ZigLean/Sep/Full/Word.lean`, `ZigLean/Sep/Full/WordRules.lean`, `ZigLean/Sep/Full/Event.lean`, `ZigLean/Sep/Full/Cond.lean`, `Proofs/Handoff/Protocol.lean`

Deletion plan: Before PR397 is READY, remove the obsolete Word.Op/LocsKeep/BlkStep dependency from every actual new native producer and consumer path, including the shared Fits.stable -> Full.LockWord.Step boundary. Cover preparation, load, all signed/unsigned RMW orders, strong and weak CAS including spurious failure, wait and OS-wait, every WordRules/Event/Cond consumer and retained Handoff result. Check every changed root's actual body and full type, including inherited dependencies, against fixed source/artifact bindings. The inline native Step.locs field must retain both former obligations; retained producers prove its stronger actual array equation. No AMap-to-LocsKeep conversion is allowed. The six unused Word/Protocol preservation exports identified in6277249661 are removed now, rather than deferred as frozen compatibility wrappers. Remaining Word.BlkStep/Op projections and FLock.Inv.wordOp are reported as the old Word-contract family, never as native; retire that family together with its shared legacy producer contracts after their other old consumers migrate. This boundary does not close the row: remove Event/Cond one-waiter/newest-HB workarounds only after general contracts, singleton/owned-ledger instances and multi-waiter regressions are kernel checked. Close only when all listed workarounds and retained old exports are gone and the applicable strict new-fact graph passes.

<a id="row-thread-store-sized"></a>
### #thread-store-sized A store of a packed struct into an owned word in a thread

Status: **closed**. Requester: arena-retain (loop66 of the retaining reset).

Progress: DONE on codex/arena-reset-retain: provider `ThreadLocal.store_sized` (AutoThread.lean); regression `tests/roadmap/sep-auto/SepAuto/Threads.lean` (`packedWord`, `packedAtomicWord`: both fail without the provider)

Request: **A store of a packed struct into an owned word had no thread rule** (`CTriple`/`FTTotalTriple`: `wpts_storePacked` through `FTTotalTriple.ofSeq`): its `ThreadLocal` side goal had no provider, since `ThreadLocal.store_lawful` needs `LawfulEnc` (a packed struct's encoding is its bits', with none) and `ThreadLocal.store` asks for `OwnsPtr P p (Enc.encode v).size`, which the word's provider (`OwnsPtr.wpts`, 8 bytes) does not unify with. The arena's `reset` stores a kept node's new size (`Node.Size.fromInt`) into its `size` word: the rule over a region (`region_storePacked_wpts`) applied instead, through the one-way view of every word of the node's block as a region, so the `end_index` word stayed a region and the node's parts owned bytes (`bytesAt`). Fixed: `ThreadLocal.store_sized`, the store's bytes the `n` the precondition owns, with `(Enc.encode v).size = n` an arithmetic side goal after `n` is fixed (`reduceEncodeVia`).

<a id="row-final-match-greedy"></a>
### #final-match-greedy The planner's final match takes the first atom that unifies, also for an existential a later atom fixes

Status: **open**. Requester: arena-retain (reset's retaining modes).

Progress: open (workaround: the lists as `FreeList` atoms at `reset`'s level)

Request: **The final match of a plan (`closeEntail`, Auto.lean "final match") is greedy**: each atom of the target is matched with the first state atom that unifies, and an assignment is never undone when a later atom then finds none. The arena's `loop66_ct` asks for `Inv66 … ⟨ok, 0, it⟩`, whose two lists unfold to `aptsE pu xu ⋆ (∃ ns, Chain CI true (ns.map NodeV.full) xu ⋆ FreeCl CI ns)` and the same for `pf xf`; against a state that holds both lists opened (`Chain … ns x ⋆ aptsE pf x ⋆ Chain … ns' x' ⋆ aptsE pu x' ⋆ FreeCl CI ns ⋆ FreeCl CI ns' ⋆ …`) the plan fails with "the state has no atom for `Chain CI true (ns.map NodeV.full) x'`": the used list's existential is already the free list's `ns` when its `Chain` is matched (inferred: its `FreeCl CI ?ns` took the free list's `FreeCl CI ns` first). With the state's two `FreeCl` atoms swapped the same entailment closes; the same shape over two opaque predicates closes in either order. Reproduction: `fsym_entail` on that `EUpd` (scratch arena-retain9/exp/GMX.lean on codex/arena-reset-retain). Needed: match the atoms whose candidates are fewest first (most constrained), or retry a failed atom first with the assignments of the atoms before it undone.

Workaround sites: `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean`

Deletion plan: drop `attribute [local fsym_atom] FreeList` of `reset_retain_capacity_ct`/`reset_retain_with_limit_ct` and pass `count_spec` for `count_free` (delete `count_free`) in each ArenaSpec*.lean once the final match does not commit to an atom that a later atom's match contradicts.

<a id="row-undecided-eq-branch-cost"></a>
### #undecided-eq-branch-cost (perf) A walk through an undecided equality branch of a computed value exceeds the budget

Status: **open**. Requester: arena-retain (loop66 of the retaining reset).

Progress: open (workaround: the limit split before the walk)

Request: **(perf)** The arena's `loop66` body computes a kept node's size `adj = (24 + v) &&& ~1` from a list's limit `v` and branches on `adj == 24` (give the node back) before the long keep path (resize in place, or a new node from the child). Walked once with the branch undecided, both list indices time out at 4M heartbeats each (one file, 428 s, 11 GB peak) and one index alone is killed at 16M (12 GB guard, 315 s); split before the walk on `v.toNat < 2` (which decides the branch) both paths of both indices take 247 s and 7 GB together. Suspected: the negative branch's fact `¬ adj = 24` (a disequality of a masked value) makes every later `omega` problem of the keep path split. Needed: the walk's cost with an undecided branch near that of the split cases (a disequality fact that `omega` does not split when the goal does not need it).

Workaround sites: `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean`

Deletion plan: delete the `by_cases hsm : v.toNat < 2` before `fsym` in `loop66_c0` and `loop66_c1` of each ArenaSpec*.lean once one walk of the body with the undecided branch stays within the budget.

<a id="row-per-translation-walks"></a>
### #per-translation-walks The same std code translated for several targets is proved once per translation

Status: **open**. Requester: coordinator (critic run 31, arena retaining reset).

Progress: open (workaround: each ArenaSpec*.lean repeats the statements and walks)

Request: **The arena's three translations (`AllocArena.ArenaLinux`, `ArenaMacos`, `ArenaFixedLinux`) are separate Lean modules with their own constants and types**, even where the source is the same: `heap_ArenaAllocator_reset`, `.loop66`, `.loop78`, `heap_ArenaAllocator_deinit`, `countListCapacity` are byte-identical text in the three files (diff of the `reset` section: empty), but `heap_ArenaAllocator_resetLocals`, `heap_ArenaAllocator_resetExit`, `heap_ArenaAllocator_deinitLocals`, `heap_ArenaAllocator_State` are three distinct structures and inductives, and the generated functions three distinct constants. A specification is stated over a module's own types (`Inv66 … (s : heap_ArenaAllocator_resetLocals)` reads `s.local55`; `Exit66`/`Exit78`/`Exit9`/`Exit19` match the module's exit constructors `.br65`, `.br77`, `.br8`, `.br18`; `tables` names the module's entries) and proved by `fsym` unfolding the module's concrete body, so it cannot be stated once and instantiated: there is no common type to state `Inv66` over, and no shared code for one walk. After renaming the namespaces, `ArenaSpecMacos.lean` and `ArenaSpecFixed.lean` differ only in their doc comments (17 lines), and from `ArenaSpec.lean` only in its extra M01 statements; the module-independent layer (invariant, updates, ghost part, kept nodes) is already shared (`AllocArena/Core.lean`, `AllocArena/Reset.lean`). Needed: the translator emits std code that does not depend on the target once, in a module the target translations share (target constants as parameters, ledger mechanism M10-style generic code), or a module-generic presentation of a translation (a record of its types and functions with the defining equations, which `fsym` walks and each translation proves by `rfl`), so that a specification and its walk are stated once over it.

Workaround sites: `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean`

Deletion plan: state once, in a shared module over the generic translation, the defs and theorems that ArenaSpecMacos.lean and ArenaSpecFixed.lean repeat from ArenaSpec.lean (main's 24: `free_ct`/`free_spec`, `resize_ct`/`resize_granted_ct`/`remap_ct`/`resize_spec`/`remap_spec`, `al`, `tables`, `child_decode`, `count_loop`/`count_spec`, `Inv19`/`Exit19`/`loop19_step`/`loop19_ct`, `Lists9`/`Inv9`/`Exit9`/`loop9_step`/`loop9_ct`, `deinit_ct`, `reset_free_all_ct`/`reset_free_all_spec`; and the retaining reset's 15: `count_free`, `Inv78`/`Exit78`/`loop78_step`/`loop78_ct`, `Inv66`/`Exit66`/`loop66_c0`/`loop66_c1`/`loop66_step`/`loop66_ct`, `reset_retain_capacity_ct`/`reset_retain_with_limit_ct`/`reset_retain_capacity_spec`/`reset_retain_with_limit_spec`), and make each ArenaSpec*.lean an instance (only a walk over code that differs between translations, the patched `free` and `resize`, stays per module), once the translator emits the shared std code once or fsym walks a module-generic presentation.

<a id="row-arena-retained-capacity"></a>
### #arena-retained-capacity The retaining reset's retained capacity is not stated

Status: **open**. Requester: coordinator (takeover review of PR #468).

Progress: open (M01 register row)

Request: **`reset_retain_capacity_spec` and `reset_retain_with_limit_spec` have the same postcondition as `reset_free_all_spec` (`own (e+1) ⋆ epTok`), so they prove that both retaining modes preserve the arena's ownership contract and nothing about the capacity kept.** The internal `loop66_ct` gives every node back to the child except at most one per list (kept as it is, shrunk or grown in place, or replaced), but `Kept`'s `sz` is existential with no link to the limit `l` or to the list's capacity, and the specs forget it. Needed: strengthen `Kept` to link `sz` to `l` and the list's capacity (`capOf`), and state the retained capacity in `reset_retain_capacity_spec` / `reset_retain_with_limit_spec` (what Zig's `reset(.{ .retain_capacity })` and `.{ .retain_with_limit = l }` promise), for every translation. No statement is weakened meanwhile: docs and the README claim only the ownership contract.

Workaround sites: `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean`

Deletion plan: state the retained capacity in `reset_retain_capacity_spec` and `reset_retain_with_limit_spec` of each ArenaSpec*.lean (after the per-translation-walks row, once in the shared module) by linking `Kept`'s `sz` to the limit and the list's capacity, then close this row and drop the 'not stated' wording from docs/alloc-arena.md, docs/allocator-identity.md, tests/roadmap/alloc-arena/README.md and register row M01.

<a id="row-region-end-opt-in"></a>
### #region-end-opt-in The owned-region end bound is a per-file opt-in fact

Status: **open**. Requester: coordinator (takeover review of PR #468).

Progress: open (performance opt-in)

Request: **`attribute [local fsym_facts] MemFacts.region_end` (ArenaSpec.lean, ArenaSpecMacos.lean, ArenaSpecFixed.lean, before `Inv66`) lets `fsym` derive that an owned region ends at an offset of at most `2 ^ 63` (`ZigLean/Sep/Full/OwnedBound.lean`).** The retaining reset's `loop66` additions need it for the overflow-checked sums, and it is switched on by hand per file because making it a default fact costs every other walk. Needed: `fsym` derives or demands the bound only where an arithmetic side goal asks for it (on-demand facts from the state's owned regions), so no proof opts in.

Workaround sites: `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean`

Deletion plan: delete the three `attribute [local fsym_facts] MemFacts.region_end` lines (ArenaSpec.lean, ArenaSpecMacos.lean, ArenaSpecFixed.lean) once `fsym` supplies the owned-region end bound on demand (or as a default fact without a measurable cost).

<a id="row-l10-native-lock-step-contract"></a>
### #l10-native-lock-step-contract Native lock-step contract before semaphore resource-transfer walks

Status: **open**. Requester: L10 semaphore migration (Task 07; coordinated with L11 and Task 06).

Note: Program-walk qualification also requires a native full-state primitive-rule closure; no legacy frame-relation adapter may remain in the proof dependency graph.

Progress: open. Native invariant repartitioning is provided. #397 replaces `LockWord.Step.locs : LocsKeep` with native array equations (row seen-floor-sync-retirement). The semaphore contract and the translated clients remain.

Request: A generic semaphore fsym holder-transfer wrapper over FLock.Fits would inherit Fits.stable -> LockWord.Step.locs : Conc.LocsKeep. The complete resource can already be repartitioned natively at FLock.Inv, but adding a new Step-typed wrapper would grow the legacy proof closure. Replace the native primitive producers and their Full consumers together with permanent native frame/location facts preserving all original guarantees, including location retirement/reindexing and unaffected histories. Do not rename or adapt the legacy record, delete fields without replacement, add a premise, or hand-walk the semaphore. Task 06 PR #397 separately retires coherent Word/WordRules and Event/Cond MStep boundaries before READY; that does not by itself promise retirement of LockWord.Step.locs. The final held/outside condition-signal rule must retain a holder's complete resource. After the actual native APIs land on main, Task 07 supplies SemImpl and translated instances/clients using fsym, retaining all six SemCounter/Mailbox spec, safety and completion statements and their mutation controls.

Deletion plan: Close after native lock primitive producers and Full consumers preserve the original Step guarantees without registered legacy dependencies, the generic fsym resource-transfer and held/outside signal walks pass strict actual term-and-type closure, and Task 07's translated Semaphore/SemCounter/Mailbox migration is complete. This row authorizes no transitional code.

<a id="row-typed-region-release"></a>
### #typed-region-release Release a complete block from typed fields while preserving the native stack refund

Status: **closed**. Requester: Task14 full-state allocator client.

Note: The qualified controls release arbitrary typed word/slice fields using physical authority metadata, preserving the original stack depth. Existing substitutions not recorded by unifyBlocks can leave a stale matching hint; such hints are skipped safely, with original side proofs retained. This does not claim complete matching for every case-based size consequence. A demanded size selects or joins whole state regions and never splits one (carve whole): splitting let memcpyRegionsAll take prefixes of both buffers in Proofs/Lists/Append.lean precise_pos instead of memcpyRegions, and the walk then exhausted its heartbeats at the following free (fix-forward after PR481). Full client and legacy retirement remain open.

Progress: Native typed-region/extent/release lemmas and approved size-aware matching use data-only hints, witness rollback, shared bounded substitution refresh, unresolved-token inference and independent original side premises. Comments6279182210/6279202049 approved active-path view progress and applied explicit-frame unification. Actual fallback whole Structs, including free_fields_stack with its exact original goal, and the full29-file official sep-auto suite PASS on f9505e4e/main578aa3b2, Auto5614ed37, guards b8bf14f3/e6cbb205. The five unchanged Proofs callers retain their earlier afc52032a/Auto f13fb21a PASS binding69afbe3b; an accepted fixed-size causal audit supports reuse, not a fresh current-source claim. Isolated A/B proved the added ordinary size attempt caused the large-state regression, so Claude6280049836 dropped fix3 and restored the whole carve function exactly to main. The separate case-fact positive remains an explicit expected failure tracked by open carve-size-probes. Fixes1-2 and all other controls remain; no cap increase, broader planner or weakened production statement. Reproduce with tests/roadmap/sep-auto/check.sh; actual report6280488414.

Request: Close by plain fsym the generic goal FTotalTriple (((up (pts p 8 e) ⋆ up (pts (p.add 8) 8 sl)) ⋆ bext b 24 .stack) ⋆ (ent t (some b) D c ⋆ sp t S (D+c))) (Zig.free p) (fun _ => sp t S D), for arbitrary e : BitVec 64 and sl : Slice, p.block = some b and p.off = 0. Reproduction: tests/roadmap/sep-auto/SepAuto/Structs.lean free_fields_stack. A typed value hides independent byte labels; actual Owns.block/Holds.bauth metadata, not a caller premise, binds these labels to the physical extent. Do not hand-walk a client, add a struct-specific free rule, drop stack tokens or weaken its resources.

<a id="row-region-memset-read"></a>
### #region-memset-read Infer a region read after a defined-value memset

Status: **closed**. Requester: Task14 full-state allocator client.

Note: The generic providers retain positive encoding size, nonnegative whole-item offset and exact fit; ordinary load alignment checks remain. Memset itself supports zero-sized/count cases. Full FBA client and legacy retirement remain open.

Progress: Implemented by ReadsAt.regionMemset/regionMemset0 through the existing region/extraction/decode lemmas. Reproduce with tests/roadmap/sep-auto/check.sh: Region.memset_read and Region.memset_word_reads cover byte and multibyte initial/interior loads. No new provider kind or engine change.

Request: Close tests/roadmap/sep-auto/SepAuto/Region.lean memset_read by fsym: for arbitrary p,A,S,K and bs.size=4 and v:BitVec8, FTotalTriple (up(regionIn p A S K 1 bs)) (do memset 1 p 4 (some v); load (BitVec8) 1 (p.add 3)) (fun r => ⟪r=v⟫ ⋆ up(regionIn p A S K 1 (memsetBytes 4 (some v)))). The generic fix must cover every lawful encoding/value/count and aligned in-bounds item offset using the existing ReadsAt.regionIn, Array.extract_flatten_replicate and decode_encode path, including fail-closed empty/zero-size read guards. Do not add a byte/client-specific load rule, new provider kind, Auto edit, premise or manual code walk.

<a id="row-known-bytes-on-demand"></a>
### #known-bytes-on-demand Derive requested block-address knowledge from raw bytes without changing global store results

Status: **closed**. Requester: PR481 coordinator takeover review.

Note: Follow-up from actual FullClient on main8bb62cdd/Auto0957: a positive arithmetic-cache proof outlives its auxiliary theorem and Lean rejects reuse (report67864631, PR521 comment6302152515). The exact creator call site and invalidating snapshot were not sampled. Existing RunCaches.saveArith now pairs with closeEntail's failed outer transaction and all12 tryRule outer restores; successful attempts stay unchanged. Private unchanged FullClient87f87 with candidateAuto8229 reaches the same failed-plan/retry path without the missing auxiliary (reportf524f3df, completeleaf0636d9ee). Its generic fold/split then supplies both fields; later known-address knowledge remains unresolved, so no client theorem or legacy retirement is claimed. Whole Updates and official409-target ROOT (128Proofs) pass at1b6bccf7/main8bb62cdd, reports6da5d281/ab8dc939. Updates.failed_rule_retry is ordinary full-bytes/frame behavior, not an old-fail auxiliary reproducer. Other nested/provider/walk/selected-state rollback owners remain outside this finite repair; no global cache-lifetime closure is claimed.

Progress: The original storeBlock/storeBlock_finite posts are restored; one requested-knowledge planner precedes region planning and uses known_of_bytesAt. Approved committed-descendant retry, snapshots/fallbacks, source-first determined-block address selection, unknown-block matching and direct-update shape checks remain. Whole actual Structs, including concrete/existential/idempotence/no-request/fail-closed controls, and the full29-file official sep-auto suite PASS on f9505e4e/main578aa3b2, Auto5614ed37, guards b8bf14f3/e6cbb205. The five actual unchanged Proofs callers PASS at their original afc52032a/Auto f13fb21a binding69afbe3b; the accepted causal audit supports retaining that evidence after the final change only restores main's carve. The isolated A/B and Claude6280049836 removed the ordinary size probe while preserving fixes1-2 and the explicit case-fact expected failure. No current-source fresh-five claim or blanket full-build repeat for a head move. Reproduce with tests/roadmap/sep-auto/check.sh; actual report6280488414.

Request: Close the generic store_fields_keep_address control in tests/roadmap/sep-auto/SepAuto/Structs.lean by deriving requested known b A from nonempty bytes before typed views hide their metadata. Do not eagerly add known to global store posts: the exact old result shape is required by Proofs/Threadsync/Mutex.lean, Proofs/Sync/Mutex.lean, Proofs/Sync/SnapshotCache.lean, Proofs/Threadsync/Handoff.lean and Proofs/Sync/Handoff.lean. Use only the existing knowledge-planning mechanism and known_of_bytesAt, with exact block/address and positive-byte guards; no per-proof glue or broader leftover-resource framing. Validate the completed global-rule repair with scripts/full-build.sh.

<a id="row-wp-local-hypothesis-application"></a>
### #wp-local-hypothesis-application Apply current local proof functions during bounded WP side proofs

Status: **closed**. Requester: Task07 condition-signal and semaphore migration; coordinator481/6279583751 and confirmed order6279729681.

Note: The bounded local-hypothesis path retains stable conclusion-head filtering plus full argument unification, current-context candidates once per level, shared depth/fuel, complete proof/data closure and failed-choice rollback. It performs no new case search and preserves ordinary case-enabled behavior. The generic incoming-fact normalization uses proof-producing existing simp/False.elim, not a division-specific contradiction rule. The assigned-update synthetic control checks its raw assigned-mvar shape and completed proof; it alone does not detect the old recovered PANIC. Captured fresh actual Full compiler output must establish absence of that PANIC. Global computational definition hints use addExtra's existing named-unfold path; proof terms and specific rules/updates retain their prior classification. Task14's distinct missing-field/auxiliary and Task23 conditional-post remainders are not claimed fixed. No new judgment, tactic, premise, cache schema, provider, caller wrapper or protected carve-size probe is introduced. Main515 demanded whole-region fix remains baseline. The exact seven-file restoration remains unapplied after automatic execution review rejected it despite human approval; preserved source/recovery and no-bypass requirements remain.

Progress: Qualified in PR529: at2f1b/main737, Auto/AutoWP fe270e1f/b9839887, whole canonical WP100 jobs, both actual condition modules161 jobs and exact407-target ROOT pass. Guardf07c262a/unit16d97d42 binds1005 unchanged source/command rows; physical ROOT8e2f1fa3/logdc09702f is reused for inventory. Official SepAuto31 builds206 jobs and replays203 modules/2111 theorems with standard axioms; OneLogic8 builds132 jobs and replays129 modules/108 theorems. SepAuto's general assurance output retains3 unchanged-class float-key/test-opaque policy findings; its documented fixture gate passes, not general policy. Currentnessfc737e7a renews only3 supported stale swap recipes, retains13 runs/49 qualified artifacts, and passes official inventory write/check. At a3a634ab8/main737, focused preflight and independent framework both pass (guardb3e8ad24, logs3b2b8c45/d4af7583), fixed inputs/artifacts unchanged. Final review/simple find no actionable issue. One structural walk retains raw/normalized evidence, forwarding priority, proof-local Eq substitution and exact-type own-equation exclusion; observable controls check actual substituted data. Assigned-update/global-definition controls compile; actual fresh FBA Full/no-PANIC evidence retains its35d8 binding. All original failures/source/artifacts remain archived; no new premise, cap, provider or manual walk is introduced.

Request: At an existing Proto.WP pure side goal, use a current local h : R -> forall u, A u -> B after current facts supply R and A u. Keep whole-hypothesis matching and caller-lemma priority; try each current local function once at the current chain level only after its final stable conclusion head matches, then unify every conclusion argument, prove every premise through the existing bounded backward side-proof path, close all data metavariables and restore failed choices. Share existing fuel/depth3; no new case search, forward saturation, provider search or unsupplied nested program walk. Scope-valid already-built proof reuse is permitted; case-free proof ancestry is not promised.

Deletion plan: Completed in PR529: all four actual translated signal walks (Sync.sig_body, Sync.ioCond_signal_wp, Threadsync.wake_body and Threadsync.cond_signal_wp) use one fsym each with exact initial ghost, hseen, complete holder resource and unchanged six public result/safety/completion statements. Current ROOT/all Proofs/Append, official fixture/axiom gates, genuine inventory renewal and focused metadata/framework pass with their original source bindings. The all-width Result run fact preserves zero-width, zero-divisor and signed-overflow errors through unchanged Basic semantics; no legacy VC rule or manual WP walk remains for this capability. Wait-family, general condition accounting and SemImpl/L8 obligations remain separately open.
