<!-- Generated from assurance/engine-ledger.json by scripts/engine-ledger.py generate; edit the JSON. -->
# fsym engine ledger

Engine features and fixes that proofs and libraries needed from `fsym`, and the workarounds that stand
in for the missing ones. This is the recorded deletion plan that CLAUDE.md asks for: code cites a row as
`ledger #<id>` (or ledger `` `<id>` ``), and `scripts/engine-ledger.py check` (preflight)
fails on a citation of a row that does not exist and on a closed row cited as a workaround that is still
there. Data and rules: `assurance/engine-ledger.json`, `scripts/engine-ledger.py`. 181 rows, 74 open.

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
| [canonical-tick-certification](#row-canonical-tick-certification) | Match emitted ticks with canonical full-memory AIR certificates | Task09 L8b-2 emitter draft; PR393 comments 6270932171 and 6278792907 | - | - |
| [protocol-tick-transport](#row-protocol-tick-transport) | Transport protocol observations and caller resources across composite ticks | Task09 L8b-2; Task07 challenges; PR393 comments 6271005146 and 6278792907 | - | - |
| [kernel-proj-ctor](#row-kernel-proj-ctor) | Projections of values that reduce to constructors are left to the kernel as definitional steps | L8e (Proofs.Sync.Cond loop56_body: kernel deep recursion, coordinator decision 2026-11-04: fix at the root, candidate (b)) | `ZigLean/Sep/Full/Auto.lean` | Transitional definitional projection steps in ZigLean/Sep/Full/Auto.lean: `retypeResult` (`projsEq`'s rest from simp's result to `reduceProjs`'s, arithGoals' `whnfR` after an unfolding), the `rflResult` step of a dependent field, and the reductions of request (1) that unification carries. Delete them when one proof-producing traversal replaces simp in `projsEq` (a congruence step at every argument, implicit and instance ones and binder domains included, a dependent field by `Eq.rec`), the matching sites of (1) rewrite the matched term by `reduceProjsEq` before unifying, and `projCtorStep?` is a simproc of the `fsym_arith`/`fsym_norm` sets for (4); then the `reduceProjsEq: simp's … is not …` trace goes, and `retypeResult` stays only for the `etaAll` step of `reduceProjsEq (eta := true)` (wpNorm, wpGoal), which is an eta reduction, not a projection step, and stays definitional; the row closes with sep-auto ProjCtorKernel as its regression. |
| [lake-needs-race](#row-lake-needs-race) | Lake 4.34 creates the jobs of concurrent `needs` facet keys twice and can deadlock | lake-hang lane (arc hangs of the assurance extraction and kernel-replay builds, 2026-11-04) | `scripts/assumptions.py`, `tests/roadmap/fixtures-lake/test_needs_race.py` | When a toolchain update fixes the race, the control assertion of tests/roadmap/fixtures-lake/test_needs_race.py fails. Then delete assumptions.needs_first (its callers build only the generated modules again), delete the test, and close this row. |
| [case-family-enrollment](#row-case-family-enrollment) | Remove transitional golden case-family enrollment markers | Task23; coordinator decision 6258258831 | `examples/threadsync/all-cases`, `examples/sync/all-cases` | When the last golden family is enrolled, remove every all-cases marker and the marker/history ratchet, derive all case families unconditionally from the full golden enumeration, and retire when_defined with its remaining users. Preserve complete output/import coverage and exact retranslation checks. |
| [3](#row-3) | ruleConcl? recognize generic FLogic.T L … rules (FAllocSpec generic in partial/total) | coordinator for D2/allocator | - | - |
| [7](#row-7) | document/plan rule preconditions ⟪φ⟫ from context facts | one-logic-tactics | - | - |
| [9](#row-9) | engine support replacing arena_* macros, within (planner rule), unroll_solo (CTriple-backend rule) | arena lane | - | - |
| [13](#row-13) | optPayload | one-logic-tactics (Lists.sum) | - | - |
| [16](#row-16) | Keep path conditions | one-logic-vc | - | - |
| [17](#row-17) | An undecided side condition φ is split by byCases | one-logic-vc | - | - |
| [18](#row-18) | Binder names | one-logic-vc | - | - |
| [21](#row-21) | fsym_arith: disjunctive goals, user Nat functions on constructors, constructor injectivity | one-logic-tactics (dispatch, PR #222) | `tests/roadmap/dispatch-templates/DispatchTemplate/Template.lean`, `tests/roadmap/dispatch-templates/TokenizerProof.lean` | delete the local `attribute [local fsym_arith] rank` lines once fsym evaluates a user Nat function on a constructor (evalUserCtor covers non-Nat results only); run the two fixtures without them. |
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
| [70d](#row-70d) | Conc/Returns: no client yet | csl/T-term | - | first client: a turn-counting protocol proof (T-term, research C13); if T-term is dropped, delete with Proto.cost. |
| [71](#row-71) | Conc/OsRules: premise evidence, standalone by design | os lane | - | move its futex facts into the full-state OS futex rules (ZigLean/Sep/Full/OsFutex.lean) and the `Io` futex-slot CTriple rules when those land (docs/thread-specs.md, STD-05), then absorb the module. |
| [76](#row-76) | Read of a read-shared io prefix in a protocol: hand copies of wp_io | critic run 15 (coordinator) | `Proofs/Sync/RwLock.lean`, `Proofs/Sync/Semaphore.lean` | when each legacy-layer file migrates to the full-state logic (docs/legacy-retirement.md), replace its `wp_io` copy with `FLock.Fits.wp_readRest` and its holder copies with `FLock.Fits.wp_hold`. Keep the primitive load/record proof shared through Inv.loadRest. Close this row only when every listed legacy workaround site is gone. |
| [return-bool-split](#row-return-bool-split) | A return whose Boolean value the postcondition matches on is not split | arena-gen (arena macros -> fsym) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete `rcases Nat.lt_trichotomy n.toNat s.len.toNat` in each arena `resize_ct` (with #64) once the walk splits a return's undecided Boolean that the postcondition matches on. |
| [arena-resize-update-cost](#row-arena-resize-update-cost) | (perf) whole-state updates at every return: the arena's resize | arena-gen (arena macros -> fsym) | - | - |
| [carve-size-probes](#row-carve-size-probes) | A carve's size probes searched the case facts of other regions | arena-retain (retaining reset over wpts headers) | - | - |
| [packed-lawful-split](#row-packed-lawful-split) | LawfulPacked for vector and packed-union fields: the law split by direction | critic 32 (review of #450, packed-roundtrip) | `ZigLean/PackedLayout.lean`, `tests/roadmap/sep-auto/SepAuto/Packed.lean` | The single-direction `LawfulPacked` class of ZigLean/PackedLayout.lean becomes the two directional classes (the conjunction kept as `LawfulPacked`), and the fail-closed `Wrap` example of the bits direction in tests/roadmap/sep-auto/SepAuto/Packed.lean becomes a proved round trip (the value direction stays fail-closed for the union); a vector-field struct joins the regressions. |
| [chain-case-unfold](#row-chain-case-unfold) | A recursive list predicate unfolded by the case the loop tests | arena-retain (loop78 of the retaining reset) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | replace the per-case bullets of `loop78_step` (ArenaSpec.lean, ArenaSpecMacos.lean, ArenaSpecFixed.lean) with one uniform `fsym` walk, drop the local `fsym_atom` attribute and delete `chain_one`, `chain_cons2`, `chain_full_cons2` and `chain_head` (Reset.lean) if no other proof uses them, once fsym unfolds a recursive list predicate by the case the step tests. |
| [P09-E4](#row-p09-e4) | @[fsym_inv] loop-invariant registry | P09 | `tests/roadmap/loop-tactics/nested/Proof.lean` | Nested's hand outer loop (`outerI`, `outerPost`, `outer_step`, `outer_loop`; `fsym` walks its step since #arith-atom-congruence, and its inner loop by the generated `@[fsym_inv]` definitions): delete when the generator also emits the counter-dependent outer invariant over `tsum` with a summary of the generated inner loop (S2c′) and `@[fsym_inv]` applies its loop rule. |
| [P09-E5](#row-p09-e5) | @[fsym_upd] ghost-update registry keyed by heads, tried at returns | P09 | - | - |
| [list-walk-step](#row-list-walk-step) | a list walk's step from its invariant: split the ghost list by the cursor's test, unfold and fold the list | invariant-synthesis (P09, S2d: Proofs/Lists/Linked.lean, Proofs/Lists/Alloc.lean freeAll, loop-tactics/Queue.lean) | `Proofs/Lists/Linked.lean`, `Proofs/Lists/Alloc.lean` | When `fsym` walks these steps from the invariant and the generator emits the list-walk family (S2d), delete `revInv`/`revPost`/`sumInv`/`sumPost`/`freeInv`/`freePost` and the `*_step`/`*_loop` lemmas. The files then hold statements proved by `fsym` over the generated `@[fsym_inv]` definitions, and loop-tactics/Queue.lean builds on top unchanged. |
| [recursive-group-total](#row-recursive-group-total) | Generic total correctness of a recursive function group | L8b-1 tick coverage (Task 09); P03/stack | `Proofs/Pointers/Sep.lean` | Proofs/Pointers/Sep.lean (#617): the private `addDown_group`, which `addDown_total` applies, closes the postcondition by hand after fsym: `EUpd.of_imp`, two `sep_left_comm_eq` reorderings and `congrArg (BitVec.ofNat 64)` with `addDown_sum_step`, because fsym's frame planner cannot match `pts p 8 v` against `pts p 8 v'` when the values are equal only by arithmetic. Missing fsym capability: matching values that are equal by arithmetic (a kernel-checked value-congruence step in the frame planner, or an existential postcondition `∃ y, ⟪y.toNat = x.toNat + sumDown n.toNat⟫ ⋆ pts p 8 y` closed by `fsym_arith`). This capability is separate from this row's generic recursive-group rule (which is why no row of its own tracks it yet: open one when the engine work starts); delete that hand block from `addDown_group` and this site when it lands, and do not close this row while the site stays. |
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
| [cond-window-multi-waiter](#row-cond-window-multi-waiter) | The condition's epoch window with two or more registered waiters | L10k (review of #630/#631, 2026-11-04) | - | Closes when the quantitative premise (a registered waiter reaches its futex wait before `2^32` further epoch writes) has an ID in docs/premises.md and assurance/premises.json and a mechanism (M1 or M2 above, maintainer decision) by which a client with two or more registered waiters meets the narrowed `win` and lists the premise. |
| [final-match-greedy](#row-final-match-greedy) | The planner's final match takes the first atom that unifies, also for an existential a later atom fixes | arena-retain (reset's retaining modes) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | drop `attribute [local fsym_atom] FreeList` of `reset_retain_capacity_ct`/`reset_retain_with_limit_ct` and pass `count_spec` for `count_free` (delete `count_free`) in each ArenaSpec*.lean once the final match does not commit to an atom that a later atom's match contradicts. |
| [undecided-eq-branch-cost](#row-undecided-eq-branch-cost) | (perf) A walk through an undecided equality branch of a computed value exceeds the budget | arena-retain (loop66 of the retaining reset) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete the `by_cases hsm : v.toNat < 2` before `fsym` in `loop66_c0` and `loop66_c1` of each ArenaSpec*.lean once one walk of the body with the undecided branch stays within the budget. |
| [per-translation-walks](#row-per-translation-walks) | The same std code translated for several targets is proved once per translation | coordinator (critic run 31, arena retaining reset) | `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | state once, in a shared module over the generic translation, the defs and theorems that ArenaSpecMacos.lean and ArenaSpecFixed.lean repeat from ArenaSpec.lean (main's 24: `free_ct`/`free_spec`, `resize_ct`/`resize_granted_ct`/`remap_ct`/`resize_spec`/`remap_spec`, `al`, `tables`, `child_decode`, `count_loop`/`count_spec`, `Inv19`/`Exit19`/`loop19_step`/`loop19_ct`, `Lists9`/`Inv9`/`Exit9`/`loop9_step`/`loop9_ct`, `deinit_ct`, `reset_free_all_ct`/`reset_free_all_spec`; and the retaining reset's 15: `count_free`, `Inv78`/`Exit78`/`loop78_step`/`loop78_ct`, `Inv66`/`Exit66`/`loop66_c0`/`loop66_c1`/`loop66_step`/`loop66_ct`, `reset_retain_capacity_ct`/`reset_retain_with_limit_ct`/`reset_retain_capacity_spec`/`reset_retain_with_limit_spec`), and make each ArenaSpec*.lean an instance (only a walk over code that differs between translations, the patched `free` and `resize`, stays per module), once the translator emits the shared std code once or fsym walks a module-generic presentation. |
| [arena-retained-capacity](#row-arena-retained-capacity) | The retaining reset's retained capacity is not stated | coordinator (takeover review of PR #468) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | state the retained capacity in `reset_retain_capacity_spec` and `reset_retain_with_limit_spec` of each ArenaSpec*.lean (after the per-translation-walks row, once in the shared module) by linking `Kept`'s `sz` to the limit and the list's capacity, then close this row and drop the 'not stated' wording from docs/alloc-arena.md, docs/allocator-identity.md, tests/roadmap/alloc-arena/README.md and register row M01. |
| [region-end-opt-in](#row-region-end-opt-in) | The owned-region end bound is a per-file opt-in fact | coordinator (takeover review of PR #468) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete the three `attribute [local fsym_facts] MemFacts.region_end` lines (ArenaSpec.lean, ArenaSpecMacos.lean, ArenaSpecFixed.lean) once `fsym` supplies the owned-region end bound on demand (or as a default fact without a measurable cost). |
| [l10-native-lock-step-contract](#row-l10-native-lock-step-contract) | Native lock-step contract before semaphore resource-transfer walks | L10 semaphore migration (Task 07; coordinated with L11 and Task 06) | - | Close after native lock primitive producers and Full consumers preserve the original Step guarantees without registered legacy dependencies, the generic fsym resource-transfer and held/outside signal walks pass strict actual term-and-type closure, and Task 07's translated Semaphore/SemCounter/Mailbox migration is complete. This row authorizes no transitional code. |
| [l11-waitgroup-rwlock-impl](#row-l11-waitgroup-rwlock-impl) | Word rules for gone threads, then WaitGroup and RwLockImpl on the full-state logic | L11 RwLock/WaitGroup migration (maintainer decision 2026-11-03) | - | Closes when Proofs/Sync/RwLock.lean, Proofs/Sync/RwLockContract.lean, Proofs/Sync/RwLockSnapshotPair.lean and Proofs/Threadsync/WaitGroup.lean leave `legacy_users` with their statements unchanged. |
| [literal-pointer-provider](#row-literal-pointer-provider) | A literal pointer in a state region, found by the planner instead of a walk rewrite | coordinator (2026-11-04, /simple on #604: the walk rewrite is shallow) | `ZigLean/Sep/Full/Auto.lean` | Transitional: delete `rebaseLitPtr?` and its call in walk's no-rule fallback once the planner's pointer-in-region provider lands; the tests SepAuto.Region `literal_store_load` and `literal_store_offset` stay green through the switch. |
| [client-glue-copies](#row-client-glue-copies) | Sync clients copy the memory glue of their protocol's rest (cells of the words in the rest, the block, start and fork facts) | L10p (/review of PR648, 2026-11-05) | `Proofs/SemCounter/Mem.lean`, `Proofs/SemCounter/Start.lean`, `Proofs/Handoff/Protocol.lean`, `Proofs/Handoff/Start.lean`, `Proofs/Handoff/Steps.lean`, `Proofs/Handoff/Ops.lean`, `Proofs/MutexCounter/Protocol.lean`, `Proofs/Sync/Mailbox/Protocol.lean`, `Proofs/Sync/Mailbox/Steps.lean`, `Proofs/Sync/Mailbox/Start.lean`, `Proofs/Threadsync/WaitGroup/Protocol.lean`, `Proofs/Threadsync/WaitGroup/Start.lean`, `Proofs/Threadsync/WaitGroup/Main.lean`, `Proofs/Threadsync/WaitGroup/Wait.lean` | Move the layout-free lemmas (`res_eq`, `heap_blk`, `frame_rest`, `apart_of`, `BlkOk.of_block`, `word_init`, `heap_ne_*`, `erase_ne_r`, `clk_fork`, `cinv_out`, `einv_out`, `ewait_ok` (next to `FEvent.Inv.toOut`), `hb_fork`, and `sinv_grow` as a generalisation of `FSem.Inv.mono`) to `ZigLean/Sep/Full`, replace Handoff's `le_nil` by `VClock.le_default` (as SemCounter does) and `upd0_1`/`upd1_0` by `upd_ne`, and state the rest family once over a block, a byte range of words and an `io` prefix (a generic `Rest`/`BlkOk` module) with Handoff, MutexCounter and SemCounter as instances; delete every copy and close this row. |
| [fsym-or-witness-order](#row-fsym-or-witness-order) | fsym's post solver chooses an existential's witness by a disjunction before the conjunct that determines it | claude/fsym-fvar (found closing row fsym-unknown-fvar-mutex-loop, 2026-11-05) | `Proofs/Threadsync/ThreadMutex.lean` | Transitional: once the solver orders such a conjunction itself, state `lockInvD` (darwin) in its natural order `∃ g₀, (g₀ = g ∨ g₀ = L.set g .spin rnil) ∧ P.inv (upd G t g₀) m` again, swap-build `Proofs.Threadsync.ThreadMutex` against the darwin translation, and close this row. |
| [callocspec-partial-step-count](#row-callocspec-partial-step-count) | The allocator contract CAllocSpec is partial, so a client's exact step count holds only for runs that return | L8g/L8h (#562, coordinator decision 2026-11-04: accepted as a recorded obstruction) | - | - |
| [rwlock-reader-admission-room](#row-rwlock-reader-admission-room) | Derive reader and pending-writer admission room from actual RwLock handles | Original Task08 RwLockImpl migration (2026-11-04) | - | RwState.Family and its ABI64 instance supersede legacy Sync.RwLockRead.sv3, sv3_* and RM; delete that duplicate algebra with the RwLock/RwLockContract/RwLockSnapshotPair migration when their real contract consumers use this family, then close this row. Keep the native-operand and count-boundary kernel controls. |
| [mutex-held-foreign-wait](#row-mutex-held-foreign-wait) | Keep mutex ownership across a wait at an independent sync object | Original Task08 RwLockImpl migration (2026-11-04, PR #637) | - | Close after the generic existing mutex contract and its translated instance support the actual nested wait, and RwLock consumes that support with unchanged public clients. Do not add a local semaphore contract, omit the blocking branch, assume a waiter never sleeps, or hand-walk the outer mutex as a replacement for MutexImpl. |
| [fsym-forward-bool-fact](#row-fsym-forward-bool-fact) | fsym does not forward a hint term's Bool-equation fact, so a rule's autoParam guard cannot use it | S6 (#649, futex address validation) | `tests/roadmap/sep-auto/SepAuto/WPOsFutex.lean` | Transitional: once fsym forwards such a fact, delete the `have hw := …` before each `fsym` in SepAuto.WPOsFutex, pass the term in the `fsym` list instead, and close this row. |
| [fevent-live-exit](#row-fevent-live-exit) | A thread with FEvent's waiter role stays in the event word's live set after its last access | L11f review of PR646 (pass 2, cross-file angle) | - | - |
| [waitgroup-impl-contract](#row-waitgroup-impl-contract) | No generic wait-group contract (`WaitGroupImpl`) on the full-state logic | L21 (retirement of ZigLean/Conc/Spec, PR677) | - | Closes when `WaitGroupImpl` is on main with 0.15.2's `Thread.WaitGroup` proved against it and `Proofs/Threadsync/WaitGroup.lean` uses only the contract (docs/thread-specs.md, "What has no replacement yet"). |
| [mutex-impl-relaxed-witness](#row-mutex-impl-relaxed-witness) | No kernel-checked witness that `MutexImpl` rejects a relaxed `unlock` | L21 (retirement of ZigLean/Conc/Spec, PR677) | - | Closes when the witness is in tests and checked by its fixture's check script. |
| [guard-lifeline-mirror](#row-guard-lifeline-mirror) | build-guard mirrors a lifeline ticket in `merge/` for guards of checkouts before PR #661 | P1c (elastic build-guard admission, PR #661) | `scripts/build-guard.py`, `tests/roadmap/build-budgets/test_guard.py`, `docs/build-budgets.md` | Delete `Admission.mirror` and `mirror_lifeline` (and the `lifeline_aware` mark, which only it reads), the mirror part of `test_the_lifeline_goes_ahead_of_every_exclusive_ticket` and the mirror paragraph of docs/build-budgets.md#elastic-workloads in the first PR after 2026-11-19 whose check shows no older guard running: at one main-health run, on arc and on the Mac, for every running build-guard process (`ps -eo pid,args \| grep build-guard.py`), its checkout (the script path when absolute, else the process's working directory: `readlink /proc/PID/cwd` on arc, `lsof -a -p PID -d cwd -Fn` on the Mac) contains #661's merge commit (`git -C <checkout> merge-base --is-ancestor <merge> HEAD`). Then close this row. |
| [two-lock-product](#row-two-lock-product) | The generic two-lock product over FLock (lock nesting) is not built yet | L8q/L8r lock-order work (Step 2), #693; parked by the coordinator 2026-11-05 | - | Closes when the product invariant, the partTick and waitNest rules at FLock level and the generic two-mutex fixture land; no workaround is in the tree. |
| [second-pass-speculative-cost](#row-second-pass-speculative-cost) | the arithmetic's second pass runs on the failed side goals of rules that do not apply | coordinator (main red on alloc-translated since #699, PR #703) | `tests/roadmap/alloc-translated/PageThread.lean` | Delete `fthread_remap`'s `set_option maxHeartbeats 300000` when a failed rule premise no longer pays the second pass and `fthread_remap` elaborates within 180k heartbeats (a margin under the default 200k, which it reached before #699). |
| [share-gather](#row-share-gather) | gathering partial read shares of different owners into a whole share fails closed | coordinator (F4 read shares, option R, PR #713) | `ZigLean/Sep/Full/ThreadOwned.lean`, `ZigLean/Sep/Full/ThreadSpawn.lean`, `ZigLean/Sep/Full/Lock.lean` | Replace the no-gather premises `hg`/`hgat`/`NoGather` of `FOwned.join`, `FCapture.join_regain`, `FLock.Inv.join`, `FLock.Inv.acq` and `FLock.Inv.take` by the `Mem.Owns` premise of the gathered bytes (`Mem.OwnsRes.addOwns` shape), and delete `FLock.NoGather`. |

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
| [9h](#row-9h) | unroll_solo: concrete counterexample runs | closed by PR #697 (on the `zig_run` simp set of #690): ArenaObstruction `client_illegal`/`reset_client_run` and ListsPage's runs name only their own client (`unfold client vt`) and unfold the generated code with `simp only [zig_run]` (singlePass), so no translation's loop numbering appears in a proof; proof-tools/Unroll `even_six_solo` names only its own test definitions. |
| [10](#row-10) | Full/Arr rules (arr_load/store/ptrProject, facts_arr, split/join) | not engine (library Full/Arr); note only |
| [11](#row-11) | CTriple backend on top of FTTriple (T-ctriple | open (after #1); exact request below (2026-10-12, approved design R2, docs/sep-threads.md §T-ctriple) |
| [12](#row-12) | Precondition planning: region atoms before size-dependent atoms | READY #250 |
| [14](#row-14) | One fsym entry for other front ends | Auto.run is the shared entry of evalFsym (and was memVc's until vc_gen was retired), including introductions, context preparation, run caches and the orphan-proof check; runReport adds residual attribution to that entry |
| [15](#row-15) | Quiet stop | Auto.runReport returns stop reasons without emitting a report message, and fsym.report emits schema-versioned JSON; a reporting walk emits no human stop message. The fsym.quiet option was removed |
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
| [69d](#row-69d) | Conc/Spec/MutexToy: witness of the legacy MutexSpec | DONE (L21): deleted with ZigLean/Conc/Spec and MutexSpec. Its relaxed-unlock counterexample against MutexImpl is row mutex-impl-relaxed-witness. |
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
| [P09-E2](#row-p09-e2) | strongest-postcondition inference at returns for FTotalTriple/FTriple and the thread backends, as inferPost... | DONE (R1, PR #717; approved with P09 2026-10-15). An unknown post at the top of a goal is inferred as before (`inferPost`, now over `strongestPost`, which takes any arguments). New: a return into an unknown that the walk infers (a registered loop's exit post that the engine created, the goal's postcondition also after a case split, `?Q true v`) applied to computed arguments is noted by the entailment (`noteExit`, after `decidePost` takes the decided conditions; an undecided exit condition is split on, so the exit's post carries it), never unified. When the unknown's walk ends (end of `Auto.run`; before a registered loop's continuation), it becomes the join of the returns' strongest posts, each with equations for its arguments (`finishExits`, `upd_join_l`/`upd_join_r`, checked before the assignment). A registered loop without `B.post` continues from the strongest post of its step's exits only if the step's walk closed every path (`⟪False⟫` if no exit is reached); a stopped step leaves the exit post unknown and the continuation a residual (`exit_post_not_inferred`), in every backend with a loop rule. The report lists the inferred posts (`posts`, `kind` `return`/`loop_exit`). Regression tests/roadmap/sep-auto/SepAuto/Infer.lean: total, partial and thread logics, function ends and loop exits, a too-strong caller post rejected, a step that stops before an exit, an exit post assigned before its join, a return without a strongest post, an undecided exit condition; LoopInv's concurrent loop without a post. |
| [P09-E3](#row-p09-e3) | abduction report | DONE (R1, PR #717; approved with P09 2026-10-15). Each plan of a rule's precondition collects the atoms it misses (`noteWanted` into `planNotes`, `withPlanNotes`: only while a report is collected, each plan its own notes). A rule whose plan fails is kept for the step once (`notePlan`, in `tryRule` and `tryBindRule`; a retry with the same missed atoms adds no row). A stop with no rule, or an invariant that does not hold at a loop's entry (the loop rule's plan), lists them in its origin's `plans`: the rule, and each missed atom with its unknowns (`?u0`, … and their types). A view's walk that is rolled back restores the step's plans. Regression tests/roadmap/sep-auto/SepAuto/Infer.lean: a load from a state without the cell; a loop invariant that needs a cell the entry lacks. |
| [arith-atom-congruence](#row-arith-atom-congruence) | arithmetic congruence of library atoms (counter-dependent sums) | DONE (E5, 2026-11-05): `arithCore` runs `omega` again, unless a probe, with the relevant facts each normalized against all the facts (`renormFacts`: a conditional rewrite whose side condition a later fact proves, `tsum_sub_of_lt` under the loop test) and the congruence of atoms (`atomCongr`: an atom `f t` of a function the solver does not read, a constant or a local, with `t` containing the side `l` of a fact `l = r` that is itself an atom, equals `f t[r/l]` in `fsym_arith` normal form; one step per equation, at `Nat`/`Int`). The library sum is `Zig.Full.tsum` (`ZigLean/Sep/Full/TSum.lean`, imported by `AutoAll`) with `tsum_zero`, `tsumSucc` (a bound `n + 1`, not a numeral) and the non-recursive differences `tsumSubLt` (`tsum_sub_of_lt` where the term `g x` is not `0`, whose right side would normalize back) and `tsum_sub_of_le`. Regression `tests/roadmap/sep-auto/SepAuto/AtomCongr.lean` (the side goals of `tri.loop5`'s step; negatives: a step of two, a bound, a missing loop test). Clients: `tri.loop5`'s step walks by bare `fsym` under `v + (tsum n id - tsum i id) = v₀ + (tsum n id - tsum i₀ id)` (checked in a scratch walk over counted's translation, not committed: the generator lane emits it); nested's outer loop is stated over `tsum` and `outer_step` is a bare `fsym [inner_loop]` (`cnt`, `cnt_mono` and the hand rewrite deleted; its hand invariant `outerI` stays until the generator emits it, S2c′ in docs/invariant-synthesis.md). Found by R1d (2026-11-05). The difference forms are non-recursive because a recursive conditional unfold (`x < b → S x b = x + S (x + 1) b`) hits the maximum recursion depth: in a context whose facts are contradictory the discharger proves every side condition. |
| [atom-args-normal-form](#row-atom-args-normal-form) | an existential's witnesses against a state atom's unnormalized arguments (`List.set` of a literal list) | DONE (E5, 2026-11-05): the planner's `matchArgs` matches a constructor application of a pattern with metavariables (an existential's list `[?w₀, ?w₁]`) against a state value that is not one (not a number: the solver's) by the value's head normal form (`whnfD`, within `probeCaseBudget`), recursively, so the final match assigns `?w₀ := x`, `?w₁ := y`; the match is then proved by `proveEq` and checked by the kernel. Regression `tests/roadmap/sep-auto/SepAuto/AtomArgs.lean` (two stores into `arr p [a, b]` into `∃ w₀ w₁, … ⋆ up (arr p [w₀, w₁])`; negatives: swapped witnesses, a list of another length). Client: `pairAt.loop5`'s step walks by bare `fsym` under an invariant owning `arr p [w₀, w₁]` (scratch, for the generator lane). Found by R1d (2026-11-05). The item rules through the array's own pointer (`FTotalTriple.arr_load_zero`/`arr_store_zero`, merged with this row) make `fsym` walk `pairAt.loop5`'s body (`acc[0] += 1; acc[1] += 2`) under an invariant owning `arr p [w₀, w₁]`. A concrete target list already matches (`docs/proof-tools.md`: `arr p [x, y, z]`, store at `p.elem 4 1`, post `arr p [x, w, z]`); tagging `List.set_cons_zero`/`List.set_cons_succ` `fsym_norm`/`fsym_arith` does not change the residual. |
| [T2](#row-t2) | plain atom: tick_plain receipt dropped (bare fsym) | see request text (tick rows, plans/tick-cost.md) |
| [T3](#row-t3) | credits 1 consumed by tick (bare fsym) | see request text (tick rows, plans/tick-cost.md) |
| [T4](#row-t4) | ticks in the CTriple backend (not attempted) | The existing rules walk callMC Zig.tick in sep-auto/Ticks.cbody_spec and its loop in cloop_spec, in the plain mode; no backend-specific tick rule was needed (a historical probe against 958596cfc, 2026-10-16, first showed it; sep-auto/check.sh now checks Ticks). The CTriple evidence covers the plain mode only: a metered (credits) tick under CTriple has no control yet. |
| [T5](#row-t5) | tick_run kept opaque in fsym_norm | see request text (tick rows, plans/tick-cost.md) |
| [pick-bind](#row-pick-bind) | Pick-bind rules: bind rules over pick >>= op >>= g | DONE: PR #352 (merged 2026-10-15) registered `CTriple.weakCasPtr_bind` as `@[fsym]` (AutoConc.lean ~363); `publishWeak_spec` and `publishWeak_frame` are a bare `unfold publishWeak; fsym` |
| [thread-loop](#row-thread-loop) | Loop rule for a Zig.loop in a thread (FTTriple) | DONE PR #319 (codex/fsym-thread-loop: Full/ThreadLoop) |
| [cond-epoch-load-floor](#row-cond-epoch-load-floor) | The condition waiter's epoch load has a floor, so contended clients can prove the window | CLOSED by option (a) (coordinator decision 2026-11-04, PR #631): the `FPrim.ofWords` Move step carries the lock's word invariant `L.WInv (L.pl G) m` at the state before the step; `Fits.back`/`Fits.wStep` take it and every word rule passes stopW's `hiL.w` to its callback. `U` itself cannot carry holder uniqueness, because `FLock.Fits.stable` admits a lock step of an `ok` thread to any ghost place, so `U` must tolerate two ghost holders; the pre-state `WInv` at Move gives it instead. New `FCond.ld_newest`: with `FLock.WordHB L C.Ep` before the step, an `en -> ld i e` step saves the newest epoch write (`i = size - 1`) and keeps the epoch's writes. #630's `FCond.EpHB` lemmas became the word-generic `FLock.WordHB`, `.last`, `.step`, `.lstep` (ZigLean/Sep/Full/Word.lean; review of #630). No contract statement (MutexImpl/CondImpl/EventImpl/SemImpl) changed its text; their `Fits` premise now gives a client's `kstep` the lock's word invariant before a step (stronger for clients; every implementation supplies it through the word rules). Before it, #630 gave `en -> ld i e` the load's floor in `FCond.SigStep` and pinned the registration `ld -> reg i jr`, both proved inside the library rules. Remaining: two or more registered waiters, row `cond-window-multi-waiter`. |
| [lock-stable-inv](#row-lock-stable-inv) | A lock step's U-stability may use the lock's invariant before the step | CLOSED in #667: `FLock.Fits.stable` takes `L.Inv G rX m` (the state before the step) beside `U G rX m`, and so do `Fits.ofLock`/`ofLockAll`'s `stable` argument. `Fits.step`/`Fits.stay` take it, and every rule that applies them passes the lock invariant it already has. `FSem.Fits`/`FCond.Fits` extend `FLock.Fits`, so they inherit it. Clients that do not need it ignore the binder. Second step, decision (a) on #693 (L8r): `stable` also takes `L.Transfer G rX m m' t p h`, the resource the step moves: without the lock afterwards `h = rnil`, a holder that stays one keeps `L.held (G t)`, at an acquire the lock was free and `h` is its resource before the step (`L.Free G ∧ L.FreeRes G rX m h`; `FreeRes` is now `Inv.rest`'s body), and at a release the free resource after the step is the old held one. `Inv.acq`/`Inv.rel` return those `FreeRes` facts, `Transfer.none`/`stay`/`acquire`/`release` build it, and every rule that applies `Fits.step` passes it; `ofLock`/`ofLockAll` and the seven client `stable` lemmas take the binder. |
| [sem-go-code-moves](#row-sem-go-code-moves) | The semaphore's holder moves (`FSem.Go`) are not tied to its code | DONE ([PR636](https://github.com/riventic/air2lean/pull/636)): `FSem.Go` admits `.wt` only from `.out`, `.pst` only from `.out` or from `.wt` with `S.cnt G != 0`, `.out` from `pst` as before, and staying in place. `wp_lockWt` (from `out`, new premise `S.ph g = .out`), `Fits.wp_take` (from `wt`, its `hnz`) and `Fits.wp_give` (from `out`, new premise `S.ph g = .out`) meet it through `U_pst`'s source premise; `ioSem` passes `SemImpl`'s existing `S.ph g = .out`. The per-registration bound (at most one epoch write while a waiter is registered) is each client's proof. The first is SemCounter's migration over `SemImpl` (legacy user `Proofs/Sync/SemCounter.lean` in assurance/proof-framework.json). |
| [sem-wait-role](#row-sem-wait-role) | The semaphore's wait is open to every thread, so a permit's holder may sleep at the condition | DONE ([PR639](https://github.com/riventic/air2lean/pull/639)): `FSem.wx : γ → Prop` is the client's waiting role next to the condition's `sx`, with the iff laws `wx_l`, `wx_part`, `wx_c`, `wx_s` (the lock's, the part's, the condition's and the semaphore's updates keep the role, like `FEvent.wx_set`). The role is a property of the ghost value, not of the op: a client keeps every thread it counts on to post out of it, also in `post`'s tail. `FSem.Go` admits `.wt` only from `.out` with `wx (G t)`, and `Move.enter` needs `wx (G t)`. `wp_lockWt`, `wp_cwait`, `SemImpl.wait_wp_resource` and `SemImpl.wait_wp` take `wx g`; `post` is unchanged. `ioSem` passes it on. A client names the threads that may wait (SemCounter: the client part `work k false`, not the permit's holder). |
| [sem-hold-rest-inv](#row-sem-hold-rest-inv) | The semaphore holder's step keeps the rest but does not give the lock's invariant after it, so no client's rest keeps the condition's cells | DONE ([PR644](https://github.com/riventic/air2lean/pull/644)): `FSem.Move.hold` takes `(∃ G'', L.Inv G'' rX m')` after its `FStepIn` premise. Its three producers already have it: `Fits.move` (the same memory, `hL`), `Fits.wp_cnt` and `U_pst` (their `hL'`). `Sem.lean` and `Proofs.Sync.IoSemaphore` build unchanged otherwise. |
| [sem-take-index](#row-sem-take-index) | The semaphore's wait fixes the taken resource and the waiter's new ghost value before the call | DONE ([PR642](https://github.com/riventic/air2lean/pull/642)): `SemImpl.wait_wp_resource` and `SemImpl.wait_wp` take `gx : (ThreadId → X) → γ` and `T : (ThreadId → X) → FAssn`, indexed by the client parts at the take, `Y = S.xs (upd G t g)` with `G` the take's state (the one the premises quantify); `hcnt`, `hpool` and `hU` are at `gx Y` and `T Y`, the `gx` premises hold for every `Y`, and the post returns `Y`. `ioSem` proves it. `post` is unchanged. A client with a fixed `gx`/`T` passes constant functions. |
| [thread-store-sized](#row-thread-store-sized) | A store of a packed struct into an owned word in a thread | DONE on codex/arena-reset-retain: provider `ThreadLocal.store_sized` (AutoThread.lean); regression `tests/roadmap/sep-auto/SepAuto/Threads.lean` (`packedWord`, `packedAtomicWord`: both fail without the provider) |
| [typed-region-release](#row-typed-region-release) | Release a complete block from typed fields while preserving the native stack refund | Native typed-region/extent/release lemmas and approved size-aware matching use data-only hints, witness rollback, shared bounded substitution refresh, unresolved-token inference and independent original side premises. Comments6279182210/6279202049 approved active-path view progress and applied explicit-frame unification. Actual fallback whole Structs, including free_fields_stack with its exact original goal, and the full29-file official sep-auto suite PASS on f9505e4e/main578aa3b2, Auto5614ed37, guards b8bf14f3/e6cbb205. The five unchanged Proofs callers retain their earlier afc52032a/Auto f13fb21a PASS binding69afbe3b; an accepted fixed-size causal audit supports reuse, not a fresh current-source claim. Isolated A/B proved the added ordinary size attempt caused the large-state regression, so Claude6280049836 dropped fix3 and restored the whole carve function exactly to main. The separate case-fact positive remains an explicit expected failure tracked by open carve-size-probes. Fixes1-2 and all other controls remain; no cap increase, broader planner or weakened production statement. Reproduce with tests/roadmap/sep-auto/check.sh; actual report6280488414. |
| [region-memset-read](#row-region-memset-read) | Infer a region read after a defined-value memset | Implemented by ReadsAt.regionMemset/regionMemset0 through the existing region/extraction/decode lemmas. Reproduce with tests/roadmap/sep-auto/check.sh: Region.memset_read and Region.memset_word_reads cover byte and multibyte initial/interior loads. No new provider kind or engine change. |
| [known-bytes-on-demand](#row-known-bytes-on-demand) | Derive requested block-address knowledge from raw bytes without changing global store results | The original storeBlock/storeBlock_finite posts are restored; one requested-knowledge planner precedes region planning and uses known_of_bytesAt. Approved committed-descendant retry, snapshots/fallbacks, source-first determined-block address selection, unknown-block matching and direct-update shape checks remain. Whole actual Structs, including concrete/existential/idempotence/no-request/fail-closed controls, and the full29-file official sep-auto suite PASS on f9505e4e/main578aa3b2, Auto5614ed37, guards b8bf14f3/e6cbb205. The five actual unchanged Proofs callers PASS at their original afc52032a/Auto f13fb21a binding69afbe3b; the accepted causal audit supports retaining that evidence after the final change only restores main's carve. The isolated A/B and Claude6280049836 removed the ordinary size probe while preserving fixes1-2 and the explicit case-fact expected failure. No current-source fresh-five claim or blanket full-build repeat for a head move. Reproduce with tests/roadmap/sep-auto/check.sh; actual report6280488414. |
| [wp-local-hypothesis-application](#row-wp-local-hypothesis-application) | Apply current local proof functions during bounded WP side proofs | Qualified in PR529: at2f1b/main737, Auto/AutoWP fe270e1f/b9839887, whole canonical WP100 jobs, both actual condition modules161 jobs and exact407-target ROOT pass. Guardf07c262a/unit16d97d42 binds1005 unchanged source/command rows; physical ROOT8e2f1fa3/logdc09702f is reused for inventory. Official SepAuto31 builds206 jobs and replays203 modules/2111 theorems with standard axioms; OneLogic8 builds132 jobs and replays129 modules/108 theorems. SepAuto's general assurance output retains3 unchanged-class float-key/test-opaque policy findings; its documented fixture gate passes, not general policy. Currentnessfc737e7a renews only3 supported stale swap recipes, retains13 runs/49 qualified artifacts, and passes official inventory write/check. At a3a634ab8/main737, focused preflight and independent framework both pass (guardb3e8ad24, logs3b2b8c45/d4af7583), fixed inputs/artifacts unchanged. Final review/simple find no actionable issue. One structural walk retains raw/normalized evidence, forwarding priority, proof-local Eq substitution and exact-type own-equation exclusion; observable controls check actual substituted data. Assigned-update/global-definition controls compile; actual fresh FBA Full/no-PANIC evidence retains its35d8 binding. All original failures/source/artifacts remain archived; no new premise, cap, provider or manual walk is introduced. |
| [literal-pointer-rebase](#row-literal-pointer-rebase) | Store or load through a literal pointer into a region of the state | Branch claude/fsym-literal-pointer: `rebaseLitPtr?` (Auto.lean) in the walk's no-rule fallback, before views and unfolding, with `ptr_eq_add_off_sub` (AutoRules.lean). Tests: SepAuto.Region `literal_store_load` (a region at a literal base) and `literal_store_offset` (a region at `p.add (bs.extract 0 12).size`, its block and offset from facts). |
| [read-through-bytes](#row-read-through-bytes) | Read region bytes through stores to other bytes, memset items and a kept prefix | Branch claude/fsym-read-through. Region.lean `@[fsym_arith]`: `extract_writeBytes_other`, `extract_memsetBytes_item`, `extract_replicate_le`, `decode_byte`, `LawfulEnc.decode_encode`, `Array.replicate_one`, `Array.size_replicate`, and the simproc `keptExtract` (with `extract_of_keepsPrefix`). Auto.lean: `arithCore` closes an equation with an unknown side by reducible unification of the normalized sides; `omegaDisch` states a discharged side condition as itself. Tests: SepAuto.Region `read_unwritten`, `read_unwritten_word`, `read_kept`. |
| [fsym-split-nested-struct-subst](#row-fsym-split-nested-struct-subst) | fsym's split of a user-structure fact leaves a stale local when a field is a structure whose split substitutes a local | closed by the branch claude/fsym-fvar: `destruct`'s structure branch takes each field from the fact as the previous field's substitution reintroduced it (`liveFVar?`). `Zig.SemCounter.U` is a structure again. Regression: SepAuto.Facts `nested_struct_subst`. |
| [fsym-unknown-fvar-mutex-loop](#row-fsym-unknown-fvar-mutex-loop) | fsym leaves an unknown free variable on the macOS ThreadMutex lock loop body | closed by the branch claude/fsym-fvar: each branch of a split is walked with the substitutions of its own branch (`eachBranch`); the second branch's substitution of `g₀` had replaced the first's. The row's original call elaborates (checked); `loopD_body` is the shorter call without the `hset`/`hph`/`hok₀` glue, swap-built against the darwin translation. Regression: SepAuto.WP `sibling_values`. |
| [word-ok-live-set](#row-word-ok-live-set) | Word.Ok asks every plain access to happen before every thread, so a whole-struct read next to a futex word breaks it | closed by PR646, which gives Word.Ok a live set |
| [run-witness-loop-names](#row-run-witness-loop-names) | Kernel run witnesses name the functions on the run's path to its loops, and the path differs between Zig versions and targets | closed by PR #697 on the `zig_run` simp set of #690 (docs/proof-automation.md, kernel-run witnesses): every former workaround site unfolds the run's path with `zig_run` and names only hand-written definitions; `Sync.Handoff.handoff_completes` no longer uses `unroll_sched`. |
| [fstepin-addrs](#row-fstepin-addrs) | FStepIn does not keep the blocks' addresses, so a futex key of another block is lost across a frame step | closed by PR #681: `FStepIn.addrs : m.SameAddrs m'` (ZigLean/Conc/Clock.lean) replaces the field `blocks` (now the theorem `FStepIn.blocks`), with the library lemmas `Mem.SameAddrs.refl/trans/of_blocks/of_push/of_set/size/addrIn_eq` and `Mem.sameAddrs_write` (ZigLean/Mem/Lemmas.lean) |

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
- **M9** counterexample runs (`unroll_solo` → term-level expand/decide). Closes 9h (decide with arena lane). L16: `unroll_solo` deleted, runs by `unfold` of the defining equations, then `decide +kernel`; 9h stays open for name-independent unfolding.
- **M10** (coordinator 2026-10-12, CLAUDE.md #216 "build generic, prove individual items") ONE fsym dispatch rule set for calls through any vtable/interface value under a registered contract (Allocator, Io, Random, Writer, user vtables, callbacks). Coordinate with the interface-contract lane (docs/interfaces.md, handoff codex__alloc-param.md — neither existed yet at 2026-10-12 evening). Today: CAllocSpec.dispatch + indirectWalk (Auto.lean) are allocator-shaped; M10 generalizes them to a contract registry. Providers (Active/Live) are stated generically over tags/blocks (no allocator-specific provider kinds).

## Rows

<a id="row-canonical-tick-certification"></a>
### #canonical-tick-certification Match emitted ticks with canonical full-memory AIR certificates

Status: **open**. Requester: Task09 L8b-2 emitter draft; PR393 comments 6270932171 and 6278792907.

Note: The approval excludes the separate STK factual schema, authenticated producer/case boundary and carrier reductions; drops remain off. Checks retain their actual source bindings. The original modeled-panic mangling placeholder and predicted induction-completeness boundary (PR510/6285634841) were subsequently resolved by exact source-identity lowering and the existing compiler factual query, qualified in the actual15d workflow. Native SCC/effects/cost policy stays canonical; derived executable function/helper references serve proof partition only.

Progress: Maintainer approved A/1a on PR510/6284852746. Actual15d172292 passes the producer, fresh complete two-call certificate, recursive executable clique using actual compiler order, wrong-order rejection and modeled-panic certificate/native policy controls (report983f38d4; PR510/6294412539). Program/importers pass at9ca3; the full arbitrary-record/default-limit RenumberOracle leaf passes atbd2f (reporta3c40cea). Earlier failures remain attributed to their original sources. The existing-Assurance factual query preserves exact rendered bytes, compiler EqnInfo order/permutations/induction binders and fail-closed lookup; it adds no proof interface or audit admission. After ordinary main8bb/#529 integration, the incremental producer and official selected14-case/12-output Sync/Threadsync/IoGroup Gen preparation pass at7a934, with exactly116 tick insertions committedec0cba647. Remaining sumTo/cost controls, affected actual clients and alternate/native rows, full required output freshness, genuine inventory receipts and supported prepush are unqualified. The draft remains open, not READY.

Request: Derive one canonical instrumentation policy from existing whole-program memory/concurrency and original call-group classification, and use it consistently in Emit, Sem and Certificate for every supported version/backend and translate-c input. Preserve pure M/Result and viewed-slice behavior, exact full-Mem equality in loop/function certificates, and fail-closed excluded fragments. Exact boundary: a memory loop body that exits immediately now emits Zig.tick and returns ticks+1, while current Sem.execLoop/Certificate.loopCert return the old ticks. Unconditionally ticking Sem also changes pure/viewed certificates. Do not erase counters, add an unchecked caller Boolean/premise, duplicate graph analysis, reject previously supported memory loops, or claim support for the existing recursive-memory stack-frame certificate gap. Add matched positive and fail-closed controls before qualifying generated artifacts.

<a id="row-protocol-tick-transport"></a>
### #protocol-tick-transport Transport protocol observations and caller resources across composite ticks

Status: **open**. Requester: Task09 L8b-2; Task07 challenges; PR393 comments 6271005146 and 6278792907.

Note: A/1a/1b are approved, not pending. Darwin uses genuine spatial caller framing under the existing primitive contract (PR510/6287119784), without a wrapper tick; STD-06/OSL-01 debt is unchanged. The ignored-Plain adapter remains unapplied; neither nil parts nor cost=None imply resource admission. Every pass retains its original source/artifact identity. The unresolved orphan is kernel-rejected automation, not an accepted unsound theorem; no completed whole-client or cost-bound claim is made.

Progress: Maintainer approved composite ticks1b on PR510/6284852746 and the resource-polymorphic interface on6290377096; native atomic/futex Step/Aux stay exact. Generic caller-resource/Fits/Mutex/Word/IoMutex passes90 jobs at553e (#562 folds the caller-resource record into the `op_pre`/`op_post`/`op_unmetered_*` fields of MutexImpl/CondImpl; EventImpl.set keeps main's caller-part-free `set_wp`); actual Cond/Event caller-post/during-floor generics pass at0f64 after #529/main8bb integration. The single strengthened tick proof exposes exact m.ticked and derives old callback headers unchanged; that rule and real Deadline pass at079f. Real Sync.IoMutex and IoGroup.Lock constructor passes retain their original bindings. Existing affected program results and resource guards are explicit in D3; named Plain/unmetered specializations do not claim old unrestricted admission. Remaining native-Lake constructors fail at2361437d: actual signal tick observation is resolved, but applied simp-term generalization, nested decoder normalization and a rejected orphan Nat-to-Inv(wait) obligation need closure. The raw printer's outer-context warning does not prove variable escape. Separate generic engine proposals are source-only under the active engine writer, with no manual walk, new premise or limit increase. Actual retained families, alternate variants, current receipts and readiness remain pending. #599 (the multi-waiter CondImpl, no `hseen`) removes CondImpl's `signal_during`/`signal_unmetered_during` and with them the Cond during floor; Event's stays.

Request: Use existing Full triples and fsym to pay each composite tick from the current caller part and re-establish arbitrary observation U and the protocol invariant at exact m.ticked and the actual resulting setPart ghost state. Frame the complete held/protected resource, phase/role, rest and other threads. Preserve native LockWord.Step and Mem.Aux. Exact boundary: U(m):m.ticks=0 is stable under current native Step, whose Aux fixes ticks, but not after a tick from zero. Plain availability alone does not prove U transport; cost=None does not imply unmetered/Plain. A metered operation must expose its actual setPart post, not the original exact ghost state, and admission must cover internal busy phases rather than require lock-code ok. Resolve the common construction obligation without a new judgment, tactic, hidden premise or module-specific automation. Every approved public statement correction must list old/new contracts and carry D5 no-cost-bound reporting in the same correcting PR.

<a id="row-kernel-proj-ctor"></a>
### #kernel-proj-ctor Projections of values that reduce to constructors are left to the kernel as definitional steps

Status: **open**. Requester: L8e (Proofs.Sync.Cond loop56_body: kernel deep recursion, coordinator decision 2026-11-04: fix at the root, candidate (b)).

Progress: The kernel checks `((a, r).2).f =?= s.f` by comparing the projections' arguments first (`(a, r).2 =?= s`), by structure eta down to `r`'s fields; a literal field (`Packed.ofBits 65537#32 =?= s.prev_state`) then evaluates its arithmetic against an open term (no literal acceleration with free variables) until the recursion limit, an error rather than a failed comparison. Any definitional form of the step traps: `eq_self` unified up to reduction, simp's own `proj` step, and a `change`/`replaceTargetDefEq` to the reduced type (kernel experiment: `show s.f = s.f from rfl` at `(a, r).2.f = s.f`). Two explicit steps pass: the value against its constructor application, then the projection of the constructor application. Landed (claude/fsym-proj-ctor): `projCtorStep?` rewrites such a projection with those two `rfl` steps, and every fsym simp run takes it first (`fsimp`, `withProjCtor`, `lazyMethods`). Regression: sep-auto ProjCtorKernel (plain `simp only [eq_self]` on the goal is rejected by the kernel). Landed (claude/fsym-reduce-projs-eq): the engine's own reductions of projections are proof steps, one per projection. `unfold1Eq?` is `unfold1` with a proof: `projCtorStep?` with `unfold1`'s `whnfD`, else an `rfl` step of its own, also for a projection of a constructor application: two definitional steps (`(a, c).2` to `c`, then `c.f` to `s.f`) reach the kernel as the one comparison `((a, c).2).f =?= s.f` and trap (found on the row's counterexample). `reduceProjsEq`/`reduceCtorProjsEq` (`projsEq`) join those steps by simp's congruence (no lemmas, no reduction of simp's own) at the projections `reduceProjs`/`reduceCtorProjs` select, the result `reduceProjs`'s own. They replace the definitional installs at: arithGoals (unfolding, `And` split), destruct (etaProj's facts after `cases`, a user definition's fact), wpNorm, wpGoal (assertion, field step, unfolding, projection), wpHyp's unfolding, the update (side goals, its precondition `P₀`, `EUpd.frame` transported to `P₀ ⋆ R`/`Q₀ ⋆ R`), run's hypotheses (each a new local at the end of the context by `Eq.mp`, the old one cleared, the other locals kept; the run's substitution `caches.substs` records the old one as the new one cast back by `Eq.mpr`, so a caller's term that names it keeps its type, and `liveFVar?`/`wpCurrentHyp?` follow it), normPre, assumptionEq (also its unfolding of a Boolean argument), assnByHyp, proveEqGoal, the walk's protected recursive call (`recCommandView`, then `reduceCtorProjsEq`), the planner's postcondition (closeEntail's state `if`, closeEntail' `Q`/`Qi`/`Qi2` by `imp_eq` of the proofs, the stated `Q` kept), instQ/unfoldAtom/unfoldLeaves, withinParts, unfoldCmd (walk's inlining by `rewriteCmd`, recCommandView), wpWalk's inlining, the ThreadLocal unfolding, fsym_entail. Regressions: sep-auto ProjCtorKernel `fsym_post_epoch` (the counterexample), `fsym_hyp_epoch` (a hypothesis), `fsym_hyp_binder` (the hypothesis a binder after the colon) and `fsym_caller_term` (a caller's term `tick_spec _ h` naming the replaced hypothesis: with the new local itself the kernel rejected it), with the negative controls (`#guard_msgs`: the goal's reduced form installed by its type, and the hypothesis used at its reduced type, are rejected by the kernel).

Request: The projection steps that still reach the kernel definitionally. (1) Reductions that meet the stated form through unification, not a proof step: tryRule's command (`reduceProjs` after `unfoldToHead`/`expandMapLits`, `reduceCtorProjs` of a recursive command), a WP rule's command (`reduceProjs` of its command argument), the update's `Q₀` unified with the return's postcondition, `goalForms`/`hypIs` (a hypothesis closing the goal's reduced form), `pieceAtom`'s field values and `piecesF`'s list, `conjuncts`' `unfold1` of a user definition's fact feeding `blockFacts`/`solveBlock`'s unification; the matched goal would be rewritten by `reduceProjsEq` before unifying. (2) `projsEq`'s rest where simp does not reach (implicit and instance arguments, binder domains, dependent `let`s, proofs, a raw `.proj`): one definitional step from simp's result to `reduceProjs`'s (traced `reduceProjsEq: simp's … is not …`); and a field whose type depends on the value (an `rfl` step of its own: `congrArg` does not apply). (3) Reducible normalization at a head after an unfolding (`whnfR` in arithGoals and destruct; `wpGoal`'s `whnfR` of its goal installed by `replaceTargetDefEq`). (4) The tactic-syntax simp runs (`closeWith` with `simp only [fsym_arith] at *; simp only [*]`, `piecesEq`'s and the `Array.extract` `simp only`), which a simproc in the `fsym_arith`/`fsym_norm` sets would reach.

Workaround sites: `ZigLean/Sep/Full/Auto.lean`

Deletion plan: Transitional definitional projection steps in ZigLean/Sep/Full/Auto.lean: `retypeResult` (`projsEq`'s rest from simp's result to `reduceProjs`'s, arithGoals' `whnfR` after an unfolding), the `rflResult` step of a dependent field, and the reductions of request (1) that unification carries. Delete them when one proof-producing traversal replaces simp in `projsEq` (a congruence step at every argument, implicit and instance ones and binder domains included, a dependent field by `Eq.rec`), the matching sites of (1) rewrite the matched term by `reduceProjsEq` before unifying, and `projCtorStep?` is a simproc of the `fsym_arith`/`fsym_norm` sets for (4); then the `reduceProjsEq: simp's … is not …` trace goes, and `retypeResult` stays only for the `etaAll` step of `reduceProjsEq (eta := true)` (wpNorm, wpGoal), which is an eta reduction, not a projection step, and stays definitional; the row closes with sep-auto ProjCtorKernel as its regression.

<a id="row-lake-needs-race"></a>
### #lake-needs-race Lake 4.34 creates the jobs of concurrent `needs` facet keys twice and can deadlock

Status: **open**. Requester: lake-hang lane (arc hangs of the assurance extraction and kernel-replay builds, 2026-11-04).

Progress: Workaround: scripts/assumptions.py needs_first names each needed module's `:olean` on the command line before the generated modules, so Lake creates every job on its build thread before a library's `needs` tasks run. Upstream draft docs/upstream/lake-concurrent-needs.md (issue #131 row 17).

Request: A Lake whose facet keys in `needs` share one job per key (an atomic fetchOrCreate, or `needs` fetched on the calling thread), or whose Module.computeExportInfo does not await inside a sync continuation.

Workaround sites: `scripts/assumptions.py`, `tests/roadmap/fixtures-lake/test_needs_race.py`

Deletion plan: When a toolchain update fixes the race, the control assertion of tests/roadmap/fixtures-lake/test_needs_race.py fails. Then delete assumptions.needs_first (its callers build only the generated modules again), delete the test, and close this row.

<a id="row-case-family-enrollment"></a>
### #case-family-enrollment Remove transitional golden case-family enrollment markers

Status: **open**. Requester: Task23; coordinator decision 6258258831.

Progress: Enroll complete golden families through existing retranslation cases; Threadsync and Sync use no per-case selector.

Request: Every supported golden family becomes an unconditional case family, built side by side with disjoint generated APIs.

Workaround sites: `examples/threadsync/all-cases`, `examples/sync/all-cases`

Deletion plan: When the last golden family is enrolled, remove every all-cases marker and the marker/history ratchet, derive all case families unconditionally from the full golden enumeration, and retire when_defined with its remaining users. Preserve complete output/import coverage and exact retranslation checks.

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

Progress: arena_* macros gone (#388); `unroll_solo` deleted (L16). Open until 9h closes and the `within` macro, whose fsym_entail replacement 9g landed, has no uses left (proof-framework.json tactic_uses)

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

Status: **closed**. Requester: arena lane.

Progress: closed by PR #697 (on the `zig_run` simp set of #690): ArenaObstruction `client_illegal`/`reset_client_run` and ListsPage's runs name only their own client (`unfold client vt`) and unfold the generated code with `simp only [zig_run]` (singlePass), so no translation's loop numbering appears in a proof; proof-tools/Unroll `even_six_solo` names only its own test definitions.

Request: `unroll_solo` (Unroll.lean:56; users ArenaObstruction.lean:162, tests/roadmap/proof-tools/Unroll.lean): concrete counterexample runs, not program proofs. Proposal: a term-level use of `Unroll.expand` + `Sched.soloRun_apply_le` + `decide`, or a CTriple-backend mode; engine lane decides

Deletion plan: Done (PR #697): the hand-named unfold lists before `decide +kernel` are gone; each proof names only its client.

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

Note: vc_gen (ZigLean/VC/Extract.lean) called Auto.run until it was retired (L15): memory VCs are now fsym's residuals directly; tests/roadmap/sep-auto/SepAuto/Report.lean checks ordinary/reporting proof and residual identity

Progress: Auto.run is the shared entry of evalFsym (and was memVc's until vc_gen was retired), including introductions, context preparation, run caches and the orphan-proof check; runReport adds residual attribution to that entry

Request: One fsym entry for other front ends: expose `Zig.Full.Auto.run (g) (user : Array Expr) (extra : Array Syntax) : TacticM (List MVarId)` = what `evalFsym` does after elaborating its args (intros, `reduceProjs` of hyps, `withRunCaches`, `arithSimpCtx`, `walk … 400`); `evalFsym` calls it. `vc_gen` (ZigLean/VC/Extract.lean `memVc`) then calls it instead of re-doing `withRunCaches`/`arithSimpCtx`/`walk` and missing intros/reduceProjs

<a id="row-15"></a>
### #15 Quiet stop

Status: **closed**. Requester: one-logic-vc.

Note: vc_gen and its memVc were retired (L15), and tests/roadmap/vcs/Memory.lean now pins fsym's own reports. fsym.quiet then had no caller outside its test and was removed (L19): a reporting walk emits no human stop message, and tests/roadmap/sep-auto/SepAuto/Report.lean captures the stop messages it checks

Progress: Auto.runReport returns stop reasons without emitting a report message, and fsym.report emits schema-versioned JSON; a reporting walk emits no human stop message. The fsym.quiet option was removed

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

Request: (nice) An undecided side condition `φ` is split by `byCases`; the negative case leaves `hc : ¬φ ⊢ φ` (equivalent to `⊢ φ`). A mode that leaves `φ` unsplit gives one obligation and one walk

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

Workaround sites: `tests/roadmap/dispatch-templates/DispatchTemplate/Template.lean`, `tests/roadmap/dispatch-templates/TokenizerProof.lean`

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

Status: **closed**. Requester: sync lane.

Note: dead-module row 69 of agent 17; L9 row 69 keeps 69; this one is 69d

Progress: DONE (L21): deleted with ZigLean/Conc/Spec and MutexSpec. Its relaxed-unlock counterexample against MutexImpl is row mutex-impl-relaxed-witness.

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

Request: `Conc/OsRules`: proof-only premise evidence for OSF-01/02, OST-01/02, OSG-01 (docs/premises.md "Derived from", docs/os-threads.md); standalone by design (not dead). PLAN: its facts move into the full-state futex rules (the `Io` futex slots as `CTriple` rules when those land, docs/thread-specs.md), then the module is absorbed

Deletion plan: move its futex facts into the full-state OS futex rules (ZigLean/Sep/Full/OsFutex.lean) and the `Io` futex-slot CTriple rules when those land (docs/thread-specs.md, STD-05), then absorb the module.

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

Progress: PARTLY DONE: `FLock.Inv.loadRest` (ZigLean/Sep/Full/LockSteps.lean) proves the exact plain-load/read-record fact once, from invariant-rest bytes and the caller's NoRace premise. `FLock.Fits.wp_readRest` derives its existing shared-reader statement from that fact with ReadShared.noRace_read; its duplicated primitive proof is removed. The full-state copies in Iogroup/Counter, Handoff/Ops and MutexCounter/Protocol are deleted; their walks pass the protocol's obligations to the rule; SemCounter's copy is gone with its migration (PR648, `wp_readRest`). WaitGroup (#640) uses `FLock.Fits.wp_hold`; its legacy holder copies `wp_cntLoad`/`wp_cntStore` are gone. LEFT: the copy in the legacy-layer file RwLock (`ZigLean.Conc` logic, legacy_users), and the legacy holder copy Semaphore `wp_cnt`.

Request: **`wp_io` has hand copies**: the read of the `io` prefix (read-shared bytes in the protocol's rest, `FLock.Inv.recordX`, no race by `ReadShared.noRace_read`) is proved by hand once per protocol: `Proofs/Iogroup/Counter.lean`, `Proofs/Handoff/Ops.lean`, `Proofs/MutexCounter/Protocol.lean`, `Proofs/Sync/SemCounter.lean`, `Proofs/Sync/RwLock.lean`. Needed: one `@[fsym]` library rule over every protocol with a lock whose rest keeps read-shared bytes, each protocol discharging only its obligations (the bytes in the rest, the invariant kept by a read record).

Workaround sites: `Proofs/Sync/RwLock.lean`, `Proofs/Sync/Semaphore.lean`

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

Status: **closed**. Requester: P09.

Progress: DONE (R1, PR #717; approved with P09 2026-10-15). An unknown post at the top of a goal is inferred as before (`inferPost`, now over `strongestPost`, which takes any arguments). New: a return into an unknown that the walk infers (a registered loop's exit post that the engine created, the goal's postcondition also after a case split, `?Q true v`) applied to computed arguments is noted by the entailment (`noteExit`, after `decidePost` takes the decided conditions; an undecided exit condition is split on, so the exit's post carries it), never unified. When the unknown's walk ends (end of `Auto.run`; before a registered loop's continuation), it becomes the join of the returns' strongest posts, each with equations for its arguments (`finishExits`, `upd_join_l`/`upd_join_r`, checked before the assignment). A registered loop without `B.post` continues from the strongest post of its step's exits only if the step's walk closed every path (`⟪False⟫` if no exit is reached); a stopped step leaves the exit post unknown and the continuation a residual (`exit_post_not_inferred`), in every backend with a loop rule. The report lists the inferred posts (`posts`, `kind` `return`/`loop_exit`). Regression tests/roadmap/sep-auto/SepAuto/Infer.lean: total, partial and thread logics, function ends and loop exits, a too-strong caller post rejected, a step that stops before an exit, an exit post assigned before its join, a return without a strongest post, an undecided exit condition; LoopInv's concurrent loop without a post.

Request: strongest-postcondition inference at returns for FTotalTriple/FTriple and the thread backends, as `inferPost` does for WP segments

<a id="row-p09-e3"></a>
### #P09-E3 abduction report

Status: **closed**. Requester: P09.

Progress: DONE (R1, PR #717; approved with P09 2026-10-15). Each plan of a rule's precondition collects the atoms it misses (`noteWanted` into `planNotes`, `withPlanNotes`: only while a report is collected, each plan its own notes). A rule whose plan fails is kept for the step once (`notePlan`, in `tryRule` and `tryBindRule`; a retry with the same missed atoms adds no row). A stop with no rule, or an invariant that does not hold at a loop's entry (the loop rule's plan), lists them in its origin's `plans`: the rule, and each missed atom with its unknowns (`?u0`, … and their types). A view's walk that is rolled back restores the step's plans. Regression tests/roadmap/sep-auto/SepAuto/Infer.lean: a load from a state without the cell; a loop invariant that needs a cell the entry lacks.

Request: abduction report: at "no plan for its precondition", return the missing atom with its unknowns

<a id="row-p09-e4"></a>
### #P09-E4 @[fsym_inv] loop-invariant registry

Status: **open**. Requester: P09.

Progress: Approved by the maintainer 2026-11-05 (this engine case only: no new tactic, no new judgment). Generator done (lanes E4b/E4c, #701): `air2lean-invgen` emits `F.loopN.inv`, `F.loopN.meas` and an exit post `F.loopN.post` with `@[fsym_inv]`; the hand step and loop lemmas of loop-tactics/nested (`inner_step`, `inner_loop`) and loop-tactics/counted (the five `F_step`/`F_loop` pairs) are deleted, the callers' walks are bare `fsym`, and the mutants name the callers' theorems. Engine (lane E4, #688): the `@[fsym_inv]` registry of `B.inv`/`B.meas`/`B.post` (ZigLean/Sep/Full/AutoAttr.lean) and the loop case of `walkCore` (`loopInvRule?` in Auto.lean): at a loop no rule is about, the backend's loop rule (`FTotalTriple.loop_measure`, `FTriple.loop`, the thread forms, `CTriple.loop`) applied by `tryRule` with the registered definitions, unknowns planned at entry, frame inferred, the body's step walked as a goal of its own (regression tests/roadmap/sep-auto/SepAuto/LoopInv.lean; docs/proof-automation.md, §Loops). The exit post is registered too (`B.post`): without one the walk continues from the strongest post of the step's exits (P09-E2, closed), which keeps the exit's label and test. Open: nested's hand outer loop (deletion plan), whose invariant is outside the generator's families today.

Request: `@[fsym_inv]` loop-invariant registry: apply the backend's loop rule with a registered invariant and measure; parameters by the planner, frame inferred

Workaround sites: `tests/roadmap/loop-tactics/nested/Proof.lean`

Deletion plan: Nested's hand outer loop (`outerI`, `outerPost`, `outer_step`, `outer_loop`; `fsym` walks its step since #arith-atom-congruence, and its inner loop by the generated `@[fsym_inv]` definitions): delete when the generator also emits the counter-dependent outer invariant over `tsum` with a summary of the generated inner loop (S2c′) and `@[fsym_inv]` applies its loop rule.

<a id="row-p09-e5"></a>
### #P09-E5 @[fsym_upd] ghost-update registry keyed by heads, tried at returns

Status: **open**. Requester: P09.

Progress: pending maintainer approval

Request: `@[fsym_upd]` ghost-update registry keyed by heads, tried at returns; generalizes caller updates (9f); replaces #64–#67 workarounds with the bump-ledger family

<a id="row-list-walk-step"></a>
### #list-walk-step a list walk's step from its invariant: split the ghost list by the cursor's test, unfold and fold the list

Status: **open**. Requester: invariant-synthesis (P09, S2d: Proofs/Lists/Linked.lean, Proofs/Lists/Alloc.lean freeAll, loop-tactics/Queue.lean).

Progress: Found by R1 (2026-11-06, PR #717). The generator rejects the loops: `air2lean-invgen Proofs.Lists.Gen Lists` records reverse.loop6 and sum.loop6 as "an unsupported term: i8.isSome", and freeAll.loop5 as "an unsupported term: i7.isSome" (the S2d reading). The engine side is this row.

Request: At a list walk's step `T (∃ ys zs, ⟪xs = f ys zs⟫ ⋆ list X s.prev ys ⋆ list X s.cur zs ⋆ …) (B.run s) …` whose body tests the cursor (`s.cur.isSome`, a `match` on `?*Node`), `fsym` should case-split the ghost list `zs` (`[]`, with `cur = none`; `z :: zs'`, with `list X cur (z :: zs')` unfolded to `node X p z q ⋆ list X q zs'`, `list_cons`). At the repetition it should fold `node X p z q ⋆ list X prev ys` back into the invariant's list (`lseg_snoc` of the S3 list family). Today the hand steps `reverse_step`, `sum_step` and freeAll's step do the split, the unfolding and the fold by hand around `fsym`-proved fixed-shape steps (`reverse_tstep_nil`/`_cons`, `sum_step_nil`/`_cons`, `freeAll_step_nil`/`_cons`).

Workaround sites: `Proofs/Lists/Linked.lean`, `Proofs/Lists/Alloc.lean`

Deletion plan: When `fsym` walks these steps from the invariant and the generator emits the list-walk family (S2d), delete `revInv`/`revPost`/`sumInv`/`sumPost`/`freeInv`/`freePost` and the `*_step`/`*_loop` lemmas. The files then hold statements proved by `fsym` over the generated `@[fsym_inv]` definitions, and loop-tactics/Queue.lean builds on top unchanged.

<a id="row-arith-atom-congruence"></a>
### #arith-atom-congruence arithmetic congruence of library atoms (counter-dependent sums)

Status: **closed**. Requester: invariant-synthesis (P09, S2c′: `counted.tri`, `nested`'s outer loop).

Progress: DONE (E5, 2026-11-05): `arithCore` runs `omega` again, unless a probe, with the relevant facts each normalized against all the facts (`renormFacts`: a conditional rewrite whose side condition a later fact proves, `tsum_sub_of_lt` under the loop test) and the congruence of atoms (`atomCongr`: an atom `f t` of a function the solver does not read, a constant or a local, with `t` containing the side `l` of a fact `l = r` that is itself an atom, equals `f t[r/l]` in `fsym_arith` normal form; one step per equation, at `Nat`/`Int`). The library sum is `Zig.Full.tsum` (`ZigLean/Sep/Full/TSum.lean`, imported by `AutoAll`) with `tsum_zero`, `tsumSucc` (a bound `n + 1`, not a numeral) and the non-recursive differences `tsumSubLt` (`tsum_sub_of_lt` where the term `g x` is not `0`, whose right side would normalize back) and `tsum_sub_of_le`. Regression `tests/roadmap/sep-auto/SepAuto/AtomCongr.lean` (the side goals of `tri.loop5`'s step; negatives: a step of two, a bound, a missing loop test). Clients: `tri.loop5`'s step walks by bare `fsym` under `v + (tsum n id - tsum i id) = v₀ + (tsum n id - tsum i₀ id)` (checked in a scratch walk over counted's translation, not committed: the generator lane emits it); nested's outer loop is stated over `tsum` and `outer_step` is a bare `fsym [inner_loop]` (`cnt`, `cnt_mono` and the hand rewrite deleted; its hand invariant `outerI` stays until the generator emits it, S2c′ in docs/invariant-synthesis.md). Found by R1d (2026-11-05). The difference forms are non-recursive because a recursive conditional unfold (`x < b → S x b = x + S (x + 1) b`) hits the maximum recursion depth: in a context whose facts are contradictory the discharger proves every side condition.

Request: **Congruence of the arithmetic's atoms, as `modCongr` does for remainders**: the counter's step leaves a fresh word `x` with the fact `x.toNat = s.i.toNat + 1`, and the invariant's atom `sumBelow x.toNat` is unrelated to `sumBelow (s.i.toNat + 1)` (which `fsym_arith` rewrites to `sumBelow s.i.toNat + s.i.toNat`), so `omega` leaves `v' + (sumBelow n - sumBelow x.toNat) = w + (sumBelow n - sumBelow i₀)`. Needed in `arithCore`: for an application `f a` of a `Nat`/`Int`-valued function in the target or the facts, an argument `a` that the facts equate to a term `b` (by `congrEq`), rewrite it to `f b` (or add `f a = f b`) before `omega`, so the `fsym_arith` lemmas of `f` apply.

<a id="row-atom-args-normal-form"></a>
### #atom-args-normal-form an existential's witnesses against a state atom's unnormalized arguments (`List.set` of a literal list)

Status: **closed**. Requester: invariant-synthesis (P09, S2c′: `counted.pairAt`).

Progress: DONE (E5, 2026-11-05): the planner's `matchArgs` matches a constructor application of a pattern with metavariables (an existential's list `[?w₀, ?w₁]`) against a state value that is not one (not a number: the solver's) by the value's head normal form (`whnfD`, within `probeCaseBudget`), recursively, so the final match assigns `?w₀ := x`, `?w₁ := y`; the match is then proved by `proveEq` and checked by the kernel. Regression `tests/roadmap/sep-auto/SepAuto/AtomArgs.lean` (two stores into `arr p [a, b]` into `∃ w₀ w₁, … ⋆ up (arr p [w₀, w₁])`; negatives: swapped witnesses, a list of another length). Client: `pairAt.loop5`'s step walks by bare `fsym` under an invariant owning `arr p [w₀, w₁]` (scratch, for the generator lane). Found by R1d (2026-11-05). The item rules through the array's own pointer (`FTotalTriple.arr_load_zero`/`arr_store_zero`, merged with this row) make `fsym` walk `pairAt.loop5`'s body (`acc[0] += 1; acc[1] += 2`) under an invariant owning `arr p [w₀, w₁]`. A concrete target list already matches (`docs/proof-tools.md`: `arr p [x, y, z]`, store at `p.elem 4 1`, post `arr p [x, w, z]`); tagging `List.set_cons_zero`/`List.set_cons_succ` `fsym_norm`/`fsym_arith` does not change the residual.

Request: **Witnesses of an existential against an atom argument that needs normalizing**: `arr_store`'s post `arr p (vs.set i.toNat w)`, instantiated at a literal list and index, stays `arr p (([w₀, w₁].set 0 x).set (1#64).toNat y)` in the state, and the update into the invariant's `∃ w₀ w₁, ⟪…⟫ ⋆ up (arr p [w₀, w₁])` fails (`EUpd` residual): the witnesses `?w₀ ?w₁` are not found by unifying `[?w₀, ?w₁]` with that list. Needed: the walk puts the arguments of the state's atoms in `fsym_arith` normal form (literal `toNat`, `List.set` of a literal list at a literal index) before planning, or the planner unifies an existential's atom with a state atom up to that normal form.

<a id="row-recursive-group-total"></a>
### #recursive-group-total Generic total correctness of a recursive function group

Status: **open**. Requester: L8b-1 tick coverage (Task 09); P03/stack.

Note: Decision: https://github.com/riventic/air2lean/pull/393#issuecomment-6211327766 . The displayed goal identifies the missing generic entry point. The exploratory input containing per-program inductions elaborated, but that is not generic total-recursion coverage and no bare-fsym failure is claimed. The rejected scaffolding was removed. The separately scheduled feature closes the P03 memory-recursion/stack-budget gap.

Progress: The sequential group rules merged in PR #433 and the finite compiler-member/contract-only engine slice in PR #557, including the existing stronger thread-total companions. Parity (PR #597), all-input gcd (PR #613) and bounded factorial fact_total in Proofs/Recursion/Proofs.lean use rec_group with one fsym step per group; factorial retains n.toNat <= 12 and the separate 13! overflow boundary. Each of the three groups still closes its leftover per-item side goals after fsym with a hand `all_goals first | apply ...` dispatch over private lemmas: fsym's lemma chaining rejects equation conclusions (isChainConcl), and fsym [fact_mul_bound] does not fire because the leftover hypothesis keeps `p.toNat + (1#32).toNat = n.toNat` unnormalized (parity adds `(1#32).toNat = 1` by hand for the same reason). That dispatch is open matcher debt of this row. The isEven_isOdd_aux, gcd_spec_aux and fact_ok_aux compatibility projections (no consumer; only gcd_spec_aux and fact_ok_aux carry nonvacuity witnesses) remain public API; their retirement needs an explicit maintainer decision, and they are not deleted here. Proofs/Pointers/Sep.lean addDown_total proves the current generated MemM program with its exact accumulator result, current-thread token, original stack depth and unmetered mode: one fsym step, a strictly smaller input, nonoverflow and room for n+1 frames, including the base case. Its concrete start-memory witness has a real 32-byte stack reserve. addDown_group still transports its arithmetic-equal post-resource/value by EUpd.of_imp/of_eq, separation reordering and congrArg after fsym; this hand congruence is recorded below as open matcher debt, while addDown_sum_step is permanent per-item mathematics. This is generated-model progress only: recursive memory remains outside Certificate.fragment because AIR reference stack semantics is absent. tests/roadmap/loop-tactics/Recursion.lean (cited by docs/proof-tools.md) now consumes the public gcd, parity and bounded factorial contract projections, preserving its three theorem statements, each under a standard-axiom guard, without per-program generated-code induction. Unknown initial conditionals, native/P03 acceptance, entry-tick/producer integration, protocol clients and legacy retirement remain open. This row stays open.

Request: One general library rule per emitted recursive partial_fixpoint group: a contract for each member and a well-founded measure on the arguments. fsym must discharge each recursive call through the callee's contract at a smaller measure, with recursive frames charged to the stack-depth token (#402, STK-01). The same full-state framework must support sequential, thread and protocol clients without a new judgment, tactic, proof template or per-program induction. Exact exploratory goal: for `def recur (n : Nat) : MemM Unit := do Zig.tick; if n == 0 then pure () else recur (n - 1)` with `partial_fixpoint`, prove `FTTotalTriple (R ⋆ plain) (recur n) (fun _ => R ⋆ plain)` from a supplied invariant/contract and argument measure, with fsym walking the body. The existing `FTriple.admissible_fun` supplies partial correctness only; `FTotalTriple.loop_ghost`/`loop_measure` and their thread forms apply to Zig.loop, not recursive call groups. Per-instance `Nat.strongRecOn; rw [recur.eq_def]; fsym [ih]` is explicitly not the required API and is not retained as a workaround.

Workaround sites: `Proofs/Pointers/Sep.lean`

Deletion plan: Proofs/Pointers/Sep.lean (#617): the private `addDown_group`, which `addDown_total` applies, closes the postcondition by hand after fsym: `EUpd.of_imp`, two `sep_left_comm_eq` reorderings and `congrArg (BitVec.ofNat 64)` with `addDown_sum_step`, because fsym's frame planner cannot match `pts p 8 v` against `pts p 8 v'` when the values are equal only by arithmetic. Missing fsym capability: matching values that are equal by arithmetic (a kernel-checked value-congruence step in the frame planner, or an existential postcondition `∃ y, ⟪y.toNat = x.toNat + sumDown n.toNat⟫ ⋆ pts p 8 y` closed by `fsym_arith`). This capability is separate from this row's generic recursive-group rule (which is why no row of its own tracks it yet: open one when the engine work starts); delete that hand block from `addDown_group` and this site when it lands, and do not close this row while the site stays.

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

Note: Task02 nested-frame follow-up: closeEntail resolves every fresh frame occurrence before constructing its final AC proof. The first independent head receives the exact remainder and later independent heads receive emp; repeated, source-owned and already assigned heads are checked without assignment. Applied fresh heads use the existing bounded constant-abstraction pattern. The frame transaction restores metavariables and arithmetic caches together, and final AC reconstruction cannot infer a frame from a source atom. SepAuto.Updates checks the ordinary caller-contract path, bare/applied/dependent frames, shared-head refusal, explicit frames, empty remainders, source aliases, genuine False residuals and explicit kernel checking of completed direct EUpd proofs. This is a bounded planner correction, not global backtracking or heap contraction. Full TLS/Leak and client/bridge retirement remain open; the separately tracked current-context caller-proof transport must land before claiming the unchanged TLS exit walk.

Progress: part 1 (codex/fsym-fowned): the WP walk takes a thread's own stack block before its spawn through the registered `WP.liftMem_fowned` segments: allocation, field pointers (`Reaches.bauth`: the block's size from its extent), stores at byte offsets (`FTotalTriple.storeBytesAt`, Int offsets as generated code writes them), closed sizes of encodings (`reduceClosedSize`, kernel evaluation; closed side goals by `decide +kernel`); regression sep-auto WP `block_fields`; on Sync/Mutex `main` the walk reaches the spawn. Part 2 (codex/fsym-fowned2): the protocol's start at the spawn, so each `main` is one `fsym` call from `FOwned.start0_facts`: facts of a step's run (`@[fsym_run]`, `wpRunFacts`: `store_runFacts`, `alloc_runFacts`, `allocStack_runFacts`, `ptrProject_runFacts`, `load_runFacts`, `load_clocksLe`; a caller's run lemma such as `inv_spawn`), `inv_start` backwards with unknowns (`assnByHyp` unifies atoms up to unfolding), the child's ghost value from the protocol's `init` (a projection reduced, an equation that assigns the unknown), `inv_of_box` forwards (`wpForwardEx`: an `∃` conclusion at a stop), `wpAssumptionArgs`, `numAliases` (ThreadId), Boolean facts in `fieldEqs`, a conjunction's first part again after its second fixed an unknown; the hand bridges of Sync/{Mutex,Handoff,SnapshotCache} and Threadsync/{Mutex,Handoff} `main` are gone; regressions sep-auto WP `run_facts`, `thread_bound`, `same_pred`, `bool_case`, `and_retry`, `main_start`, `main_start_ex`. Open: the hand bridge sites of the other clients (Atomics/{MessagePassing,Relaxed,Stack}, Cancel/Group, Detach/Worker, Iogroup/Counter, Sync/{Cond,RwLock,RwLockSnapshotPair,SemCounter,Semaphore}, Threads/{Counter,Disjoint}, Threadsync/{Cond,WaitGroup}, tests sep-auto Threads, spawn-failure Group/Pair, thread-locals Counters), then the CM-form bridges and the alloc FTT ofSeq forms in Block.lean. Threads/Disjoint (PR #621): the post-join tail (two loads, the add, four frees) is one fsym call; the allocation/store prefix of main_spec still uses the hand bridges. That call passes `Array.size_setIfInBounds` (not registered in fsym_arith, so thread-count facts after a join need it) and `joinedAll_of_threads` (no fsym attribute transports a thread-only hypothesis across a step; Sync/{Mutex,Handoff,SnapshotCache} and Threadsync/{Mutex,Handoff} pass it the same way) as hints; both are open. Task 18 library follow-up (2026-10-19, change PR #461; approval PR #390 https://github.com/riventic/air2lean/pull/390#issuecomment-6259257096 and https://github.com/riventic/air2lean/pull/390#issuecomment-6260745106): the existing allocation/store run facts now expose the returned old block index, one-block allocation growth, store block-count preservation, and unchanged current/threads/atomics/waiters/woken/groups/clock count. All 19 positive sep-auto WP controls pass, including strengthened run_facts, two_blocks and two_blocks_loop through the existing WP.loop body inference; no engine change or missing generic-loop rule is claimed. Iogroup/Counter remains open: its unchanged main_spec diagnostic walks both allocations, owned projections 16/20 and all four initialization stores, then stops before the initial protocol invariant is admitted. wpForwardEx needs the invariant constructor's resource atom up (bytesAt gPtr ?A' 16 .stack ?bg), but the current atom uses the allocated pointer with block m_after_first.blocks.size, whose equality to 1 uses FOwned.start0_facts (no blocks at start), allocation growth and store block-count preservation together; the allocation facts alone allow arbitrary initial block counts. assnByHyp attempts only definitional matching when an atom contains any unknown witnesses; it uses proveEq only for a fully determined atom, so the known pointer equality is not used while inferring address/bytes. This mixed-atom match is the exact remaining step; later fixed-body matching is not isolated. The full extent is preserved (bext is bauth with Frac.one). The remaining clients, bridges and retirement conditions stay open; this library follow-up retires none. Follow-up from coordinator review https://github.com/riventic/air2lean/pull/461#issuecomment-6265159666 (not implemented in this PR): registered WP.liftMem_fowned in ZigLean/Sep/Full/ThreadOwned.lean currently forwards only current and threads from FStepIn. A load after alloc/store loses the groups equality in the coordinator's control; load_runFacts forwards only blocks. Forward the groups, woken, clocks.size and waiters equalities, plus the existing FStepIn.atomics AMap relation, through the generic wrapper for every MemM step, rather than adding per-primitive copies. This does not assert atomics equality for arbitrary steps: atomic stores can change that state. Keep operation-specific atomics equalities where their semantics justify them; the per-primitive current/threads conjuncts are redundant and can be removed with the generic follow-up. The two_blocks/two_blocks_loop controls and private Counter diagnostic select the final allocation with FTriple.allocStackDrop 16 8: this size/alignment hint is layout-sensitive, so review its generic mode-selection boundary before relying on it in migrated clients. These wrapper and hint follow-ups remain open and add no code to this PR. Task18 generic wrapper follow-up (approval https://github.com/riventic/air2lean/pull/461#issuecomment-6265159666): WP.liftMem_fowned and the existing total wrapper now forward the same actual FStepIn hF m m' alongside the ownership post and the guaranteed current/threads/waiters/woken/groups/clocks.size equalities. Atomic transport remains the exact frame-indexed existential AMap relation, not arbitrary atomic-array equality. All 28 explicit narrow callbacks are adapted without changing client statements. Four forwarding WP controls and the actual direct-caller modules compile. This implements only the generic-wrapper slice; Counter, mixed-atom matching, the layout-sensitive Plain/drop boundary and all last-user/client retirement conditions remain open. Task18 mixed-atom matcher follow-up (approved https://github.com/riventic/air2lean/pull/461#issuecomment-6278476415): the existing assnByHyp first preserves its whole-context original search, then uses existing matchArgs plus a checked whole-atom proveEq for mixed unknown witnesses. Source occurrences are indexed and transported by typed congruence, so identical atoms retain multiplicity and one occurrence can be rewritten without changing another. Matcher candidates and whole-hypothesis refusals restore the same-start Meta state and existing five arithmetic cache fields; actual main's public fsym entries already prepare the arithmetic context before the walk. This is a finite matcher boundary, not a global repair of proveEqGoal internal restore paths. Eleven identical canonical WP controls were checked against old main8bb and the candidate: four old refusals (single-occurrence rewrite, mixed duplicates, Counter-style initial-index equation, failed-first/later-valid candidate) now pass, while old-priority and wrong pointer/address/bytes/resource/multiplicity controls remain passing. The unchanged Counter and all 409 official ROOT targets compile. The real Counter migration still needs start0_facts' zero-initial-block fact together with allocation/store counts; no empty-memory seed or new client proof is added. The wrapper-forwarding follow-up (#551) is merged. Actual client migrations, Plain/drop mode selection and every last-user/bridge retirement criterion remain open; no row closure or legacy retirement is claimed. Task18 actual-main Counter diagnostic (2026-11-04, after merged #551/#555 at b8b302c5): an unchanged-statement one-fsym candidate seeded real FOwned.start0_facts and selected only the final 16-byte allocation with existing FTriple.allocStackDrop 16 8. The actual module walk passed both allocations, owned projections and all initialization stores. Supplying existing WP.loop/spawnInv/spawnPost/loop13_body still refuses the fixed loop-body contract: the command uses a group pointer with block m_after_first.blocks.size, while loop13_body uses gPtr (block1), although the context contains the checked allocation equation m_after_first.blocks.size=1. A documented trace isolates Auto.wpRule command matching (unifyKeyed) refusing this non-definitional contextual equality; WP.loop itself unifies, then its fixed-body step remains. This is fail-closed incompleteness, not a soundness finding or absence of a generic loop rule. Recommend general kernel-checked contextual command-argument equality transport before WP contract matching, preserving speculative rollback and unknowns; reject per-client pointer rewrites or wrapper proof walks. Initial spawnInv/resource inference and subsequent await/join/free obligations remain unqualified. The three failed candidates' original source snapshots, guard reports and full logs were preserved before worktree archival, on the maintainer's development host only (not reachable from a checkout or CI), at `~/.cache/air2lean/handoffs/task18-counter-blocker-20261104/` (original 39-file manifest `ea4825b7d2a6d4ec5423eb8a2701ba0646d16ba62ddc80b077aa48e1d0f27baf`; separate `ready-phase/manifest.json` `92768308550700834272f136a1b9fa45c6359807323003be170f2ce323572331` covers five further files). The later `~/.cache/air2lean/handoffs/merged598-cleanup-20261104/` supplement (manifest `81a359910dc8896d11643814ed658617459c43358bef178f2cba29bb88e36622`) references those retained files. PR #598 records the measurement (the candidate, the refused contract and the equation); it and this row are the public account of the obstruction. No engine change, new premise, weakened statement or failed proof is committed, and the working Counter source of that date was restored. Counter's proof has changed since, so the diagnostic describes the 2026-11-04 source; a re-measurement starts from the current Counter statement and re-checks whether the command-argument mismatch still occurs. This row and all client/bridge/legacy retirement obligations stay open.

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

Progress: PR397 implements permanent AMap/Word floor and Fresh transport, actual native primitive producers, WordRules callbacks and Event/Cond MStep consumers. The approved joint LockWord.Step.locs cut uses its actual unchanged/first-address replacement/first-address append equation, with native first-index/full-record and new-record lemmas; every direct producer and internal locIdx result migrates together. The native modules and actual Sync/Threadsync Handoff clients compile, and malformed overlapping/duplicate-record controls check. The source/artifact-bound a0fe64d8a audit established zero registered legacy or adapter dependencies for native producer/consumer and real Handoff client paths, retaining all roots including thirteen old exports. Takeover6277249661 removed six exports with no external callers: Protocol.U_frame/U_own/keepK_of and Word.keepK_fstep/keep_lockWordStep/keep_waiters. Fresh source/artifact-bound qualification at65138df91 retains all2364 declaration roots,1703 theorem records and89 fresh kernel replays; every native producer/consumer and real Handoff client remains legacy-free, and all retained theorem statements match the prior report. Exactly seven old roots remain visible: Word.BlkStep.eq_set, Word.Op.block/fpAt/lockLoc/rest/word and FLock.Inv.wordOp. The earlier thirteen-root count is historical. Generic actual read/fork validity-history lemmas and direct FStepIn.afterAlloc fields preserve their headers. Existing Event/Cond singleton contracts and remaining old Word contracts stay open debt; this is not whole-module strict-zero, completion or reclassification. The source-only epoch-ABA schedule fact that ruling6264821278 requires first is kernel-checked: `FCond.epoch_aba` (`ZigLean/Sep/Full/CondEpoch.lean`) runs the model's actual epoch load, state RMW, weak CAS, epoch RMW and futex wake/wait ops of one round, not the mutex's unlock and lock between them (the waiter registers, the signaller posts and bumps the epoch, the waiter's futex wait returns and it consumes), proves the round's effect on (state, epoch) as `(1, 0), e -> (1, 0), e + 1`, iterates it `2^32 - 1` times, and a last signal leaves the state `(1, 1)` with the epoch back at the saved value, so the saved waiter's futex wait sleeps with its signal pending. The newest-choice op lemmas it uses (`Word.Ok.load_newest`, `rmw_newest`, `weakCas_newest`, `futexWait_newest`, `apart_run`, `Thread.futexWake_run_idle`) are general (`ZigLean/Sep/Full/WordNewest.lean`). It is a fact about op runs, not a scheduler run, and does not refute the singleton theorem. Next: the general Cond admission/accounting contract with the `< 2^32` save-to-enqueue window, then the singleton instance. The semaphore is off the one-waiter workaround (PR #575, on #599's multi-waiter `CondImpl`): `SemImpl` has no `hone`; `FSem.Inv` tracks takers (waiters back from the condition that relock the mutex) and a snapshot at `pst`, so a sleep with permits has a `pst` holder or a taker that runs (`FSem.Fits.live`); `FSem.Fits` carries the window `win` as `FCond.Fits` does, and `ioSem` proves the contract for any number of waiters and posters. `ZigLean/Sep/Full/Sem.lean` and `Proofs/Sync/IoSemaphore.lean` are no longer workaround sites. L8j (2026-11-04) split Conc/Word: the legacy-independent word vocabulary is ZigLean/Conc/Base/Word.lean, which Full/Word now imports instead of Conc/Word, so no full-state module reaches the legacy layer through it. The old Word-contract family stays in the legacy ZigLean/Conc/Word.lean, statements unchanged: Word.Op with its legacy LocsKeep field and producers, the step records BlkStep/AtomsStep/Keep/KeepK with their lemmas, and the seven old roots Word.BlkStep.eq_set, Word.Op.block/fpAt/lockLoc/rest/word and FLock.Inv.wordOp, moved there from Full/Word. It leaves with Conc/Lock (stage D-d).

Request: Complete the existing full-state Event/Cond multi-waiter contracts using caller-local seen floors, selected-subset wakes and sufficient actual broadcast counts. Derive general Cond admission/accounting over all en/ld/reg phases and finite ghost-admitted support. PR397 ruling6264821278 selects fewer than 2^32 epoch increments during save-to-enqueue, discharged by existing client cost/admission resources, with unconditional safety and the exact singleton instance. First kernel-check the source-only epoch-ABA one-round/iteration schedule fact; it is not a checked singleton refutation. Do not require every translated implementation to prove the rejected sleeping-thread liveness assumption. Keep existing client results and derive singleton/owned-ledger instances. Native-ID capacity, reservation and physical-exit accounting are the separately approved D2 change. Before READY, qualify the coherent native producer/consumer boundary required by corrections6269584785 and6273571981: actual primitive-run RestStep, actor-normalized AMap, counter, validity, history, result, exact-index and raw-block facts; WordRules callbacks; both Event/Cond MStep families; every affected Handoff client. Preserve exported Event/Cond/Impl/Handoff statements and strength. No client premise, weaker result, adapter, renamed record, reclassification or module-specific proof walk; do not hide capacity in Fits.

Workaround sites: `ZigLean/Conc/Word.lean`, `ZigLean/Sep/Full/LockWord.lean`, `ZigLean/Sep/Full/Word.lean`, `ZigLean/Sep/Full/WordRules.lean`, `ZigLean/Sep/Full/Event.lean`, `ZigLean/Sep/Full/Cond.lean`, `Proofs/Handoff/Protocol.lean`

Deletion plan: Before PR397 is READY, remove the obsolete Word.Op/LocsKeep/BlkStep dependency from every actual new native producer and consumer path, including the shared Fits.stable -> Full.LockWord.Step boundary. Cover preparation, load, all signed/unsigned RMW orders, strong and weak CAS including spurious failure, wait and OS-wait, every WordRules/Event/Cond consumer and retained Handoff result. Check every changed root's actual body and full type, including inherited dependencies, against fixed source/artifact bindings. The inline native Step.locs field must retain both former obligations; retained producers prove its stronger actual array equation. No AMap-to-LocsKeep conversion is allowed. The six unused Word/Protocol preservation exports identified in6277249661 are removed now, rather than deferred as frozen compatibility wrappers. Remaining Word.BlkStep/Op projections and FLock.Inv.wordOp are reported as the old Word-contract family, never as native; retire that family together with its shared legacy producer contracts after their other old consumers migrate. This boundary does not close the row: remove Event/Cond one-waiter/newest-HB workarounds only after general contracts, singleton/owned-ledger instances and multi-waiter regressions are kernel checked. Close only when all listed workarounds and retained old exports are gone and the applicable strict new-fact graph passes.

<a id="row-cond-epoch-load-floor"></a>
### #cond-epoch-load-floor The condition waiter's epoch load has a floor, so contended clients can prove the window

Status: **closed**. Requester: L10j SemCounter on SemImpl (helper SC, after #575; coordinator decision 2026-11-04).

Note: Coordinator decision 2026-11-04 (approved as fix steps 1-2, same class as #599's SigStep tightening: stronger for clients, implementations prove more, no statement weakened). The per-client bound (at most one epoch write per registration) is each client's proof, starting with SemCounter.

Progress: CLOSED by option (a) (coordinator decision 2026-11-04, PR #631): the `FPrim.ofWords` Move step carries the lock's word invariant `L.WInv (L.pl G) m` at the state before the step; `Fits.back`/`Fits.wStep` take it and every word rule passes stopW's `hiL.w` to its callback. `U` itself cannot carry holder uniqueness, because `FLock.Fits.stable` admits a lock step of an `ok` thread to any ghost place, so `U` must tolerate two ghost holders; the pre-state `WInv` at Move gives it instead. New `FCond.ld_newest`: with `FLock.WordHB L C.Ep` before the step, an `en -> ld i e` step saves the newest epoch write (`i = size - 1`) and keeps the epoch's writes. #630's `FCond.EpHB` lemmas became the word-generic `FLock.WordHB`, `.last`, `.step`, `.lstep` (ZigLean/Sep/Full/Word.lean; review of #630). No contract statement (MutexImpl/CondImpl/EventImpl/SemImpl) changed its text; their `Fits` premise now gives a client's `kstep` the lock's word invariant before a step (stronger for clients; every implementation supplies it through the word rules). Before it, #630 gave `en -> ld i e` the load's floor in `FCond.SigStep` and pinned the registration `ld -> reg i jr`, both proved inside the library rules. Remaining: two or more registered waiters, row `cond-window-multi-waiter`.

Request: `FCond.prim` did not constrain the waiter's epoch load `en -> ld i e` (`SigStep` covered only `out -> sl` and `sl -> inc`), and `FCond.Inv.ld` asked only `i < size`, the value and write `i` before the waiter. Counterexample: A waits while B holds the permit; B posts, signals (`epoch += 1`) and unlocks; A consumes, relocks, finds count 0 and loads the epoch, saving write `0` by a ghost choice; it registers and unlocks; B relocks and posts again. After `2^32 + 1` rounds A is at `reg 0` with more than `2^32` epoch writes. So `FCond.Fits.win` (and `FSem.Fits.win` via `Fits.toC`) failed for every client in which a waiter registers again under contention (SemCounter: 2 threads, 4 posts); no invariant could bound `size - i`. It is not unsound: merged proofs stay valid, but `CondImpl`/`SemImpl` were unusable by such clients.

Deletion plan: Closed: `FCond.prim` gives the load its floor, every condition implementation proves it from `Word.Ok.load` (#630), and the step carries the lock's word invariant before it, so a client with every epoch write before the mutex's holder (`FLock.WordHB`) gets `i = size - 1` at `ld` (`FCond.ld_newest`).

<a id="row-lock-stable-inv"></a>
### #lock-stable-inv A lock step's U-stability may use the lock's invariant before the step

Status: **closed**. Requester: L8p two-lock product (LockPair.lean), review of #683; maintainer decision 2026-11-05.

Note: Maintainer decision 2026-11-05: the client gets more (the lock's invariant), and no rule or statement it relies on is weakened; every library site that applies `stable` has the pre-state invariant. Maintainer decision 2026-11-05 (option (a), L8q's obstruction 5): `stable` also gets the transfer the rule makes. With `h` universally quantified a two-lock product's `U` cannot place lock A's held resource in lock B's rest, which B's invariant needs after A's critical-section step (`FOwned.move`). Counterexample: at A's acquire take `h := {d ↦ w}` with `d` outside B's rest; the coupling is false, yet `stable` demanded `U`. Rejected: (a2) the post-step invariant (pins `h` only for a precise `R`), (b) a ghost free resource (changes `FLock.Inv`), (c) fixed footprints and (d) strict nesting only (not general).

Progress: CLOSED in #667: `FLock.Fits.stable` takes `L.Inv G rX m` (the state before the step) beside `U G rX m`, and so do `Fits.ofLock`/`ofLockAll`'s `stable` argument. `Fits.step`/`Fits.stay` take it, and every rule that applies them passes the lock invariant it already has. `FSem.Fits`/`FCond.Fits` extend `FLock.Fits`, so they inherit it. Clients that do not need it ignore the binder. Second step, decision (a) on #693 (L8r): `stable` also takes `L.Transfer G rX m m' t p h`, the resource the step moves: without the lock afterwards `h = rnil`, a holder that stays one keeps `L.held (G t)`, at an acquire the lock was free and `h` is its resource before the step (`L.Free G ∧ L.FreeRes G rX m h`; `FreeRes` is now `Inv.rest`'s body), and at a release the free resource after the step is the old held one. `Inv.acq`/`Inv.rel` return those `FreeRes` facts, `Transfer.none`/`stay`/`acquire`/`release` build it, and every rule that applies `Fits.step` passes it; `ofLock`/`ofLockAll` and the seven client `stable` lemmas take the binder.

Request: In a two-lock product the client's `U` for lock A must stay over a step of lock B's code, and that needs B's facts such as `B.BlkOk m` (the other lock's blocks), which live in `B.Inv`, not in `U`. Without the hypothesis the product's `U` would have to repeat `B.BlkOk` and every step kind (lock, primitive, part tick, stop) would have to re-prove it, duplicating `FLock.Inv`.

Deletion plan: Closed: no workaround; the hypothesis is part of the final `Fits` contract.

<a id="row-cond-window-multi-waiter"></a>
### #cond-window-multi-waiter The condition's epoch window with two or more registered waiters

Status: **open**. Requester: L10k (review of #630/#631, 2026-11-04).

Note: Not unsound: `win` is a client obligation, so merged proofs stay valid. No client in the tree has two or more registered waiters on a `CondImpl`/`SemImpl` yet.

Progress: PARTLY DONE. Maintainer decision 2026-11-04: premise + narrow `win`. Narrowing DONE ([PR641](https://github.com/riventic/air2lean/pull/641)): `FCond.Fits.win` / `FSem.Fits.win` ask `(C.Ep.hist m).size <= i + 2^32` only for a waiter on its way to its futex wait, `reg i jr false e` with `C.qd m u = false` and `m.woken.contains u = false` (the one use, `waitEpFacts`' sleep, has both); a queued waiter, a woken one (a wake moves it from the queue to `woken` while its place stays `reg i jr false e` until its return) or one back from its wait (`sn`) is not asked, which closes the second case. With at most one registered waiter at a time a client bounds it per registration (`FCond.ld_newest`, row `cond-epoch-load-floor`). OPEN: the quantitative premise for the first case has no sound way into a proof yet. Any form of it as a fact about the protocol's states (`U`, a `Fits` field, a hypothesis on `U`) is false in the model: `U` is closed under every step the primitive admits, and the counterexample's states are reached by such steps, so a claim with that hypothesis would be vacuous. A premise on runs (an obligation on schedules) needs one of: (M1) an opt-in futex window in the model (with it, a futex wait by `t` on a word that has had `2^32` or more writes after `t`'s last access (`Mem.seen`) ends the run as a premise stop, as STK-01 does for the stack, and the sleep's `hwin` comes from the model; claims with the opt-in list the premise); or (M2) an opt-in `Proto` field whose `run_sound`/`run_safe` quantify over the runs whose futex waits satisfy the window, with `Proto.Step .wait`'s sleep obligation only under it. Both change the framework or the model: maintainer decision.

Request: A client with two or more registered waiters and no bound below `2^32` on its total posts (a long-running one) cannot give `win`; one with fewer posts bounds the epoch writes by them. Counterexample: waiters A and B registered, a poster P; A is not scheduled after its registration, or it reloads the epoch in its wait loop (`reg i -> reg i'` outside the mutex) keeping `i' = i`; P signals, B consumes and registers again, P signals again; after `2^32` rounds A is at `reg i`, not queued, with more than `i + 2^32` epoch writes. This is the ABA of std's comment in `Condition.signal`. Second case: under an unfair wake a queued waiter can stay queued while the others take more than `2^32` signals. Narrowing `win` to waiters not yet queued closes only the second case (A is not queued); an eventual-fairness premise gives no bound.

Deletion plan: Closes when the quantitative premise (a registered waiter reaches its futex wait before `2^32` further epoch writes) has an ID in docs/premises.md and assurance/premises.json and a mechanism (M1 or M2 above, maintainer decision) by which a client with two or more registered waiters meets the narrowed `win` and lists the premise.

<a id="row-sem-go-code-moves"></a>
### #sem-go-code-moves The semaphore's holder moves (`FSem.Go`) are not tied to its code

Status: **closed**. Requester: L10k (SemCounter over SemImpl, 2026-11-04).

Note: Coordinator decision 2026-11-04 (approved: a contract tightening, stronger for clients, no statement weakened). Not unsound before: `Go` was too permissive for clients, not for implementations; no in-tree client of `SemImpl` existed.

Progress: DONE ([PR636](https://github.com/riventic/air2lean/pull/636)): `FSem.Go` admits `.wt` only from `.out`, `.pst` only from `.out` or from `.wt` with `S.cnt G != 0`, `.out` from `pst` as before, and staying in place. `wp_lockWt` (from `out`, new premise `S.ph g = .out`), `Fits.wp_take` (from `wt`, its `hnz`) and `Fits.wp_give` (from `out`, new premise `S.ph g = .out`) meet it through `U_pst`'s source premise; `ioSem` passes `SemImpl`'s existing `S.ph g = .out`. The per-registration bound (at most one epoch write while a waiter is registered) is each client's proof. The first is SemCounter's migration over `SemImpl` (legacy user `Proofs/Sync/SemCounter.lean` in assurance/proof-framework.json).

Request: `FSem.Go` (ZigLean/Sep/Full/Sem.lean) admits `s = .wt` and `s = .pst (C.S.hist m) clk` from any place, and `Move.hold` and the condition's steps keep the client's ghost `x`, so the count stays. Counterexample for a client `U` that must hold `win` (`S.Fits`): threads u and v, v holds the permit (count 0), u registered at `reg i` with `i` the newest epoch write, v holding the mutex in `post`. v repeats: `Move.hold` with `Go .pst`; signal (`out -> sl -> inc -> wk -> out`, one epoch write); `Move.hold` with `Go .wt`; `Move.enter` at count 0; `en -> ld -> reg`; consume a signal (`reg -> out`). Every step is admitted by `S.prim` with both invariants after it (`Inv.hold`, `Inv.enter`, `Inv.cstep`), and its start state is reachable (the poster after `MutexImpl.lock_wp`), so `U` contains the states after `2^32 + 1` rounds, where `(C.Ep.hist m).size > i + 2^32` with u at `reg i`. The real `Io.Semaphore` code never makes these moves. Proposed: `.wt` only from `.out` (wait's lock), `.pst` only from `.out` (post's store) or from `.wt` with `S.cnt G != 0` (wait's take), `.out` from `pst` as now, and staying in place.

Deletion plan: Closed: `FSem.Go` is restricted to the code's moves (stronger for clients). The semaphore rules meet it with premises their callers already have: `SemImpl`'s `S.ph g = .out`, now also a premise of `wp_lockWt` and `Fits.wp_give`, and the take's count not 0.

<a id="row-sem-wait-role"></a>
### #sem-wait-role The semaphore's wait is open to every thread, so a permit's holder may sleep at the condition

Status: **closed**. Requester: L10l (SemCounter over SemImpl, `hlive`, 2026-11-04).

Note: Coordinator decision 2026-11-04. Not unsound before: `hlive` is a client obligation, and no in-tree client of `SemImpl` existed.

Progress: DONE ([PR639](https://github.com/riventic/air2lean/pull/639)): `FSem.wx : γ → Prop` is the client's waiting role next to the condition's `sx`, with the iff laws `wx_l`, `wx_part`, `wx_c`, `wx_s` (the lock's, the part's, the condition's and the semaphore's updates keep the role, like `FEvent.wx_set`). The role is a property of the ghost value, not of the op: a client keeps every thread it counts on to post out of it, also in `post`'s tail. `FSem.Go` admits `.wt` only from `.out` with `wx (G t)`, and `Move.enter` needs `wx (G t)`. `wp_lockWt`, `wp_cwait`, `SemImpl.wait_wp_resource` and `SemImpl.wait_wp` take `wx g`; `post` is unchanged. `ioSem` passes it on. A client names the threads that may wait (SemCounter: the client part `work k false`, not the permit's holder).

Request: `FSem.Go` admits `.wt` from `.out` for every holder of the mutex, so `SemImpl.wait_wp`'s `hlive` (a waiter's sleep at count 0 is no deadlock) is not provable by any client in which a thread that will post can hold the mutex. Counterexample (two threads, one permit held by v, count 0): u waits in `wait`, registers and sleeps at the epoch; v calls `post` and holds the mutex at `out` (after `MutexImpl.lock_wp`); v takes `Go .wt` (`Move.hold`), `Move.enter` (holds, condition `out`, `wt`, count 0), loads the epoch and registers; v unlocks (a calm lock step: `ok` cannot tell `wt` from `out`) and sleeps at the epoch. Both threads sleep, no signal is pending, nobody signals, the count is 0 and `P.inv` holds, so `hlive` would need `P.Live u`, which is false. No `U` excludes it: the client part is untouched by the lock's and the primitive's steps. Proposed: a client-chosen waiting role `wx` that `Go .wt` and `Move.enter` need.

Deletion plan: Closed: the waiting role is part of the semaphore's contract (stronger for clients, no statement weakened). Rejected alternative: a separate `SPh` place for `post`; the permit's holder would still take `Go .wt` from `out`.

<a id="row-sem-hold-rest-inv"></a>
### #sem-hold-rest-inv The semaphore holder's step keeps the rest but does not give the lock's invariant after it, so no client's rest keeps the condition's cells

Status: **closed**. Requester: L10n (SemCounter over SemImpl, `kstep` at `Move.hold`, 2026-11-05).

Note: Coordinator decision 2026-11-05 (approved on PR644). Not unsound: `FSem.Fits` is a hypothesis of the semaphore's rules, and `IoSemaphore` proves the rules against it (the contract was unusable, no theorem was wrong).

Progress: DONE ([PR644](https://github.com/riventic/air2lean/pull/644)): `FSem.Move.hold` takes `(∃ G'', L.Inv G'' rX m')` after its `FStepIn` premise. Its three producers already have it: `Fits.move` (the same memory, `hL`), `Fits.wp_cnt` and `U_pst` (their `hL'`). `Sem.lean` and `Proofs.Sync.IoSemaphore` build unchanged otherwise.

Request: `FSem.prim.Step` by `Move.hold` keeps the rest `rX` while the memory goes to any `m'` with `FStepIn (wordR ∪ rX) m m'` and the condition words' cells equal to `m`'s only up to `Cell.norm` (which drops the block size and normalises the kind). `FStepIn` does not constrain heap contents outside the atomics and the footprint. `FLock.Fits.sub` makes every `U` imply `S.prim.Sub`, whose `(C.prim L).Sub` needs `rX = rsum (W.cellsR m') rY` with the exact cells (`cellsAt` keeps size and kind). Counterexample (not kernel-checked): a reachable state in which thread `t` holds the mutex with the condition at `out` (after `post`'s lock); `m'` is `m` with block 0's byte array one byte longer. `FStepIn` holds (threads, waiters, clocks, footprint and atomics unchanged with `σ = id`; message coverage kept, blocks only grow); the word cells are equal up to norm; `Go` stays; `S.Inv` and `C.Inv` hold after it (they read places, histories, clocks and waiters). `Sub` fails at `m'` (`rX` has the old size's cells, `cellsR m'` the new ones), so `kstep` needs `U` at a state where it cannot hold: no client can instantiate `FSem.Fits` with a state where a thread holds the semaphore's mutex. Every other step that keeps the rest has the lock's invariant after it (`FPrim.ofWords`' own-part step, the lock's steps), from which a client pins its block through the extent in the rest (Handoff `blk_of`, `cells_same`).

Deletion plan: Closed: the lock's invariant after the step is part of the semaphore's contract (stronger for clients: fewer steps for `U` to keep; no statement weakened). It does not replace the step's cells premise, which also needs `Sub` at `m` (`FCond.cells_of_inv`), not a premise of `Move`. Rejected alternatives: change the rest to the new cells as `FPrim.ofWords` does (`rX' = rsum (W.cellsR m') rY`): it needs the rest's split at the step, which `Move` does not have, and the lock's invariant after the step is still needed for the client's other cells; ask `FStepIn` to keep heap contents: a change of the memory model's step relation used by every triple.

<a id="row-sem-take-index"></a>
### #sem-take-index The semaphore's wait fixes the taken resource and the waiter's new ghost value before the call

Status: **closed**. Requester: L10m (SemCounter over SemImpl, the take, 2026-11-04).

Note: Coordinator decision 2026-11-05. Not unsound before: the fixed `T`/`gx` was only too weak for clients, and `ioSem` was the only implementation.

Progress: DONE ([PR642](https://github.com/riventic/air2lean/pull/642)): `SemImpl.wait_wp_resource` and `SemImpl.wait_wp` take `gx : (ThreadId → X) → γ` and `T : (ThreadId → X) → FAssn`, indexed by the client parts at the take, `Y = S.xs (upd G t g)` with `G` the take's state (the one the premises quantify); `hcnt`, `hpool` and `hU` are at `gx Y` and `T Y`, the `gx` premises hold for every `Y`, and the post returns `Y`. `ioSem` proves it. `post` is unchanged. A client with a fixed `gx`/`T` passes constant functions.

Request: `SemImpl.wait_wp_resource` fixed `T : FAssn` and `gx : γ` before the call, but the pool's contents at the take depend on the other threads' steps since the call. Counterexample (SemCounter, the pool owns `n = sum X`): `T` must admit every value (`∃ v, pts n v`); thread 1 did one round (`work 1 false`), thread 0 takes `r = pts n 0` while `sum = 1`, and `P.inv` holds after it because `U` cannot see `n` (a thread's part is not `U`-stable: `FPrim.ofWords`'s own-part step admits any part; `Move.hold`'s frame leaves `n` unconstrained). Thread 0 loads 0, stores 1 and posts `rT = pts n 1`, so `post`'s `hpool` needs `pts n 1 ⊢ pts n 2`, with a satisfiable premise. No `U` makes both `wait`'s `hU` and `post`'s `hpool` provable.

Deletion plan: Closed: the index is part of the semaphore's contract (stronger for clients, no statement weakened). Rejected alternatives: index only `T` (nothing links `Y` to the state at the post); give `hU` the pool premise (`U` cannot keep facts about a thread's part); a ghost token (`Res.gh` has no user ghost state).

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

Note: The on-demand view extension records the full current requested-known multiplicity with the intact failed target on the right of a combined FAssn demand. The selected view proves only missing copies from its own nonempty byte/region source; actual-state occurrence coverage preserves original and committed-residual baselines, full frames, zero-size/no-request behavior and the true known-only/opaque/multi-atom target. Source probes pair rejected/exceptional Lean rollback with existing saveArith while propagating real errors. Corrected public Structs controls derive their ordinary Fba encoding-size obligation once without adding a caller premise: the same five controls fail old-engine baseline ab9c67973/Auto0957 (report7145add4) and the whole canonical module passes at c8bc49e91/Autof947 (report46fffc28,7.905 workload seconds). Candidate-only viewDemand assertions are compatibility checks, not baseline-failure evidence. The original underspecified-control failures remain bound to c03/d96. The one official409-target ROOT phase at79be4efb2 also passes all578 Lake jobs (report60e150a5,99.758 workload seconds); proof/native sources remain unchanged. Supported focused prepush remains pending at this note. This generic result is not a passed real FBA client, real-start strength, F2 or legacy retirement; unchanged-client execution waits for actual PR550 merge and current-main rebinding. PR550 (merged first): Follow-up from actual FullClient on main8bb62cdd/Auto0957: a positive arithmetic-cache proof outlives its auxiliary theorem and Lean rejects reuse (report67864631, PR521 comment6302152515). The exact creator call site and invalidating snapshot were not sampled. Existing RunCaches.saveArith now pairs with closeEntail's failed outer transaction and all12 tryRule outer restores; successful attempts stay unchanged. Private unchanged FullClient87f87 with candidateAuto8229 reaches the same failed-plan/retry path without the missing auxiliary (reportf524f3df, completeleaf0636d9ee). Its generic fold/split then supplies both fields; later known-address knowledge remains unresolved, so no client theorem or legacy retirement is claimed. Whole Updates and official409-target ROOT (128Proofs) pass at1b6bccf7/main8bb62cdd, reports6da5d281/ab8dc939. Updates.failed_rule_retry is ordinary full-bytes/frame behavior, not an old-fail auxiliary reproducer. Other nested/provider/walk/selected-state rollback owners remain outside this finite repair; no global cache-lifetime closure is claimed.

Progress: The original storeBlock/storeBlock_finite posts are restored; one requested-knowledge planner precedes region planning and uses known_of_bytesAt. Approved committed-descendant retry, snapshots/fallbacks, source-first determined-block address selection, unknown-block matching and direct-update shape checks remain. Whole actual Structs, including concrete/existential/idempotence/no-request/fail-closed controls, and the full29-file official sep-auto suite PASS on f9505e4e/main578aa3b2, Auto5614ed37, guards b8bf14f3/e6cbb205. The five actual unchanged Proofs callers PASS at their original afc52032a/Auto f13fb21a binding69afbe3b; the accepted causal audit supports retaining that evidence after the final change only restores main's carve. The isolated A/B and Claude6280049836 removed the ordinary size probe while preserving fixes1-2 and the explicit case-fact expected failure. No current-source fresh-five claim or blanket full-build repeat for a head move. Reproduce with tests/roadmap/sep-auto/check.sh; actual report6280488414.

Request: Close the generic store_fields_keep_address control in tests/roadmap/sep-auto/SepAuto/Structs.lean by deriving requested known b A from nonempty bytes before typed views hide their metadata. Do not eagerly add known to global store posts: the exact old result shape is required by Proofs/Threadsync/Mutex.lean, Proofs/Sync/Mutex.lean, Proofs/Sync/SnapshotCache.lean, Proofs/Threadsync/Handoff.lean and Proofs/Sync/Handoff.lean. Use only the existing knowledge-planning mechanism and known_of_bytesAt, with exact block/address and positive-byte guards; no per-proof glue or broader leftover-resource framing. Validate the completed global-rule repair with scripts/full-build.sh.

<a id="row-wp-local-hypothesis-application"></a>
### #wp-local-hypothesis-application Apply current local proof functions during bounded WP side proofs

Status: **closed**. Requester: Task07 condition-signal and semaphore migration; coordinator481/6279583751 and confirmed order6279729681.

Note: The bounded local-hypothesis path retains stable conclusion-head filtering plus full argument unification, current-context candidates once per level, shared depth/fuel, complete proof/data closure and failed-choice rollback. It performs no new case search and preserves ordinary case-enabled behavior. The generic incoming-fact normalization uses proof-producing existing simp/False.elim, not a division-specific contradiction rule. The assigned-update synthetic control checks its raw assigned-mvar shape and completed proof; it alone does not detect the old recovered PANIC. Captured fresh actual Full compiler output must establish absence of that PANIC. Global computational definition hints use addExtra's existing named-unfold path; proof terms and specific rules/updates retain their prior classification. Task14's distinct missing-field/auxiliary and Task23 conditional-post remainders are not claimed fixed. No new judgment, tactic, premise, cache schema, provider, caller wrapper or protected carve-size probe is introduced. Main515 demanded whole-region fix remains baseline. The exact seven-file restoration remains unapplied after automatic execution review rejected it despite human approval; preserved source/recovery and no-bypass requirements remain.

Progress: Qualified in PR529: at2f1b/main737, Auto/AutoWP fe270e1f/b9839887, whole canonical WP100 jobs, both actual condition modules161 jobs and exact407-target ROOT pass. Guardf07c262a/unit16d97d42 binds1005 unchanged source/command rows; physical ROOT8e2f1fa3/logdc09702f is reused for inventory. Official SepAuto31 builds206 jobs and replays203 modules/2111 theorems with standard axioms; OneLogic8 builds132 jobs and replays129 modules/108 theorems. SepAuto's general assurance output retains3 unchanged-class float-key/test-opaque policy findings; its documented fixture gate passes, not general policy. Currentnessfc737e7a renews only3 supported stale swap recipes, retains13 runs/49 qualified artifacts, and passes official inventory write/check. At a3a634ab8/main737, focused preflight and independent framework both pass (guardb3e8ad24, logs3b2b8c45/d4af7583), fixed inputs/artifacts unchanged. Final review/simple find no actionable issue. One structural walk retains raw/normalized evidence, forwarding priority, proof-local Eq substitution and exact-type own-equation exclusion; observable controls check actual substituted data. Assigned-update/global-definition controls compile; actual fresh FBA Full/no-PANIC evidence retains its35d8 binding. All original failures/source/artifacts remain archived; no new premise, cap, provider or manual walk is introduced.

Request: At an existing Proto.WP pure side goal, use a current local h : R -> forall u, A u -> B after current facts supply R and A u. Keep whole-hypothesis matching and caller-lemma priority; try each current local function once at the current chain level only after its final stable conclusion head matches, then unify every conclusion argument, prove every premise through the existing bounded backward side-proof path, close all data metavariables and restore failed choices. Share existing fuel/depth3; no new case search, forward saturation, provider search or unsupplied nested program walk. Scope-valid already-built proof reuse is permitted; case-free proof ancestry is not promised.

Deletion plan: Completed in PR529: all four actual translated signal walks (Sync.sig_body, Sync.ioCond_signal_wp, Threadsync.wake_body and Threadsync.cond_signal_wp) use one fsym each with exact initial ghost, hseen, complete holder resource and unchanged six public result/safety/completion statements. Current ROOT/all Proofs/Append, official fixture/axiom gates, genuine inventory renewal and focused metadata/framework pass with their original source bindings. The all-width Result run fact preserves zero-width, zero-divisor and signed-overflow errors through unchanged Basic semantics; no legacy VC rule or manual WP walk remains for this capability. Wait-family, general condition accounting and SemImpl/L8 obligations remain separately open.

<a id="row-l11-waitgroup-rwlock-impl"></a>
### #l11-waitgroup-rwlock-impl Word rules for gone threads, then WaitGroup and RwLockImpl on the full-state logic

Status: **open**. Requester: L11 RwLock/WaitGroup migration (maintainer decision 2026-11-03).

Note: Rejected alternatives: a new lock place `.done` that keeps `WInv.live` (existence and unjoined) for a thread past the lock: it cannot hold for a detached thread (joined while running), so such a thread could never use an FEvent or FCond. A per-protocol premise `Runs P t g` (existence from each protocol's invariant): every protocol with a gone or detached thread would restate what the scheduler already knows. No new judgment, tactic or premise.

Progress: Maintainer decision 2026-11-03: (1) the lock-word atomic rules get the stepping thread's existence without a non-gone lock place, and `FEvent`'s set path admits a lock-gone setter; (2) the L10/L11 implementation gate is released: `SemImpl` (L10) and `RwLockImpl` are built like `MutexImpl`/`CondImpl`. Step 1a (branch claude/l11-safe-exists): the concurrent logic itself hands the existence to every resumption, once and generically: `Proto.Safe`'s and `PausedOk`'s resumption and `WP.sync`/`WP.syncC`'s continuation get `t < m₁.threads.size`, which the scheduler discharges (`go_spec`, `go_some`: main is thread 0, kid i is thread i + 1, `SInv.size`). This supersedes the per-protocol premise `Full.Runs P t g` of PR #579's first version. Step 1b (PR #579): the derived stop rules the lock and word rules use pass that fact on (`WP.pickC_exists`, of which `WP.pickC` is the corollary without it; `WP.osFutexWait`, `WP.osFutexWake`); the word rules (`wp_word*`) and `FLock.Fits.pick` lose their lock-place premise, `FLock.Fits.atStop` takes the existence, and `FEvent`'s set path (`wp_peek`, `wp_xchg`, `wp_xchgAs`, `wp_wake`, `wp_osWake`, `EventImpl.set_wp`) admits a setter at `out` or `gone` of the lock (`Inv.swex` keeps a setter at `sw` existing for `Fits.liveSet`). `WP.futexWaitC`/`WP.futexWakeC` keep their statements: no rule over them needs the fact yet. WaitGroup (#640): on fsym over `MutexImpl` and `EventImpl` with its statements unchanged; the whole `Tally` read is `FLock.Inv.loadMem` (over `Inv.loadAll`) by the only non-gone thread; `Proofs/Threadsync/WaitGroup.lean` left `legacy_users`. LEFT: `RwLockImpl` and the three RwLock files.

Request: WaitGroup's last `finish` sets the ResetEvent after its `fetchSub` left the lock's protocol (lock place `gone`). The word rules required `L.ph g != .gone` only to get `t < m.threads.size` at the scheduler's resumption; the scheduler cannot supply liveness (`Thread.detach` sets `joined` on a running thread), only existence, which `Safe` now states at every resumption. Then: a general FLock plain-read rule spanning the rest, the lock word and the free lock resource, by the only non-gone thread (WaitGroup's waiter reads the result after the event); WaitGroup on fsym with ThreadMutex and ResetEvent `EventImpl`; `RwLockImpl` over L10's `SemImpl`; the three RwLock files on it.

Deletion plan: Closes when Proofs/Sync/RwLock.lean, Proofs/Sync/RwLockContract.lean, Proofs/Sync/RwLockSnapshotPair.lean and Proofs/Threadsync/WaitGroup.lean leave `legacy_users` with their statements unchanged.

<a id="row-literal-pointer-rebase"></a>
### #literal-pointer-rebase Store or load through a literal pointer into a region of the state

Status: **closed**. Requester: L6 FBA client over FAllocSpec (PR #567, blocker 3: `buffer[15] = u[11]`).

Note: One mechanism for every command and rule: a closed pointer of the command that no atom names is restated as `p.add k` from the one state region of its block whose extent holds it (block by `blockOf`, bounds by the arithmetic solver, `k` in the arithmetic's normal form). The rules and providers about derived pointers then apply unchanged (`regionStoreAdd`, `ReadsAt.regionIn`). Disjoint regions mean at most one region holds it. Rejected alternative: literal-pointer variants of the region rules, one per rule.

Progress: Branch claude/fsym-literal-pointer: `rebaseLitPtr?` (Auto.lean) in the walk's no-rule fallback, before views and unfolding, with `ptr_eq_add_off_sub` (AutoRules.lean). Tests: SepAuto.Region `literal_store_load` (a region at a literal base) and `literal_store_offset` (a region at `p.add (bs.extract 0 12).size`, its block and offset from facts).

Request: Generated code evaluates the address of a global's item to a literal pointer (`⟨some 0, 15⟩`). The state holds the global's bytes as a region at a pointer derived from the global's (`regionIn (bufp.add 12) …`). The planner matches pointers syntactically, so no rule's precondition found the literal: "the state has no atom for up (region ⟨some 0, 15⟩ …)".

<a id="row-read-through-bytes"></a>
### #read-through-bytes Read region bytes through stores to other bytes, memset items and a kept prefix

Status: **closed**. Requester: L6 FBA client over FAllocSpec (PR #567, blocker 2: reads of t[0] and t[3] after `t[7] = v +% 1` on reallocated bytes).

Note: Engine fix found on the way: every conditional `@[fsym_arith]` rewrite whose side condition contains a `dsimproc`-reduced term (`Enc.size (BitVec 16)`) failed with simp's "failed to assign proof": the discharger's proof had the reduced statement, which reducible unification does not match. Rejected alternatives: one load rule per byte source (store, memset, reallocation), which the provider already decomposes; reading a kept prefix by a user-supplied update, which every client would repeat.

Progress: Branch claude/fsym-read-through. Region.lean `@[fsym_arith]`: `extract_writeBytes_other`, `extract_memsetBytes_item`, `extract_replicate_le`, `decode_byte`, `LawfulEnc.decode_encode`, `Array.replicate_one`, `Array.size_replicate`, and the simproc `keptExtract` (with `extract_of_keepsPrefix`). Auto.lean: `arithCore` closes an equation with an unknown side by reducible unification of the normalized sides; `omegaDisch` states a discharged side condition as itself. Tests: SepAuto.Region `read_unwritten`, `read_unwritten_word`, `read_kept`.

Request: The provider `ReadsAt.regionIn` asks `Enc.decode (bs.extract lo hi) = pure ?v` of a region whose bytes are `writeBytes (memsetBytes n (some v)) o (Enc.encode w)`, or bytes `bs` with a fact `keepsPrefix old bs` (a reallocation's). The arithmetic normalization did not read through a disjoint write, an item of a memset or a kept prefix, and did not assign `?v`.

<a id="row-literal-pointer-provider"></a>
### #literal-pointer-provider A literal pointer in a state region, found by the planner instead of a walk rewrite

Status: **open**. Requester: coordinator (2026-11-04, /simple on #604: the walk rewrite is shallow).

Note: Recorded with the L6 D-b PR, which lands the coordinator's decision on #604.

Progress: open

Request: Row `literal-pointer-rebase` (#604) restates a command's literal pointer (`⟨some 0, 15⟩`) as `p.add k` from the state region that holds it, by rewriting the command in walk's no-rule fallback (`rebaseLitPtr?`, Auto.lean). The end state is a pointer-in-region provider in the planner: when a rule's precondition wants a region or a `pts` at a literal pointer, the planner finds the region whose block and extent hold it and supplies `q = p.add k` (`ptr_eq_add_off_sub`), so that every rule and provider about derived pointers applies without rewriting the program.

Workaround sites: `ZigLean/Sep/Full/Auto.lean`

Deletion plan: Transitional: delete `rebaseLitPtr?` and its call in walk's no-rule fallback once the planner's pointer-in-region provider lands; the tests SepAuto.Region `literal_store_load` and `literal_store_offset` stay green through the switch.

<a id="row-client-glue-copies"></a>
### #client-glue-copies Sync clients copy the memory glue of their protocol's rest (cells of the words in the rest, the block, start and fork facts)

Status: **open**. Requester: L10p (/review of PR648, 2026-11-05).

Note: Not a soundness issue: every copy is kernel-checked. Recorded instead of done in PR648 because the change rewrites the merged Handoff and MutexCounter proofs.

Progress: open

Request: Each client of the full-state sync contracts proves its own copy of the same lemma family, which differs only in the layout (the block, the words in the rest, the `io` prefix). Copies: `Proofs/SemCounter/Mem.lean` (`res_eq`, `Rest.split`/`step`/`congr`, `blk_ofG`, `blk_of`, `heap_blk`, `cell_eq`, `cells_same`, `frame_rest`, `apart_of`, `BlkOk.of_block`, `box_notL`, `io_notL`, `BlkOk.lstep`, `Shape.congr`) and `Proofs/SemCounter/Start.lean` (`word_init`, `heap_ne_l`/`heap_ne_r`/`erase_ne_r`, `clk_fork`, `cinv_out`, `split_at`, `box_split`, `sep_box`, `upd0_1`/`upd1_0`) against `Proofs/Handoff/Protocol.lean` (same names), `Proofs/Handoff/Start.lean`, `Proofs/Handoff/Steps.lean` and `Proofs/Handoff/Ops.lean`; `blk_of` also in `Proofs/MutexCounter/Protocol.lean`. `Proofs/SemCounter/Start.lean`'s `hb_fork` and `sinv_grow` are generic over `FLock`/`FSem` (`sinv_grow` repeats `FSem.Inv.mono` with a growing thread array). WaitGroup (#640) copies the rest family (`Rest.split`/`step`/`congr`, `res_eq`, `heap_blk`, `BlkOk.of_block`, `word_init`, `newest`/`newest_push` next to `FEvent.newest`) in `Proofs/Threadsync/WaitGroup/Protocol.lean`, the start glue (`heap_ne_*`, `split_at`, `spawners`, `inv_cur`, `projI`, `wp_free`) in `Proofs/Threadsync/WaitGroup/Start.lean`, `clk_fork` and `einv_out` (Handoff's `einv_out`, generic over `FEvent`) in `Proofs/Threadsync/WaitGroup/Main.lean` and `ewait_ok` (Handoff's, generic over `FEvent.Inv` with one waiter) in `Proofs/Threadsync/WaitGroup/Wait.lean`. A next client would copy them again.

Workaround sites: `Proofs/SemCounter/Mem.lean`, `Proofs/SemCounter/Start.lean`, `Proofs/Handoff/Protocol.lean`, `Proofs/Handoff/Start.lean`, `Proofs/Handoff/Steps.lean`, `Proofs/Handoff/Ops.lean`, `Proofs/MutexCounter/Protocol.lean`, `Proofs/Sync/Mailbox/Protocol.lean`, `Proofs/Sync/Mailbox/Steps.lean`, `Proofs/Sync/Mailbox/Start.lean`, `Proofs/Threadsync/WaitGroup/Protocol.lean`, `Proofs/Threadsync/WaitGroup/Start.lean`, `Proofs/Threadsync/WaitGroup/Main.lean`, `Proofs/Threadsync/WaitGroup/Wait.lean`

Deletion plan: Move the layout-free lemmas (`res_eq`, `heap_blk`, `frame_rest`, `apart_of`, `BlkOk.of_block`, `word_init`, `heap_ne_*`, `erase_ne_r`, `clk_fork`, `cinv_out`, `einv_out`, `ewait_ok` (next to `FEvent.Inv.toOut`), `hb_fork`, and `sinv_grow` as a generalisation of `FSem.Inv.mono`) to `ZigLean/Sep/Full`, replace Handoff's `le_nil` by `VClock.le_default` (as SemCounter does) and `upd0_1`/`upd1_0` by `upd_ne`, and state the rest family once over a block, a byte range of words and an `io` prefix (a generic `Rest`/`BlkOk` module) with Handoff, MutexCounter and SemCounter as instances; delete every copy and close this row.

<a id="row-fsym-split-nested-struct-subst"></a>
### #fsym-split-nested-struct-subst fsym's split of a user-structure fact leaves a stale local when a field is a structure whose split substitutes a local

Status: **closed**. Requester: L10p (SemCounter over SemImpl, PR648, 2026-11-05).

Note: Not a soundness issue: the engine failed closed (the walk did not elaborate). The cause was not the nesting: any structure fact whose field's split substitutes a local the fact mentions broke at the next field (`destruct` projected the reverted fact); at the top level `wpSplit` projects all fields first, which hid it.

Progress: closed by the branch claude/fsym-fvar: `destruct`'s structure branch takes each field from the fact as the previous field's substitution reintroduced it (`liveFVar?`). `Zig.SemCounter.U` is a structure again. Regression: SepAuto.Facts `nested_struct_subst`.

Request: When `fsym` splits a hypothesis of a user structure into its fields and one field is again a user structure whose own split substitutes a local (an equation `x = e` with `x` a local), the next continuation fails with `unknown free variable`. Repro (on PR648 before the workaround): `structure T3 (G rX m) : Prop where um : UM G rX m; ci : C.Inv L G m` with `Zig.SemCounter.UM` (its field `rest : Rest rX m` holds `rX = rsum (cellsAt BoxW m) rIO`), as the hypothesis of a continuation of a rule built from `FLock.Fits.wp_tick_plain`, fails even with post `True`. `UM` alone, `Lg` alone, a nested structure without the `rX` equation, `Rest` as a direct field, and the plain conjunction all pass. Same class as row `fsym-unknown-fvar-mutex-loop` (a substitution inside the engine while a pending goal still mentions the local); the fix is in the structure branch of the engine's split (`ZigLean/Sep/Full/Auto.lean`).

<a id="row-fsym-unknown-fvar-mutex-loop"></a>
### #fsym-unknown-fvar-mutex-loop fsym leaves an unknown free variable on the macOS ThreadMutex lock loop body

Status: **closed**. Requester: L8f/L8g (#562, coordinator decision 2026-11-04: ledger row with repro, hand walk kept with a deletion plan).

Note: Recorded with #562 (L8 ticks). The loop's test `if id r.1` reduces by `id_eq` in the WP simp set. `lockInvD`'s order of parts: row `fsym-or-witness-order`.

Progress: closed by the branch claude/fsym-fvar: each branch of a split is walked with the substitutions of its own branch (`eachBranch`); the second branch's substitution of `g₀` had replaced the first's. The row's original call elaborates (checked); `loopD_body` is the shorter call without the `hset`/`hph`/`hok₀` glue, swap-built against the darwin translation. Regression: SepAuto.WP `sibling_values`.

Request: `Proofs/Threadsync/ThreadMutex.lean` `loopD_body` (the macOS `osUnfairLockTry` repeat) walked by `fsym [wp_casD hP hc1 (g := g₀), wp_waitD hP, hset, L.ph_set, L.set_set, hP.ok_set, lockInvD, lockPostD]` fails with `unknown free variable _fvar.…` at the `fsym` call; `hset : ∀ q h, L.set g₀ q h = L.set g q h` is a local hypothesis about `g₀`, which the walk's case split of `hg₀ : g₀ = g ∨ g₀ = L.set g .spin rnil` (or a `subst` inside the engine) removes from the context while a rule instance still mentions it. Only the darwin translation elaborates this branch (Linux uses the futex path). Repro on #562 (before the hand walk): restore the `fsym` call above in `loopD_body`, then `python3 -B scripts/theorem-inventory.py swap-build --lake "$(elan which lake)" --swap threadsync=tests/golden/0.15.2/threadsync/Gen-darwin.lean -- Proofs.Threadsync.ThreadMutex`. Reproduced with and without #562's `eqFixesUnknowns` change. Needed: every term fsym installs is re-abstracted over (or checked against) the local context it runs in after a case split or substitution, and a local hypothesis whose fvars leave the context is re-instantiated or dropped from the rule set, never kept dangling. Regression: a sep-auto test with a local equation hypothesis over a variable that a disjunction case split substitutes.

<a id="row-fsym-or-witness-order"></a>
### #fsym-or-witness-order fsym's post solver chooses an existential's witness by a disjunction before the conjunct that determines it

Status: **open**. Requester: claude/fsym-fvar (found closing row fsym-unknown-fvar-mutex-loop, 2026-11-05).

Note: Not a soundness issue (the walk fails closed). The workaround states an equivalent invariant (the conjuncts swapped), not a weakened one.

Progress: open

Request: A post `∃ x, (x = a ∨ x = b) ∧ Inv x` with a hypothesis `Inv b`: `wpGoal`'s `And` case proves the first part first, its `Or` case proves the side `?x = a` whole (`wpAtom`, `eqFixesUnknowns`: the unknown is a side) and commits `?x := a`, and `Inv a` is then left open. The `And` case retries a first part left open, but not a first part closed with a choice the second part refutes. Repro: `Proofs/Threadsync/ThreadMutex.lean`'s `lockInvD` with its original order `∃ g₀, (g₀ = g ∨ g₀ = L.set g .spin rnil) ∧ P.inv (upd G t g₀) m`, swap-built against `tests/golden/0.15.2/threadsync/Gen-darwin.lean`: the wait branch leaves `P.inv (upd G₁ c g) m'` with `P.inv (upd G₁ c (L.set g .spin rnil)) m'` in context. Needed (a separate engine PR): a conjunction whose second part fails after its first part committed an unknown is retried in the other order (the general form of the existing retry, not one more ordering special case); regression in SepAuto.WP next to `and_retry`.

Workaround sites: `Proofs/Threadsync/ThreadMutex.lean`

Deletion plan: Transitional: once the solver orders such a conjunction itself, state `lockInvD` (darwin) in its natural order `∃ g₀, (g₀ = g ∨ g₀ = L.set g .spin rnil) ∧ P.inv (upd G t g₀) m` again, swap-build `Proofs.Threadsync.ThreadMutex` against the darwin translation, and close this row.

<a id="row-callocspec-partial-step-count"></a>
### #callocspec-partial-step-count The allocator contract CAllocSpec is partial, so a client's exact step count holds only for runs that return

Status: **open**. Requester: L8g/L8h (#562, coordinator decision 2026-11-04: accepted as a recorded obstruction).

Note: Recorded with #562 (L8 ticks): freeAll_steps takes the returning run as a premise.

Progress: open

Request: `CAllocSpec` (ZigLean/Sep/Full/Dispatch.lean) states each allocator call as a `CTriple`, a partial judgment: an implementation whose `free` never returns meets it. So `Lists.Alloc.freeAll_exact` (`CTriple`, `xs.length + 1` credits in, as many receipts out) gives `Lists.Alloc.freeAll_steps` only for a run that returns (the run's result `pure (v, m')` is a premise). The legacy `Proofs/Lists/Cost.lean` `freeAll_cost` counted unconditionally because it used the hand-written total `Allocator` model, which the trusted-base rule retires. Counterexample to the unconditional count under the present contract: an allocator whose `free` loops forever meets `CAllocSpec` (its triples hold vacuously) and makes `freeAll` diverge on a one-node list, so no run returns and there is no final memory whose `ticks` could be `m.ticks + 2`. Needed: a total allocator contract (each call, at least `free`, terminates), proved by every translated allocator; with it `freeAll_steps` drops the returning-run premise and also gives the run's existence, as `FTotalTriple.ticks_eq_post` does for sequential code.

<a id="row-rwlock-reader-admission-room"></a>
### #rwlock-reader-admission-room Derive reader and pending-writer admission room from actual RwLock handles

Status: **open**. Requester: Original Task08 RwLockImpl migration (2026-11-04).

Note: The room question is decided (hroom premises, permanent; no tokens). The value family does not enforce admission or reserve bit 63 for out-of-range encodings; the kernel controls in tests/roadmap/sync-contracts/RwLockState.lean show both carry boundaries. Full RwLockImpl, translated methods, complete-resource/progress proofs and unchanged clients remain open (B1, B2, F4).

Progress: Resolved by the maintainer decision of 2026-11-06 (#714): the room is a permanent `hroom` premise of `RwLockImpl.lockShared_wp` (preReaders + 1 < 2^31) and `RwLockImpl.lock_wp` (preWriters + 1 < 2^31), the same mechanism as the condition's 65535-waiter limit in `CondImpl.wait_wp` / `SemImpl.wait_wp`. A client with a fixed set of threads discharges it from its thread count. Init-minted admission tokens are not built. What remains of this row is the legacy retirement in the deletion plan. 2026-11-06 scope (#714): `RwState.Family` covers the operations of all eight 0.17 `Io.RwLock` entry points (`set_writing` for tryLock's `state | is_writing`, `sub_writer` for the cancel path's `Sub writer`, `clear_writer` for `And ~is_writing`, `readers_ne_zero` for both `reader_mask` guards), but `RwLockImpl` states only the four uncancelable ones. Open obligations before tryLock, tryLockShared and the cancelable lock/lockShared enter the contract: tryLock sets writing without a counted intent (no `wi` phase, so the invariant's writing count cannot rely on the holder's own -1), and a canceled `lock` clears writing while readers may be draining, so the semaphore invariant must admit the stale permit that the `waitUncancelable` after `prev_state & reader_mask == 0` consumes. Until then those entry points have no contract rule and a client calling them is rejected (no rule, the walk fails closed).

Request: In the ABI64 std layout, readerUnit=2^32, readerMask=2^63-2^32 and both counts have 31 bits. At preReaders=2^31-1 with no writer, the low-word guard holds and checked 64-bit addition succeeds, but adding readerUnit sets reserved bit 63 and the reader mask decodes 0. A successful expected-value fast CAS and the slow-path reader RMW need actual preReaders+1<2^31. Writer intent adds 2 BEFORE taking the outer mutex: encode(0,2^31-1,false)+2=encode(1,0,false), so one extra pending writer carries into reader units. The mutex does not itself bound pending intents. That RMW needs preWriters+1<2^31. Neither bound follows from a modular value equation or 64-bit arithmetic safety; both require correspondence with actual admitted handles/resources at their respective native transition. Original finite-client public statements must remain unchanged.

Deletion plan: RwState.Family and its ABI64 instance supersede legacy Sync.RwLockRead.sv3, sv3_* and RM; delete that duplicate algebra with the RwLock/RwLockContract/RwLockSnapshotPair migration when their real contract consumers use this family, then close this row. Keep the native-operand and count-boundary kernel controls.

<a id="row-mutex-held-foreign-wait"></a>
### #mutex-held-foreign-wait Keep mutex ownership across a wait at an independent sync object

Status: **open**. Requester: Original Task08 RwLockImpl migration (2026-11-04, PR #637).

Note: This is a source-level incompatibility of the present invariant with the required native control flow, not a kernel-checked reachable execution or public soundness counterexample. Serialization S and protected payload R remain distinct; the complete outer held resource must stay framed during the inner wait. The shared Lock/Word/Cond/engine writer remains with the coordinator.

Progress: Source-level interface obstruction isolated while composing the existing MutexImpl and SemImpl. No shared invariant, implementation contract, premise, tactic or generated-body walk has been changed. The RwLock implementation gate is already released; this is a distinct existing-library boundary. 2026-11-06 (claude/rwlock-impl): the Queue part is resolved on main by #668: `LockWord.Queue` admits a holder at `holdsAway` at a key of the lock's `nest` (`WInv.nap`/`unnap`, `WInv.waitNest`), and its progress obligation is `FLock.Fits.holdLive` (LockOrder.lean names the RwLock writer's semaphore wait as a nest futex discharged by the semaphore's liveness). What is left is the product invariant of the outer mutex and the semaphore's mutex over one ghost value (row two-lock-product, its parked item (5)); the RwLockImpl draft takes the outer mutex's nest to be the semaphore's mutex word and condition epoch and discharges holdLive from the protocol's writer liveness.

Request: Full/LockWord.lean Queue requires every thread waiting at another futex to have lock phase away. WInv includes that Queue, while its word field equates a zero lock word with Free (no holds phase). The real Io.RwLock writer retains the outer mutex while SemImpl.wait blocks at its embedded mutex or condition epoch (0.17 Gen lockUncancelable: outer lock then semaphore wait). A queued (writer, foreignPtr) with foreignPtr != outer.ptr and outer phase holds contradicts Queue. Relabeling that sole owner away makes Free true while the outer word remains locked, so it cannot preserve WInv or the retained serialization resource. WInv.waitOff and FLock.Inv.waitOff admit away, not a retained holder. With an additional outer contender, WInv.wit also requires a busy thread absent from every futex queue; the real progress source can instead be the last reader outside this mutex's code. Needed: a permanent generic representation/rule for holding one mutex while waiting on another object, preserving actual owner/held resources and deriving progress through the existing protocol's Live. Decide the shared Queue/WInv/MutexImpl boundary before changing statements; a generic apart-Step preservation lemma without those conditions is false.

Deletion plan: Close after the generic existing mutex contract and its translated instance support the actual nested wait, and RwLock consumes that support with unchanged public clients. Do not add a local semaphore contract, omit the blocking branch, assume a waiter never sleeps, or hand-walk the outer mutex as a replacement for MutexImpl.

<a id="row-fsym-forward-bool-fact"></a>
### #fsym-forward-bool-fact fsym does not forward a hint term's Bool-equation fact, so a rule's autoParam guard cannot use it

Status: **open**. Requester: S6 (#649, futex address validation).

Note: Recorded with #649 (S6 address validation).

Progress: open (workaround)

Request: The OS futex rules `WP.futex_4arg_of_aligned`, `WP.futex_3arg_of_aligned`, `WP.ulock_wait2` and `WP.ulock_wake` (ZigLean/Sep/Full/OsFutex.lean) select on the autoParam guard `hword : m.wordAt p = true := by first | assumption | decide`, which `runAutoParam` closes in the goal's local context. A protocol supplies the fact as a hint term, `fsym [hP.wordAt hi, …]` (`FLock.Fits.wordAt`, `Fits.wordWordAt`), but fsym forwards a hint term's conclusion as a hypothesis only when it is an `∃` (`wpForwardEx`) or arithmetic (`wpForward`), and `wpChain` proves side goals backwards only for a conclusion that is not an equation. So the guard sees no `m.wordAt p = true` and the rule does not apply. Needed: a hint term whose conclusion is a fact about the current memory (a Bool equation such as `m.wordAt p = true`) is forwarded like an `∃` fact, at the stop where its premises hold, so that an autoParam guard's `assumption` finds it. Regression: SepAuto.WPOsFutex with the `have hw` lines removed and `hP.wordAt hi` in the list.

Workaround sites: `tests/roadmap/sep-auto/SepAuto/WPOsFutex.lean`

Deletion plan: Transitional: once fsym forwards such a fact, delete the `have hw := …` before each `fsym` in SepAuto.WPOsFutex, pass the term in the `fsym` list instead, and close this row.

<a id="row-word-ok-live-set"></a>
### #word-ok-live-set Word.Ok asks every plain access to happen before every thread, so a whole-struct read next to a futex word breaks it

Status: **closed**. Requester: L11e/L11f (WaitGroup over FEvent, #640 comment 6643815474; coordinator decision: option (A)).

Note: FEvent's live set is `FEvent.Live`: a thread that may wait or set, unless a setter that has set (`sw`, `sd`). A setter at `sw` still wakes, but a futex wake records no access, so it needs no clock below a plain access (counterexample to keeping it until it leaves the event's code: main's cas writes waiting, the setter's xchg reads waiting and goes to sw, main's futex compare reads is_set and returns, main reads the whole struct while the setter is still at sw).

Progress: closed by PR646, which gives Word.Ok a live set

Request: `Word.Ok.wfp` required each plain access to a word's bytes (a footprint entry) to be at or below the clock of every thread (`AllLe`). Counterexample: in the WaitGroup proof (Zig 0.15.2's code, Proofs/Threadsync/WaitGroup), main loads the whole 24-byte `Tally` after its wait, one plain read covering the counter word (bytes 0..8) and the event word (bytes 8..12). The read's entry carries main's clock, whose main component is above every task's clock (main's add, wait and read come after the tasks' last synchronization), and the tasks stay in `m.threads`, also after their joins (a memory has no ended flag). So from the read on, `WG.Ok` and `EV.Ok` are false in every later memory, while `FPrim.ofWords.Sub` and `Word.InRest` ask `W.Ok` in every state of the protocol's rest: no rest holds after the read, and main's theorem is unprovable although the program is race-free (only threads that may still access the word must be above the plain access). The lock word does not have this: `LockWord.WInv.wfp` already uses a live set (`LiveLe`). Needed: `Word.Ok m A` with a protocol-supplied live set `A` (`AllLeOn A`); every word rule whose op by thread t accesses the word takes `A t` (a futex wake is no access); the default `fun _ => True` keeps the statements of the word lemmas, and the contracts (MutexImpl, CondImpl, SemImpl, EventImpl) and their clients keep theirs (FEvent's rules take the live-set premise and discharge it).

<a id="row-fevent-live-exit"></a>
### #fevent-live-exit A thread with FEvent's waiter role stays in the event word's live set after its last access

Status: **open**. Requester: L11f review of PR646 (pass 2, cross-file angle).

Note: Not a soundness gap: a thread outside the live set cannot access the word (every access rule takes the live-set premise); the gap is what can be proved.

Progress: open

Request: `FEvent.Live g := (wx g ∨ sx g) ∧ ¬ (ph g).Setting` takes the live set from the roles, and the invariant keeps the waiter role (`Inv.wx`, `Inv.wby`; `Inv.toOut` asks `E.wx (G t) → E.wx g`), so a waiter that returned to `out` stays live for good. Scenario: a worker waits and main sets; the worker returns and ends; main joins it and then reads the struct that holds the event with a plain read (or reinitializes it). The read's clock is main's after the join, not below the worker's, so `E.W.Ok m (Live ∘ G)` is false from then on although the program is race-free. WaitGroup (#640) is not affected: its only waiter is main, the reader. Needed: a way out of the live set for a thread that will not access the word again (a protocol-chosen exit, kept by `Inv.wby` through another witness of each `waiting` write), proved generically in `FEvent`.

<a id="row-run-witness-loop-names"></a>
### #run-witness-loop-names Kernel run witnesses name the functions on the run's path to its loops, and the path differs between Zig versions and targets

Status: **closed**. Requester: L17 (retiring unroll_sched).

Note: The `zig_run` witnesses were built against every translation `lake build Proofs` runs them on: 0.16.0 linux, and the theorem-inventory swap builds (0.17.0 sync, 0.15.2 darwin and aarch64 threadsync, 0.15.2 atomics and threads), PR #697.

Progress: closed by PR #697 on the `zig_run` simp set of #690 (docs/proof-automation.md, kernel-run witnesses): every former workaround site unfolds the run's path with `zig_run` and names only hand-written definitions; `Sync.Handoff.handoff_completes` no longer uses `unroll_sched`.

Request: Kernel run witnesses name the functions on the run's path to its loops, and that path differs between the translations `lake build Proofs` runs against (docs/proof-tools.md, concrete runs of programs with loops). The names are AIR loop ids (`f.loop<id>`) and anonymous-instance hashes, which a new compiler or std patch can change. `Sync.Handoff.handoff_completes` (Proofs/Sync/Handoff.lean) has no list at all: it reaches `Io.Condition`'s wait loops, which 0.16.0 holds in `Io_Condition_waitInner` and its body `loop23` (absent in 0.17.0) and 0.17.0 in `Io_Condition_waitUncancelable` and its body `loop22` (absent in 0.16.0), and `lake build Proofs` runs against the 0.17.0 sync translation (`0.17.0-linux-goldens`). It keeps `unroll_sched`, which finds the loops itself. Needed: a version-neutral way to reach a run's loops. Candidate: the opt-in `--proof-api` (docs/generated-code.md, stable proof interface) already emits `<B>_unfold` and `<B>_loop<k>_step` lemmas under names from the source identity and the loop's pre-order position, never AIR ids; tagging them with one simp set declared in ZigLean (with the model functions that hold a loop, `Zig.osUnfairLockC`) would make every witness `simp only [<set>, Zig.loop.eq_1]` with no names. Rejected: `when_defined` (legacy-to-retire) and `first | delta <0.16.0 names> | delta <0.17.0 names>` (version glue that the next release breaks again). Possible but weaker: moving the theorem out of `Proofs` into a 0.16.0-pinned fixture, as `mailbox_completes` moved to tests/roadmap/sync-contracts/Runtime.lean; it keeps the theorem but drops its 0.17.0 run.

Deletion plan: Done (PR #697): Sync/Handoff dropped `unroll_sched` (the tactic goes with its last use, docs/legacy-retirement.md section 5) and the others dropped their hand-written `delta` lists.

<a id="row-waitgroup-impl-contract"></a>
### #waitgroup-impl-contract No generic wait-group contract (`WaitGroupImpl`) on the full-state logic

Status: **open**. Requester: L21 (retirement of ZigLean/Conc/Spec, PR677).

Progress: open

Request: The retired `WaitGroupSpec` was stated for every client (its instance was a hand transcription of `Io.Threaded`'s private `WaitGroup`). On the full-state logic, the same algorithm (0.15.2's generated `Thread.WaitGroup`) is proved only inside one program (`Proofs/Threadsync/WaitGroup.lean`, `waitGroup_spec`/`waitGroup_safe`), as a client of `MutexImpl` and `EventImpl`. Needed: a `WaitGroupImpl` contract (start/finish/wait for every protocol that has the group: the waiter sees every finisher's writes, every token taken, no deadlock) with 0.15.2's `Thread.WaitGroup` proved against it once for every program, the threadsync program a client. 0.16.0 and 0.17.0 have no public `WaitGroup`; `Io.Threaded`'s pool counter joins this when `Io.Threaded` is translated (`IoSpec`).

Deletion plan: Closes when `WaitGroupImpl` is on main with 0.15.2's `Thread.WaitGroup` proved against it and `Proofs/Threadsync/WaitGroup.lean` uses only the contract (docs/thread-specs.md, "What has no replacement yet").

<a id="row-mutex-impl-relaxed-witness"></a>
### #mutex-impl-relaxed-witness No kernel-checked witness that `MutexImpl` rejects a relaxed `unlock`

Status: **open**. Requester: L21 (retirement of ZigLean/Conc/Spec, PR677).

Progress: open

Request: The retired `Conc/Spec/MutexToy.relaxed_not_spec` showed that `MutexSpec` rejects a spin mutex whose `unlock` writes with `monotonic` (the next holder misses the previous holder's write). No statement shows the same of `MutexImpl`. Needed: a test (`tests/roadmap/sep-full/*CX.lean` style) that refutes `unlock_wp` for a `monotonic` unlock: a concrete memory satisfying `FLock.Inv` with a holder that wrote the lock's resource, a protocol with `FLock.Fits` (e.g. via `Fits.ofLock`), and the step after which `LockWord.Owns` fails for a live thread.

Deletion plan: Closes when the witness is in tests and checked by its fixture's check script.

<a id="row-guard-lifeline-mirror"></a>
### #guard-lifeline-mirror build-guard mirrors a lifeline ticket in `merge/` for guards of checkouts before PR #661

Status: **open**. Requester: P1c (elastic build-guard admission, PR #661).

Progress: open: transitional compatibility with guards of older checkouts (not an fsym engine gap; recorded here as the deletion plan CLAUDE.md asks for).

Request: PR #661 moved an elastic workload's lifeline ticket from `<lock>.d/merge/` (where guards before #661 read every ticket as a drain ticket, so a lifeline there drained the shared host beside free memory) to `<lock>.d/lifeline-tickets/`. Guards before #661 do not see that directory, so one of them as a large or exclusive queue head could keep the queue from a lifeline until its --lock-wait. Until no such guard runs, a lifeline whose turn it is mirrors its ticket in `merge/` under a time-0 name (`Admission.mirror_lifeline`) while no `lifeline_aware` head publishes a reservation.

Workaround sites: `scripts/build-guard.py`, `tests/roadmap/build-budgets/test_guard.py`, `docs/build-budgets.md`

Deletion plan: Delete `Admission.mirror` and `mirror_lifeline` (and the `lifeline_aware` mark, which only it reads), the mirror part of `test_the_lifeline_goes_ahead_of_every_exclusive_ticket` and the mirror paragraph of docs/build-budgets.md#elastic-workloads in the first PR after 2026-11-19 whose check shows no older guard running: at one main-health run, on arc and on the Mac, for every running build-guard process (`ps -eo pid,args | grep build-guard.py`), its checkout (the script path when absolute, else the process's working directory: `readlink /proc/PID/cwd` on arc, `lsof -a -p PID -d cwd -Fn` on the Mac) contains #661's merge commit (`git -C <checkout> merge-base --is-ancestor <merge> HEAD`). Then close this row.

<a id="row-fstepin-addrs"></a>
### #fstepin-addrs FStepIn does not keep the blocks' addresses, so a futex key of another block is lost across a frame step

Status: **closed**. Requester: S6e (audit finding S6, futex keys, #668); maintainer decision 2026-11-05: option A.

Note: Rejected: option B, a field `a : Nat` (the word's address) in `LockWord` with a memory-independent key. It is a per-object special case that FCond, FSem and FEvent would each repeat, and every LockWord construction would supply the address. Option A strengthens what every client of `FStepIn` gets and weakens nothing.

Progress: closed by PR #681: `FStepIn.addrs : m.SameAddrs m'` (ZigLean/Conc/Clock.lean) replaces the field `blocks` (now the theorem `FStepIn.blocks`), with the library lemmas `Mem.SameAddrs.refl/trans/of_blocks/of_push/of_set/size/addrIn_eq` and `Mem.sameAddrs_write` (ZigLean/Mem/Lemmas.lean)

Request: With the futex queue keyed by `FutexKey` (#668), a lock word's invariant names keys: its own (`Mem.wordKey`), and in `LockWord.nest` the keys of other blocks' words (a nested lock's word). `FStepIn` kept only `m.blocks.size ≤ m'.blocks.size`. The word's own key still transports through its cells (the step keeps the word's bytes and block), but a key of another block does not. Counterexample: a frame step by the lock's owner that replaces block `b'` (another lock's word, not in the frame) by a block at another address satisfies every old `FStepIn` field, and `LockWord.nest k` read in `m` (`m.keyAt ⟨b', o⟩ false = some k`) is false in `m'`; so `WInv` is not stable under a frame step and the FLock rules cannot be proved. The model never does this (a block never moves; every `addr :=` is a new block: `Mem.afterAlloc`, a mapping, a moving `mremap`), so the step relation can say it. Needed: a field `addrs : m.SameAddrs m'` of `FStepIn`, discharged at every producer by general lemmas.

<a id="row-two-lock-product"></a>
### #two-lock-product The generic two-lock product over FLock (lock nesting) is not built yet

Status: **open**. Requester: L8q/L8r lock-order work (Step 2), #693; parked by the coordinator 2026-11-05.

Note: Not unsound: no client relies on a two-lock product yet; a nesting client today proves its own `U` (`Fits.nap`/`unnap` hypotheses).

Progress: PARTLY DONE. Landed: `Fits.stable` gets the step's `FLock.Transfer` (decision (a), #696); `Holds.regroup`, `FOwned.move` (ThreadOwned.lean) and `FLock.Pair`/`Pair.symm`/`part_ba`/`Pair.otherInv` (LockPair.lean, #693). PARKED (coordinator, 2026-11-05: finish open work, start nothing new): (1) the product invariant: one lock's rest is the other's word, the other's resource (free or held) and a common rest, with the `Off` facts and their mirror; at A's acquire B's `FOwned` is rebuilt from `Transfer`'s `A.FreeRes G rX m h` by moving each B-held resource into its holder's part (`FOwned.move`), because `Res.know`/`gh` do not cancel, so an existential free resource in `U` cannot be matched to `A.Inv`'s witness; per-witness forms of `Inv.restIn`/`lockResIn` (Word.lean) help; (2) the FLock version of `Sem.Inv.partTick`; (3) `waitNest` at FLock level; (4) a two-mutex client fixture over `MutexImpl`, generic over every `MutexImpl`; (5) the product API on #637 (RwLockImpl). 2026-11-06 (B1, #715): item (1) built in LockProd.lean without a stored witness: a lock's `U` keeps only the other lock's `FLock.Facts` and `FLock.Keeps` (its free resource, its holders' resources as `sepN` with `Mem.Owns`, the `Off` facts), never its `FOwned`; `Pair.swap`/`Pair.inv_iff` rebuild either lock's invariant from the other's (`FOwned.out`/`into`), so one protocol invariant serves both `Fits.inv`. `Keeps.otherStep`/`Keeps.cur`, `Pair.U_stable`/`U_atStop` give the other lock's `stable`/`atStop`. 2026-11-07 (B1, #715, after F4 #713): item (1) done: `Keeps.setA`/`U_setA` (nap/unnap relabel), `Keeps.partStep`/`U_partStep` (a step on a part; `Inv.wp_liftMem`'s continuation now gets the rest's `FStepIn` with its read shares, `FStepIn.dropMid`, since `.heap.erase` loses the other lock's share bytes), read shares (`Keeps.owns`/`Facts.free` are `OwnsRes`; moving the held resources into the parts needs `FLock.NoGatherHeld`, `NoGatherHeld.of_R`). Item (2) done: `Pair.U_partTick` (the other lock kept under `PartTick`, for `Fits.kstep`). Item (3) done: `FLock.Inv.waitNest` (a holder's private wait at a shared word of its nest; a nest futex that is another lock's word is that lock's code, `Pair.otherInv`). Left: (4) the two-mutex client fixture over every `MutexImpl` (it builds both locks' `Fits` from `Pair.U`), (5) the RwLock product (B2).

Request: A thread that holds one lock while it runs another lock's code (a lock order, RwLockImpl's writer, hand-over-hand) needs both locks' invariants at once over one ghost value, with each lock's held resource placed in the other lock's rest, proved once for every pair of `FLock`s and every `MutexImpl`.

Deletion plan: Closes when the product invariant, the partTick and waitNest rules at FLock level and the generic two-mutex fixture land; no workaround is in the tree.

<a id="row-second-pass-speculative-cost"></a>
### #second-pass-speculative-cost the arithmetic's second pass runs on the failed side goals of rules that do not apply

Status: **open**. Requester: coordinator (main red on alloc-translated since #699, PR #703).

Note: Cost only: the second pass adds facts, never a premise; a goal it fails on fails as before.

Progress: Since #699, `arithCore` normalizes the relevant facts again after every failed `omega` that is not a probe (`renormFacts`, then `atomCongr` and a second `omega`). The side goals of rules tried in turn (`mremapShrinkR` and its siblings, `ptrEqAddr_live`'s cases) fail by design, and each failure pays the pass. #702 caches the discharger's failures by fact set (ArenaSpec `free_ct`: 12M heartbeats a call to 0.35M); #703 makes a normalized fact state its simp result (`mpResult`): simp's proof stated the side before its last proof-less folds, so the second pass read `bs.size ≤ 18446744073709551616 - 4096` and folded it again (PageSpec `remap_spec`: 41 times, each rerunning `extraFacts` and a second `omega`). What remains is `renormFacts`' own `fsimp` of every relevant fact: PageThread `fthread_remap` 19.7M heartbeats over 25 failed goals, about 10% of its cost (180k-200k heartbeats before #699, 200k-220k with #703).

Request: Run the second pass only for a side goal the walk needs: a rule's premise that decides whether the rule applies runs it within a probe's budget (or not at all), the walk's own obligations in full.

Workaround sites: `tests/roadmap/alloc-translated/PageThread.lean`

Deletion plan: Delete `fthread_remap`'s `set_option maxHeartbeats 300000` when a failed rule premise no longer pays the second pass and `fthread_remap` elaborates within 180k heartbeats (a margin under the default 200k, which it reached before #699).

<a id="row-share-gather"></a>
### #share-gather gathering partial read shares of different owners into a whole share fails closed

Status: **open**. Requester: coordinator (F4 read shares, option R, PR #713).

Note: Fail closed, not a weakening: without the premise the rules reject the gathering step; every share-free resource discharges it by `Res.excl_eq_erase` (autoParam) or `NoGather.of_R`. Counterexample to dropping it: tests/roadmap/sep-full/ShareRaceCX.lean (`twoReaders`).

Progress: Option R (maintainer 2026-11-06): a thread owns its cells and whole shares (`Mem.Owns`: every access before its clock) and only reads its partial shares (`Mem.OwnsR`: every write before its clock); the free lock likewise (`LockWord.OwnsRes`). Where two partial shares held by different owners become one whole share, the byte turns exclusive and needs every read of it ordered before the gatherer, which no clock records. The rules fail closed there: `FOwned.join` and `FCapture.join_regain` (`hg`, discharged by an autoParam for share-free parts), `FLock.Inv.join` (`hgat`), and a lock acquire (`FLock.Inv.acq`, `Inv.take`: `FLock.NoGather`, from `NoGather.of_R` for a resource without partial shares). `FOwned.take` and `FOwned.move` take the gatherer's `Mem.OwnsRes` (with `Mem.OwnsRes.addOwns` when the clock owns the taken bytes). Lost: joining two reader threads to recover a whole share, and a mutex-protected partial share whose complement the acquirer holds. RwLock does not need it: its readers return their shares through the state word's RMWs, whose release/acquire orders their reads.

Request: An explicit `Mem.Owns` premise at the gathering join (or acquire) in place of the no-gather premise, which the client discharges once every holder's reads are ordered before the gatherer (for a join: each reader thread's reads happen before its end, which the join acquires; for a lock: the protocol's release/acquire chain).

Workaround sites: `ZigLean/Sep/Full/ThreadOwned.lean`, `ZigLean/Sep/Full/ThreadSpawn.lean`, `ZigLean/Sep/Full/Lock.lean`

Deletion plan: Replace the no-gather premises `hg`/`hgat`/`NoGather` of `FOwned.join`, `FCapture.join_regain`, `FLock.Inv.join`, `FLock.Inv.acq` and `FLock.Inv.take` by the `Mem.Owns` premise of the gathered bytes (`Mem.OwnsRes.addOwns` shape), and delete `FLock.NoGather`.
