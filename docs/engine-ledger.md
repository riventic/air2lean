<!-- Generated from assurance/engine-ledger.json by scripts/engine-ledger.py generate; edit the JSON. -->
# fsym engine ledger

Engine features and fixes that proofs and libraries needed from `fsym`, and the workarounds that stand
in for the missing ones. This is the recorded deletion plan that CLAUDE.md asks for: code cites a row as
`ledger #<id>` (or ledger `` `<id>` ``), and `scripts/engine-ledger.py check` (preflight)
fails on a citation of a row that does not exist and on a closed row cited as a workaround that is still
there. Data and rules: `assurance/engine-ledger.json`, `scripts/engine-ledger.py`. 116 rows, 52 open.

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
| [3](#row-3) | ruleConcl? recognize generic FLogic.T L … rules (FAllocSpec generic in partial/total) | coordinator for D2/allocator | - | - |
| [7](#row-7) | document/plan rule preconditions ⟪φ⟫ from context facts | one-logic-tactics | - | - |
| [9](#row-9) | engine support replacing arena_* macros, within (planner rule), unroll_solo (CTriple-backend rule) | arena lane | - | - |
| [9h](#row-9h) | unroll_solo: concrete counterexample runs | arena lane | - | - |
| [13](#row-13) | optPayload | one-logic-tactics (Lists.sum) | - | - |
| [14](#row-14) | One fsym entry for other front ends | one-logic-vc | - | - |
| [15](#row-15) | Quiet stop | one-logic-vc | - | - |
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
| [61](#row-61) | A rule whose precondition has an if the facts do not decide | arena | - | - |
| [64](#row-64) | An update at a return against a state with an undecided if | fba-reset | `tests/roadmap/alloc-fba/AllocFba/Full.lean`, `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete the `by_cases hc : n.toNat < s.len.toNat` split in `fresize_spec` and the arena's `rcases Nat.lt_trichotomy n.toNat s.len.toNat` in each `resize_ct` (the latter also needs #return-bool-split) once the walk splits the state's undecided `if` before the caller's updates (replaced by the P09-E5 ghost-update registry). |
| [65](#row-65) | An update's Q₀ is compared with library atoms only | fba-reset | `tests/roadmap/alloc-fba/AllocFba/Full.lean` | restate Q0 with the library definitions (`allocPost`, `pshare`, `epFee`) once tryUpd unfolds Q0's user definitions; delete the explicit-atom form. |
| [66](#row-66) | The planner cannot produce an empty region | fba-reset | `tests/roadmap/alloc-fba/AllocFba/Full.lean` | split `alloc_upd` back into carve and grant once the planner produces an empty region and carves at an exact start with a different alignment. |
| [67](#row-67) | updHeads keeps a user head folded only at Qv's top level | fba-reset | `tests/roadmap/alloc-fba/AllocFba/Full.lean` | write `fown` with `fbody` once updHeads keeps a nested user head folded. |
| [68](#row-68) | WP walk: a side goal whose unknown is fixed by a LATER conjunct is not re-solved | L9 | `Proofs/Sync/Mutex.lean`, `Proofs/Threadsync/Mutex.lean` | reorder `workInv` / `workPost` back (the conjunct that fixes k last) once the WP walk retries deferred side goals after their unknowns are assigned. |
| [68d](#row-68d) | Full/ThreadCall (WP.call_fowned): used by fsym's WP backend | engine | - | open until PR #354 merges (it records MutexToy's plan); then close. |
| [69](#row-69) | WP rules are tried on a command with a different head; the failed unification unfolds both generated functions | L9 | `Proofs/Threadsync/Mutex.lean` | drop `attribute [local irreducible] Thread_Mutex_lock Thread_Mutex_unlock` once WP rules are keyed by the command head (or unify generated functions at reducible transparency); then `threadMutex.lock_wp` can be passed directly. |
| [69d](#row-69d) | Conc/Spec/MutexToy: witness of the legacy MutexSpec | sync lane | - | delete Conc/Spec/MutexToy together with the legacy MutexSpec (docs/proof-framework.md row); restate the relaxed-unlock counterexample against MutexImpl if wanted. |
| [70d](#row-70d) | Conc/Returns: no client yet | csl/T-term | - | first client: a turn-counting protocol proof (T-term, research C13); if T-term is dropped, delete with Proto.cost. |
| [71](#row-71) | Conc/OsRules: premise evidence, standalone by design | os lane | - | move its facts into the FutexSpec/CTriple futex rules when those land (docs/thread-io-translation.md section 4.1), then absorb the module. |
| [72](#row-72) | PageAllocator as an environment of an open std.mem.Allocator | L4 (Controls) | - | - |
| [73](#row-73) | Run-level adequacy to .illegal | L4 (Controls) | - | - |
| [74](#row-74) | PLAN (legacy-to-retire) | L4 | - | - |
| [76](#row-76) | Read of a read-shared io prefix in a protocol: hand copies of wp_io | critic run 15 (coordinator) | `Proofs/Sync/SemCounter.lean`, `Proofs/Sync/RwLock.lean`, `Proofs/Threadsync/WaitGroup.lean`, `Proofs/Sync/Semaphore.lean` | when each legacy-layer file migrates to the full-state logic (docs/legacy-retirement.md), replace its `wp_io` copy with `FLock.Fits.wp_readRest` and its holder copies with `FLock.Fits.wp_hold`, then close this row. |
| [return-bool-split](#row-return-bool-split) | A return whose Boolean value the postcondition matches on is not split | arena-gen (arena macros -> fsym) | `tests/roadmap/alloc-arena/ArenaSpec.lean`, `tests/roadmap/alloc-arena/ArenaSpecMacos.lean`, `tests/roadmap/alloc-arena/ArenaSpecFixed.lean` | delete `rcases Nat.lt_trichotomy n.toNat s.len.toNat` in each arena `resize_ct` (with #64) once the walk splits a return's undecided Boolean that the postcondition matches on. |
| [arena-resize-update-cost](#row-arena-resize-update-cost) | (perf) whole-state updates at every return: the arena's resize | arena-gen (arena macros -> fsym) | - | - |
| [77](#row-77) | Kernel evaluation of runs over a page-sized block: deep recursion / >11 GB | L4 (Controls) | - | - |
| [78](#row-78) | LawfulEnc instances for generated structs | L6 (FBA client) | - | - |
| [79](#row-79) | Struct pts to field words entailment | L6 (FBA client) | `tests/roadmap/lists-fba/ListsFba/Witness.lean` | replace ListsFba.struct_words by the library rule and close this row. |
| [P09-E1](#row-p09-e1) | residual-goal attribution | invariant-synthesis (P09) | - | - |
| [P09-E2](#row-p09-e2) | strongest-postcondition inference at returns for FTotalTriple/FTriple and the thread backends, as inferPost... | P09 | - | - |
| [P09-E3](#row-p09-e3) | abduction report | P09 | - | - |
| [P09-E4](#row-p09-e4) | @[fsym_inv] loop-invariant registry | P09 | - | - |
| [P09-E5](#row-p09-e5) | @[fsym_upd] ghost-update registry keyed by heads, tried at returns | P09 | - | - |
| [T1](#row-t1) | credits n is not split for tick_credit | stack-ac lane (codex/stack-ac-ticks) | - | - |
| [T4](#row-t4) | ticks in the CTriple backend (not attempted) | stack-ac lane (codex/stack-ac-ticks) | - | - |
| [fowned-bridges](#row-fowned-bridges) | Step through the WP.liftMem_fowned* / callMC_fownedS bridges | coordinator | - | - |
| [ofseq-one-liners](#row-ofseq-one-liners) | Seven remaining hand ofSeq one-liners | coordinator (critic run 9) | - | - |
| [stack-child-budget](#row-stack-child-budget) | A spawned thread's stack budget, reserve and sp token | stack-region lane (codex/stack-pr5) | - | - |
| [stack-wp-cur](#row-stack-wp-cur) | The WP walk hands cur t to a thread's segment (WP.liftMem_fownedCurS) | stack-region lane (codex/stack-pr5) | - | - |
| [pick-bind](#row-pick-bind) | Pick-bind rules: bind rules over pick >>= op >>= g | CSL (#19, #20) / coordinator | `tests/roadmap/sep-auto/Conc.lean` | PR #352 registers `CTriple.weakCasPtr_bind` as a bind rule (tryBindRule); then `publishWeak_spec` is a bare `unfold publishWeak; fsym` and the hand application is deleted. |
| [allocator-creation-admissibility](#row-allocator-creation-admissibility) | Bind allocator creation admissibility to the visible instance claimed | Task10 allocator-creation soundness review | - | - |
| [admission-at-state](#row-admission-at-state) | Expose exact FAdmit side goals from the currently held full state | Task10 / coordinator PR400 comment6211941344, 2026-10-16 | - | - |
| [errok-native](#row-errok-native) | WP walk of raw MemM steps in a partial protocol: the error leaf (Proto.ErrOk) from library *_native facts | S4 (audit soundness-2026-10-14) / critic run 15 | `Proofs/Atomics/Relaxed.lean`, `Proofs/Cancel/Group.lean`, `tests/roadmap/futures/Futures/Proofs.lean`, `tests/roadmap/thread-locals/ThreadLocals/Leak.lean` | when fsym walks raw liftMem steps of a protocol main and discharges `Proto.ErrOk` from the library `*_native` facts, replace the hand `WP.bind (WP.liftM (ErrOk.of_run rfl …))` chains in the workaround sites with `fsym` and delete the explicit `ErrOk.of_run` arguments; the invariant facts (`flag_single`, `flag_vals`, `status_bytes`) stay as the proofs' invariant. |

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
| [70](#row-70) | Holder field steps as one library rule (coordinator item (a)) not landed yet | DONE codex/fsym-wp-hold: the `WP` walk applies `FLock.Fits.wp_hold` itself (`fsym [hF.wp_hold (g' := gH x'), …]`, one term per place the walk reaches): a rule for every `MemM` step is tried after the others and applies only completely; the segment's precondition comes from `hpa`, the side goals from the first one about the segment's post on (`hR`, `hg'`, `hU`) are solved after the segment; `hR` by the post's atoms (`assnByHyp`: equal or provably equal values, AC), `hU` by the protocol's lemma applied backwards (`wpChain`), arithmetic facts of the protocol's shape forwards (`wpForward`); ghost values of products normalized (`upd_snd`, `upd_ne`, data fields of user values). All per-field instances are deleted; the walks of SnapshotCache (`update_spec`, `main`'s snapshot to the free), MutexCounter (both versions' `loop4_body`), Iogroup (`add_spec`) and Handoff (both versions' producer, `ready` loop and `main`'s tail from the spawn) are `fsym` calls. Regression sep-auto WPHold. |
| [75](#row-75) | Thread backend: undecided side condition blocks a sequential rule's ofSeq | DONE codex/fsym-thread-split (solveSides: a provider hypothesis with unknowns waits for the later provider goal that fixes them; one equal to an undecided goal of the rule is that goal, so the walk splits); regression sep-auto Threads resizeTo_thread; the PageAllocator's remap is a thread triple by plain fsym |
| [update-result-unknowns](#row-update-result-unknowns) | An update's result unknowns and the bundle projections of its postcondition | DONE on codex/arena-fsym (Auto.lean `tryUpd`, `reduceCtorProjs`) |
| [T2](#row-t2) | plain atom: tick_plain receipt dropped (bare fsym) | see request text (tick rows, plans/tick-cost.md) |
| [T3](#row-t3) | credits 1 consumed by tick (bare fsym) | see request text (tick rows, plans/tick-cost.md) |
| [T5](#row-t5) | tick_run kept opaque in fsym_norm | see request text (tick rows, plans/tick-cost.md) |
| [thread-loop](#row-thread-loop) | Loop rule for a Zig.loop in a thread (FTTriple) | DONE PR #319 (codex/fsym-thread-loop: Full/ThreadLoop) |

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

Status: **open**. Requester: one-logic-vc.

Note: vc_gen (PR #202) calls its own path; the shared Auto.run entry is not confirmed

Progress: open

Request: One fsym entry for other front ends: expose `Zig.Full.Auto.run (g) (user : Array Expr) (extra : Array Syntax) : TacticM (List MVarId)` = what `evalFsym` does after elaborating its args (intros, `reduceProjs` of hyps, `withRunCaches`, `arithSimpCtx`, `walk … 400`); `evalFsym` calls it. `vc_gen` (ZigLean/VC/Extract.lean `memVc`) then calls it instead of re-doing `withRunCaches`/`arithSimpCtx`/`walk` and missing intros/reduceProjs

<a id="row-15"></a>
### #15 Quiet stop

Status: **open**. Requester: one-logic-vc.

Progress: open

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

Request: **Heartbeats (gate `assurance/heartbeat-budgets.json`, measured with fsym-perf):** `append_pos` 861k, `append_zero` 794k, `precise_pos` 284k (default budget 200k); every other list proof fits the default. `append_*` are dominated by the `precise_*` callee rule application and the `cases x <;> fsym` re-walks of #20/#35.

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

Note: plain case works; needs the arena resize case

Progress: open; the plain case WORKS on fsym-wp (agent 14 /tmp/fsym-eng/f14/T61.lean: a rule with `if n < len then … else …` in its pre, against the same undecided `if` in the state, framed). Needs the arena's resize (`relBytes`, a `callIndirect` rule) to reproduce

Request: **A rule whose precondition has an `if` the facts do not decide** (`relBytes s.ptr … n len tl`: `if n < len`) is not applied; `fsym` then walks the `callIndirect` arms inline (into the page allocator's `munmap`) and stops with "no rule". Needed: split on the undecided condition, as for side conditions. Workaround: `resize_shrink`/`resize_grow` (Core), the condition a side goal of each.

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

Status: **open**. Requester: engine.

Note: dead-module row 68 of agent 17; the handoff also numbered the L9 row 68; this one is 68d

Progress: DONE PR2

Request: `Full/ThreadCall` (`WP.call_fowned`): USED — fsym's WP backend applies it as a caller rule (`fsym [WP.call_fowned hf …]`); regression sep-auto WP `call_contract` (every protocol meeting hinv/hloc, f known only by CTriple). Next: real client (CAllocSpec entry in a thread protocol)

Deletion plan: open until PR #354 merges (it records MutexToy's plan); then close.

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

Progress: plan

Request: `Conc/OsRules`: proof-only premise evidence for OSF-01/02, OST-01/02, OSG-01 (docs/premises.md "Derived from", docs/os-threads.md); standalone by design (not dead). PLAN: its facts move into the FutexSpec/CTriple futex rules when those land (docs/thread-io-translation.md §4.1), then the module is absorbed

Deletion plan: move its facts into the FutexSpec/CTriple futex rules when those land (docs/thread-io-translation.md section 4.1), then absorb the module.

<a id="row-72"></a>
### #72 PageAllocator as an environment of an open std.mem.Allocator

Status: **open**. Requester: L4 (Controls).

Progress: part 1 #369 (CTriple.toSoloThread: no Tgt map needed; alloc/free/resize thread triples); part 2 codex/l4-page-env (remap thread triple after #368, PageThread.cAllocSpec); left: the page-backed Lists.Open env (with the Controls restatement)

Request: **PageAllocator as an environment of an open `std.mem.Allocator`**: the translated PageAllocator's entries as thread triples (FTTriple, the FBA `fthread_*` pattern), `alloc` generic over the program's `Tgt` (PageLinux's alloc is a `CTriple` over `ConcM PageLinux.Tgt`; its RawVTable form wraps it in `Sched.soloRun 16`), then `CAllocSpec.ofRaw`/`env_ofRaw` → `CAllocSpec (CVTable.env (Lists.Alloc.env e) fns)` for a page-backed `Lists.Open.Ext`. Library + alloc-translated, no new judgment

<a id="row-73"></a>
### #73 Run-level adequacy to .illegal

Status: **open**. Requester: L4 (Controls).

Progress: part 1 #364 (KFact.dead, free_dead, munmapWhole_dead, Holds.dead); part 2 codex/l4-page-env (FAllocInv.freed in free's post, coordinator decision B); left: the page allocator's freed = dead and the Controls restatement

Request: **Run-level adequacy to `.illegal`**: a library theorem over the existing judgments that reads a `CTriple` run (soloRun) down to "the block the client gave back with `munmapWhole'` is dead", so that a later access/munmap is `.illegal` (`Os.munmap_whole_then_illegal`, `access_illegal`, ZigLean/Os/MmapRun.lean). Kernel evaluation is not an option: `decide +kernel`/`unroll_solo` on `soloRun (setup; Open.push …)` with a page env exceeds maxRecDepth and, raised, 11 GB RSS as soon as a memory op follows `mem_Allocator_create`. If this needs a new judgment: stop and report

<a id="row-74"></a>
### #74 PLAN (legacy-to-retire)

Status: **open**. Requester: L4.

Progress: open: #72 and #73 have their parts (page allocator CAllocSpec env, KFact.dead, FAllocInv.freed, page freed = dead block, Lists.Alloc.freeAll_freed); the unconditional refutations wait on #77 (one concrete start memory in which push succeeds, evaluated by the kernel)

Request: PLAN (legacy-to-retire): `tutorials/memory-safety/Controls.lean` stays a legacy user (imports `Proofs.Lists.Cost`, std heap model) until #72 + #73 + #77; then its three refuted clients are restated over `Proofs/Lists/Open.lean` with the page-backed env (existential refutations: an admissible start memory in which push succeeds, from #77, and the double free / use after free `.illegal` there via `freeAll_freed`, `PageTok.deadOf`, `Holds.dead`, `Os.munmap_dead`/`access_illegal`) and it leaves `legacy_users`

<a id="row-75"></a>
### #75 Thread backend: undecided side condition blocks a sequential rule's ofSeq

Status: **closed**. Requester: L4.

Progress: DONE codex/fsym-thread-split (solveSides: a provider hypothesis with unknowns waits for the later provider goal that fixes them; one equal to an undecided goal of the rule is that goal, so the walk splits); regression sep-auto Threads resizeTo_thread; the PageAllocator's remap is a thread triple by plain fsym

Request: **Thread backend: undecided side condition blocks a sequential rule's `ofSeq`** (blocks L4 #72). `fsym` proves the translated PageAllocator's `free` and `resize` as thread triples (`FTTotalTriple`, plain `fsym`), but not `remap`: at `Os.mremap … MAYMOVE` the sequential walk (`PageSpec.remap_spec`) tries `FTotalTriple.mremapMoveC`, gets the side goal `S - lo < newLen` left and **splits on it**; the thread walk tries the same rule through `ofSeq`, and its `ThreadLocal` side goal (provider `ThreadLocal.mremapMove_of`, which needs that same `hn`) fails first, so the rule fails. Repro: branch `scratch/l4-remap-thread`, `scratch-l4/RemapThread.lean`. A provider without `hn` (`ThreadLocal.mremap_of`) was not picked up either. Request: in the thread backend, split on the undecided arithmetic side goals before solving the `ThreadLocal` goal, or try providers after the split

<a id="row-76"></a>
### #76 Read of a read-shared io prefix in a protocol: hand copies of wp_io

Status: **open**. Requester: critic run 15 (coordinator).

Progress: PARTLY DONE codex/fsym-wp-shared (#373): the library rule `FLock.Fits.wp_readRest` (ZigLean/Sep/Full/LockSteps.lean). The full-state copies in Iogroup/Counter, Handoff/Ops and MutexCounter/Protocol are deleted; their walks pass the protocol's obligations to the rule. LEFT: the copies in the legacy-layer files RwLock and SemCounter (`ZigLean.Conc` logic, legacy_users), and the legacy holder copies WaitGroup `wp_cntLoad`/`wp_cntStore` and Semaphore `wp_cnt`. These go when those files migrate to the full-state logic.

Request: **`wp_io` has hand copies**: the read of the `io` prefix (read-shared bytes in the protocol's rest, `FLock.Inv.recordX`, no race by `ReadShared.noRace_read`) is proved by hand once per protocol: `Proofs/Iogroup/Counter.lean`, `Proofs/Handoff/Ops.lean`, `Proofs/MutexCounter/Protocol.lean`, `Proofs/Sync/SemCounter.lean`, `Proofs/Sync/RwLock.lean`. Needed: one `@[fsym]` library rule over every protocol with a lock whose rest keeps read-shared bytes, each protocol discharging only its obligations (the bytes in the rest, the invariant kept by a read record).

Workaround sites: `Proofs/Sync/SemCounter.lean`, `Proofs/Sync/RwLock.lean`, `Proofs/Threadsync/WaitGroup.lean`, `Proofs/Sync/Semaphore.lean`

Deletion plan: when each legacy-layer file migrates to the full-state logic (docs/legacy-retirement.md), replace its `wp_io` copy with `FLock.Fits.wp_readRest` and its holder copies with `FLock.Fits.wp_hold`, then close this row.

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

Progress: DONE on codex/arena-fsym (Auto.lean `tryUpd`, `reduceCtorProjs`)

Request: **`tryUpd` solved an update's side goals before it compared `Q₀` with the return's postcondition**, so an unknown that only `Q₀` names (the result `r` of the arena's `rresizePost … r`, constrained by `r = true`) was taken from any fact of the side goal's shape (`Rat.blt 0 φ.val = true`), and the projections of an expanded bundle (`v.A'` of `v : FV`) were reduced in `P₀` and the side goals but not in `Q₀`, so `acEq` with the return's postcondition failed. Fixed: `Q₀` (projections of constructor applications reduced, `reduceCtorProjs`) is unified with the return's postcondition (same head, reducible) before the side goals.

<a id="row-77"></a>
### #77 Kernel evaluation of runs over a page-sized block: deep recursion / >11 GB

Status: **open**. Requester: L4 (Controls).

Progress: open (no workaround; blocks #74)

Request: **The kernel cannot evaluate a run that writes into a block of 4096 bytes.** `decide +kernel` on `do let p ← Zig.alloc .heap 4096 8; Zig.memset (α := BitVec 8) 1 p 16 none; Zig.store (α := BitVec 32) 4 p 7` from `{}` fails with "(kernel) deep recursion detected" (0.9 GB); the same with 16 bytes decides in 0.6 s. The L4 Controls hit it through the translated PageAllocator (every grant is a 4 KiB mapping): Open's `push` with a page-backed env (`create` -> `allocBytesAligned` memsets the 16 bytes, then `push` stores the fields) does not decide from a concrete start memory; raising `maxRecDepth` (4000 to 200000) makes `decide +kernel` and `unroll_solo` exceed 11 GB RSS (build-guard rss_limit). The page `alloc` alone decides (`PageAlloc.alloc_top`), and so do runs that only read the page or write it without a prior `memset`. Needed: one concrete admissible start memory in which `push` returns `.ok p`, evaluated (kernel-checked), so that the refutations of #74 are existential (natively right: `mmap` may fail, so no triple promises `.ok`). Likely cause: the kernel's representation of the 4096-byte `Array Byte` (list-backed; `writeBytes`/`extract`/`append` are linear recursions) under `memset` + `store`. Options: a bytes representation the kernel reduces with bounded depth (e.g. chunked or `ByteArray`-like with kernel-friendly ops), or a run lemma family that rewrites the memset/store effect on a symbolic block (`simp`/`fsym_norm` equations) instead of evaluating the array. Repro files: `~/.cache/air2lean/scratch/l4/T36.lean` (minimal), `T32.lean` (Open push with the page env from a precomputed memory, rss_limit), `T34.lean` (page alloc + memset + store).

<a id="row-78"></a>
### #78 LawfulEnc instances for generated structs

Status: **open**. Requester: L6 (FBA client).

Progress: open

Request: **The translator's generated structs have no `LawfulEnc` instance** (`Enc` only), so `decode (encode w) = pure w` and `(encode w).size = Enc.size T` are not available for them. Effect: after `FTotalTriple.storeBlock` stores a struct into a stack block (`store 8 s1 (sv : heap_FixedBufferAllocator)`), the state holds `up (bytesAt s1 A 24 .stack (writeBytes undef 0 (encode sv)))`, and `fsym` cannot fold it back into `up (pts s1 8 sv)` at a return (the fold needs the decode equation). The legacy FBA client proved `slice_decode_encode` and the struct's field decodes by hand. Needed: the translator emits a `LawfulEnc` instance for each generated struct (or a generic theorem for the struct `Enc` shape it builds), and an `@[fsym_view]` fold `bytesAt` -> `pts` for a `LawfulEnc` value. Repro: tests/roadmap/alloc-fba/wip/ClientStart.lean on codex/l6-client-wip.

<a id="row-79"></a>
### #79 Struct pts to field words entailment

Status: **open**. Requester: L6 (FBA client).

Progress: open

Request: **No entailment from a struct's `pts` to its field words.** `fsym_entail` leaves `EUpd (up (pts s1 8 (sv : heap_FixedBufferAllocator))) (up (pts s1 8 sv.end_index) ⋆ up (pts (s1.add 8) 8 sv.buffer))` open (FBA's invariant holds the struct as two words, `wEnd`/`wBuf`). lists-fba proves the same split by hand from the bytes (`ListsFba.struct_words`, via `bytesAt_split` and per-field decodes). Needed: one library rule (`@[fsym_view]` or planner step) that cuts a generated struct's `pts` into its fields' `pts` and joins them back, for any struct the translator generates (the field offsets and decodes from `structFields?`, as the field load/store rules of row 28 do). Then `struct_words` goes. Repro: tests/roadmap/alloc-fba/wip/ClientStart.lean on codex/l6-client-wip.

Workaround sites: `tests/roadmap/lists-fba/ListsFba/Witness.lean`

Deletion plan: replace ListsFba.struct_words by the library rule and close this row.

<a id="row-p09-e1"></a>
### #P09-E1 residual-goal attribution

Status: **open**. Requester: invariant-synthesis (P09).

Progress: pending maintainer approval

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

Status: **open**. Requester: stack-ac lane (codex/stack-ac-ticks).

Progress: see request text (tick rows, plans/tick-cost.md)

Request: not attempted (CTriple backend, phase 2).

<a id="row-t5"></a>
### #T5 tick_run kept opaque in fsym_norm

Status: **closed**. Requester: stack-ac lane (codex/stack-ac-ticks).

Progress: see request text (tick rows, plans/tick-cost.md)

Request: OK so far: `tick_run` is `@[zig_unfold]` (Mem/Lemmas) but fsym's rule match on `Zig.tick` fires first in the repro; keep `tick` opaque in fsym_norm when the emitter (L8b) inserts `callM tick`.

<a id="row-fowned-bridges"></a>
### #fowned-bridges Step through the WP.liftMem_fowned* / callMC_fownedS bridges

Status: **open**. Requester: coordinator.

Progress: part 1 (codex/fsym-fowned): the WP walk takes a thread's own stack block before its spawn through the registered `WP.liftMem_fowned` segments: allocation, field pointers (`Reaches.bauth`: the block's size from its extent), stores at byte offsets (`FTotalTriple.storeBytesAt`, Int offsets as generated code writes them), closed sizes of encodings (`reduceClosedSize`, kernel evaluation; closed side goals by `decide +kernel`); regression sep-auto WP `block_fields`; on Sync/Mutex `main` the walk reaches the spawn. Open (part 2): the start of the protocol at the spawn. (a) memory facts across segments that the segment rule does not carry (`m.atomics = #[]`, `m.waiters = #[]` for `inv_start`/`inv_of_box`; `FStepIn` has no atomics equation): forward facts from a step's run equation (`store_atomics`, `alloc_ok`), which `wpHyp` skips today (`hasRun`); (b) the block's pointer is `cPtr` (`alloc_ok` on the start memory, `m0.blocks.size = 0`), which the protocol's `init` needs; (c) `inv_start`/`inv_of_box` as chain lemmas: premise `X (own 0)` with unknowns `A bs` and `bext` against the walk's `bauth … Frac.one` (`assnByHyp` matches atoms without unknowns), `FOwned (upd (fun _ => rnil) 0 r)` against `upd plainOwn 0 r'` (`plainOwn` normal form); (d) after the spawn, `inv_spawn` forward from the fork's run equation (premises `P.inv G₁ m₁`, `G₁ 0 = g`, the run).

Request: fsym should step through the WP.liftMem_fowned*/callMC_fownedS bridges (~20 hand call sites) so the 4 remaining alloc FTT ofSeq forms in Block.lean can be deleted (#329 body has details).

<a id="row-ofseq-one-liners"></a>
### #ofseq-one-liners Seven remaining hand ofSeq one-liners

Status: **open**. Requester: coordinator (critic run 9).

Progress: PR #352 (open) deletes the term-level copies

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

Status: **open**. Requester: CSL (#19, #20) / coordinator.

Progress: prototype green on scratch/fsym16-pickbind; PR #352 (open)

Request: fsym pick branch (Auto.lean ~4410) should also try @[fsym] CTriple rules stated on a pick-bind sequence `pick f >>= fun c => liftMem (op c ..) >>= g` (needed for weak cmpxchg choice 1). Coordinate with the CSL lane, which may write the rule first.
- CSL #20 (2026-10-14): the rule exists on codex/csl-s4-followups: `CTriple.weakCasPtr_bind` (ZigLean/Sep/Full/AtomicRules.lean,
  end): `CTriple (aptsE p v) (pick (weakCasPtrCount 8 p v) >>= fun c => liftMem (cmpxchgWeakPtrAt c succ fail 8 p v new) >>= g) S`
  from `hn : CTriple (aptsE p new) (g none) S` and `hs : CTriple (aptsE p v) (g (some v)) S` (side triples, not facts). Not
  @[fsym] yet. Regression sep-auto/Conc publishWeak_spec applies it by hand (WORKAROUND comment); when the pick branch tries
  pick-bind rules, register it and make the regression a bare `fsym`.
- CSL #20 (2026-10-14) CORRECTION: NOT a flake. The one failure of sep-auto Views `fact_left` ("unknown metavariable"
  at `fsym_entail`) in the S4 gate ran against a stale Auto.olean right after a merge (check.sh does not build);
  green once built. No engine issue. (Lesson: build before running checks after a merge.)

Workaround sites: `tests/roadmap/sep-auto/Conc.lean`

Deletion plan: PR #352 registers `CTriple.weakCasPtr_bind` as a bind rule (tryBindRule); then `publishWeak_spec` is a bare `unfold publishWeak; fsym` and the hand application is deleted.

<a id="row-allocator-creation-admissibility"></a>
### #allocator-creation-admissibility Bind allocator creation admissibility to the visible instance claimed

Status: **open**. Requester: Task10 allocator-creation soundness review.

Note: Existing family and proof-binder regressions remain in tests/roadmap/claims/Fixture.lean. Full-state-only AllocatorApplications.lean adds exact/mismatched dependent arguments, False/Holds and scope controls, producer/invariant aliases, higher-order/polymorphic forwarding, structure fields, type-only indices and unknown callbacks. Named-body controls include foreign generic projections and an admitted direct spec0 masking a hidden unadmitted spec1; own-body checks retain transitive foreign admission before caching the named result. Fresh applications remain unbound until actual created-result binding is extracted; relabelling a visible value as fresh cannot authenticate another member. These new source controls still need kernel/extractor execution after the complete Lean prerequisite. No new judgment or tactic. Arena creation remains a subsequent instance obligation.

Progress: Maintainer chose exact applied-argument admission (PR400 comment6209913710, 2026-10-16). Checked actual applications retain their full dependent context; only an exact original root FAdmit hypothesis or closed checked let can bind admission. Serialized False/Holds contexts do not suffice. Rejected FBA/page seed/client glue is removed from active scope; bounded generic transport/tool module compilation passed on main7ef, before subsequent source-only specialization repairs. Official full prerequisite and kernel/extractor controls remain pending. Coordinator approved generic engine row admission-at-state in comment6211941344; it must land separately after batch8, PR409 and fsym engine part2 on main, before concrete FBA/page acceptance. Direct checked context evidence is intentionally incomplete for those instances. Task13 native holds_mem is also a strict main dependency. No Auto/registry edit, hand seed or per-FBA facts lemma is installed. Unbound uses remain fail closed; F2 is not fixed.

Request: Keep the existing FTotalTriple/FAdmit framework. An existential nonvacuity witness for a parameterized creation theorem does not establish admissibility for every visible instance: admissionFamilySpec n has own = lift(n=0), a total creation triple from lift(n=0), and a valid witness choosing zero, while FAdmit(lift(1=0)) is impossible. Retain the actual applied visible contract arguments and require checked FAdmit of the creation precondition at those exact arguments. A parameterized client carries that same admission predicate, not a second hand-stated domain. Derive actual arguments/resources from translated initialization with general fsym and start-memory rules; PR409 owns generic struct encoding/splitting support. Do not require admission for invalid raw pointers, silently select one convenient family member, erase impossible or dependent premises, hand-write client admission walks/seeds, or weaken the contract.

<a id="row-admission-at-state"></a>
### #admission-at-state Expose exact FAdmit side goals from the currently held full state

Status: **open**. Requester: Task10 / coordinator PR400 comment6211941344, 2026-10-16.

Note: Coordinator decision https://github.com/riventic/air2lean/pull/400#issuecomment-6211941344. Current memFactsOf considers single atoms and ordered pairs and atomFacts matches exact head keys; pre_mfact is only an ordinary rule. The approved target-aware feature reuses the existing state planner instead of changing that registry. Keep unbound_admissibility fail closed until real instance evidence verifies.

Progress: APPROVED general engine feature; no existing hook. Implementation waits for main landing order batch8, PR409, fsym engine part2, then this small separate engine PR. Current source/API analysis is not a new kernel-checked failure of a translated FBA proof; no Auto edit has been made.

Request: Add ordinary library lemma FAdmit.of_holds with exact goal Holds m r rF -> (P ⋆ R) r -> m.FSeq -> FAdmit P. When existing fsym encounters FAdmit X as a contract-use side goal, plan X ⋆ ?R against the CURRENT held assertion using the existing planner and frame rule, retaining the actual dependent arguments and context. Add a sep-auto regression with actual state/frame and mismatched-argument rejection. No wildcard MemFacts, new registry, judgment, tactic, proof template, per-allocator facts lemma, fabricated seed or permissive claim-gate fallback. Implement only on main after PR409 and fsym part2 have landed; do not stack or copy those branches. This must land before allocator-creation-admissibility/F2 can accept concrete FBA/page instances.

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
