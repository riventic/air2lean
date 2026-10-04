# 1.0 review strategy

Baseline: `5a849265f4a38d6bd05aec81aa270b6c81d11b5d`; 838 tracked files. The working tree was clean when the review began. `REVIEW_COVERAGE.tsv` preserves the original 20 independent GPT-6.1 Sol reviewers' per-file coverage and baseline SHA-256 hashes. Temporary finding reports were lost in the interrupted session; the ledger records review depth, not a surviving finding report or final test result.

1. Inventory all tracked project files, including hidden CI configuration, generated code, patches, data and documentation. Exclude Git internals, build caches and downloaded dependencies.
2. Give every file one primary independent GPT-6.1 Sol reviewer. Read handwritten and generated Lean/Zig/shell/configuration files fully. For large AIR and JSONL corpora, parse each file in full, inspect schema and semantic summaries for each file, and trace representative or suspicious records to source and generated Lean. Record the method honestly.
3. Review these disjoint scopes in parallel. Within each scope check conditions and boundaries, error paths and guards, callers/callees, language pitfalls, adapter forwarding, reuse, simplification, efficiency, abstraction and repository conventions. Compare proofs with the claimed semantics and assumptions.

| Scope | Files | Lines |
|---|---:|---:|
| infra | 11 | 1795 |
| parser_checker | 9 | 2811 |
| emitter | 1 | 2394 |
| docs | 8 | 1362 |
| proofs_value | 20 | 4908 |
| proofs_conc_a | 11 | 10052 |
| proofs_float | 6 | 1819 |
| proofs_mem | 9 | 3741 |
| proofs_conc_b | 13 | 19958 |
| runtime | 9 | 679 |
| concurrency | 11 | 9088 |
| floats | 9 | 3542 |
| memory_sep | 13 | 3355 |
| examples | 29 | 2174 |
| harness | 34 | 7387 |
| fixtures_inputs | 196 | 87294 |
| fixtures_versions | 160 | 120065 |
| fixtures_values | 173 | 42528 |
| fixtures_conc | 105 | 137374 |
| exporter | 11 | 1767 |

4. Establish baseline compilation, proof checking, no-sorry checks and available differential tests. Record unavailable compiler versions or host restrictions.
5. Independently verify each suspected defect as CONFIRMED, PLAUSIBLE or REFUTED. A finding must describe a concrete input/state and wrong behavior. Keep real limitations distinct from bugs.
6. Report each scoped pass and apply confirmed fixes sequentially. Add focused regressions where they test meaningful behavior. Preserve proof soundness; never add sorry, admit or an unjustified axiom.
7. Run fresh gap reviewers after the first pass, then the /simple four-angle cleanup over the changes. Recheck the final diff for correctness and run appropriate builds and regressions.
8. Reconcile reviewer coverage against the entire baseline inventory and deliver a per-file coverage ledger, test results, fixed issues and remaining limitations. Keep the original baseline ledger intact and record review of added files separately. Final test results must come from the completed integration checks, not the baseline coverage ledger.

Coverage depth is explicit: structured fixture inspection is not a claim that every repetitive JSON line received a separate manual judgment. A completed review reduces risk and does not prove the absence of bugs.

## Resumed integration and delivery

The user authorized scoped worktrees and draft pull requests. Repairs are grouped into these
integration scopes, with one owner per file (the CI review step belongs to integration/docs):

| Scope | Contents |
|---|---|
| Translation and examples | AIR parser/checker/emitter, exporter and compiler wrappers, example fixes and relevant goldens, parser and emission/exporter regressions |
| Runtime semantics | memory, concurrency and float semantics, affected proofs, focused runtime regressions and float model documentation |
| Proof hygiene | pointer/slice theorem fixes, proof namespace composition and aggregate handwritten-proof imports |
| Validation scripts | golden/differential/mutation/probe harnesses and shell regressions |
| Test inputs | differential corpus generation, edge cases and input consistency regression |
| Integration and documentation | this strategy, baseline coverage, package version 1.0.0, public documentation, final regression driver and its CI step |

Draft PRs 47 (proof hygiene), 48 (validation scripts) and 49 (runtime) are independent and
merge first. PR 50 (translation) depends on 48 and 49 through
`codex/review-translation-base`; PR 51 (test inputs) depends on 50. PR 52 (integration/docs)
uses `codex/review-integration-base`, the union of 47–51. Its driver requires the complete
suite and fails if a dependency file is missing. The input PR uses
`codex/review-test-inputs-scoped`, created non-destructively before the original input
branch's verification-only scripts merge to keep its diff scoped.

During this resumed session, only the coordinator runs Zig, Lake or Lean, including scripts
that launch them. All such commands share one serial queue across worktrees. The local
resource guard takes an exclusive build lock, sets `LEAN_NUM_THREADS=1`, isolates Zig caches
per worktree, monitors total descendant RSS and elapsed time, and terminates the command's
process group when its configured memory or time budget is exceeded. The default guard
budgets are 8 GiB and 15 minutes; each recorded check includes the command, worktree, exit
status, peak RSS, elapsed time and log path. Reviewers perform static inspections and submit
explicit test requests. Parallel CI matrix jobs run on separate runners; the session's local
serialization rule does not require disabling that matrix.

`scripts/review.sh` requires the complete regression suite before starting. It builds the
translator and proofs, elaborates the aggregate proof and float regressions, executes the
concurrency, memory and parser test `main` functions, then runs input, emission and exporter
checks. Parser and emitter test generators write semantic fixtures into a temporary directory;
the emission driver preserves the six parser fixtures, adds 19 emitter fixtures, and
elaborates all 25 generated files serially without nested compiler launches. CI invokes it
after the selected version's translation and proofs have been checked,
for every non-mutation matrix job, including 0.14.1. Its synthetic parser cases are independent
of the selected Zig version; aggregate imports use the generated modules already selected by
`check.sh`. Compiler-exporter checks use CI's current patched compiler and translator; local
runs without the opt-in compiler variables cover the exporter shell/cache regressions only.

## Recorded integration validation

The coordinator reported these completed checks from the serial guarded queue:

| Check | Result |
|---|---|
| Actual input generator | All 185 input files reproduced byte-for-byte |
| Compiler-exporter regressions | Passed with freshly patched Zig 0.15.2 and 0.16.0 |
| Stock compiler spawn regressions | All 11 cases passed with each of Zig 0.15.2 and 0.16.0 |
| Inline assembly regression | Passed with stock Zig 0.15.2 |
| Focused shell harness regressions | All 32 passed; `normalize-air.py` is part of the validation-scripts PR |
| Full generated-code regeneration | All 29 generated modules regenerated and checked |
| Proof variants | Zig 0.14.1/0.15.2/0.16.0 translations each passed the full `Proofs` target (103 jobs) and all 40 handwritten imports; 0.15.2 Darwin threadsync passed (44 jobs). Peak 2,188.9 MiB, 57.4 s (`proof-variants.log`) |
| Parser/emitter semantics | All 21 generated fixture files passed (`emitter-capture.log`) |
| Baseline coverage audit | 838/838 actual Git objects match ledger hashes; no missing or duplicate paths |
| Zig 0.15.2 differential rerun | Passed: 85,801 selected cases, zero mismatches; 78,143 `ok`, 4,975 `fail`, 1,077 pinned `unspecified`, 1,606 existing host exceptions |
| Zig 0.16.0 final differential rerun | Passed on final generated code: 85,861 selected cases, zero mismatches; 79,043 `ok`, 4,975 `fail`, 1,077 pinned `unspecified`, 766 existing host exceptions. Peak 650.5 MiB, 176.1 s (`diff16-pinned-final.log`) |
| Zig 0.15.2 exception pins | All rows of the four exact pins independently verified (`82dc776`) |
| Zig 0.15.2 full golden check | Passed with actual compiler dumps |
| Zig 0.16.0 final full golden check | Actual compiler pipeline passed (44 jobs; `goldens16-final.log`) |
| Integrated regression suite | `scripts/review.sh` passed: 32 shell checks, full `Proofs`, 40 joint imports, runtime execution, 21 emitted fixtures, inputs and actual exporters 0.15.2/0.16.0. Peak 2,177.3 MiB, 41.9 s (`integration-review.log`) |

All final local checks passed. The golden checks also verified the genuine 0.16.0
`floatops.divExact64` override and seven corrected sync packed-constant fixtures (four
shared, three Linux); their bit encoding received independent verification.

The 8 GiB guard stopped a ReleaseFast compiler bootstrap at 8,233 MiB. Stripped Debug
builds with `-j1` completed: Zig 0.15.2 peaked at 3,419 MiB and Zig 0.16.0 at 4,526 MiB.
The memory cap was not raised.

Native Zig 0.14.1 bootstrap was blocked on this macOS host before exporter validation:
its host build runner could not resolve libc symbols against the installed SDK. Only full
SDKs 26.5 and 27 were found; both use `arm64e` target tags for the relevant libc exports,
while Zig 0.14.1 matches `arm64`. No compatible older full SDK or simple supported
workaround was established. Linux CI retains the 0.14.1 matrix job; its final run result
must be reported separately. The local guard's 8 GiB cap remains in force.

The first complete Linux CI run passed the 0.14.1 exporter/translation/proof job and four
mutation shards. The 0.15.2 and 0.16.0 full jobs exposed f128 multiplication and f80 edge
differences hidden by this Mac's existing host exceptions. Mutation shard 5 also found a
stale sentinel-free mutation. These failures motivated the second review wave below.
An earlier PR 50 run lacked PR 48's `target_endian` normalization dependency; its base and
head ancestry now include that dependency. Local passes do not imply a completed Linux run.

## Supplemental coverage for added files

The baseline ledger remains 838 files. Before the merge reconciliation below, the
baseline-to-integration added-file inventory contained these 27 files.
Every added path has an owner and final-review assignment; none is uncovered. Assignments
record review scope separately from the completed local checks and Linux CI results.

| Final reviewer | Owner | Added files |
|---|---|---|
| final_proof_scripts | Proof hygiene (`AllProofs`); validation scripts (`scripts/`) | `tests/review/AllProofs.lean`, `scripts/normalize-air.py`, `scripts/review-checks.sh` |
| final_runtime_concurrency | Runtime semantics | `tests/review/Concurrency.lean` |
| final_runtime_memory_floats | Runtime semantics | `tests/review/Memory.lean`, `tests/review/Floats.lean` |
| final_translation_parser | Translation and examples | `tests/review/Parser.lean` |
| final_translation_emitter; coordinator actual pipeline | Translation and examples | `tests/review/Emitter.lean`, `tests/review/emitter.sh`, `tests/review/regenerate.sh`, `tests/golden/0.16.0/floatops/air/floatops.divExact64.json` |
| final_exporter_examples | Translation and examples | `tests/review/exporter-checks.sh`, `tests/review/exporter.zig`, `tests/spawn_cleanup.py`, `tests/asm_early_clobber.py`, `examples/asm/zig-versions`, `examples/atomics/zig-versions`, `examples/floatconv/zig-versions`, `examples/lists/zig-versions`, `examples/slices/zig-versions`, `examples/threads/zig-versions`, `examples/vectors/zig-versions` |
| final_translation_parser + final_runtime_concurrency; coordinator actual dump | Translation and examples | `tests/golden/0.15.2/threadsync/air-linux/Thread.Condition.signal.json` |
| resume_inputs | Test inputs | `tests/review/inputs.py` |
| resume_docs + coordinator | Integration and documentation | `REVIEW_STRATEGY.md`, `REVIEW_COVERAGE.tsv`, `scripts/review.sh` |

## Second review wave

The user requested further improvements. Independent GPT-6.1 Sol agents reviewed AIR/CLI,
translation, runtime/concurrency and tooling; separate adversarial agents checked each fix
scope. Four additional agents applied `/simple`'s reuse, simplification, efficiency and
altitude angles. Reviewers remained static-only; the coordinator kept the single global
compiler queue and unchanged 8 GiB memory cap. This wave changes 26 already-covered files
and adds no tracked files: all 865 tracked paths at that wave's head retain primary coverage.

| Scope | Independently checked files |
|---|---|
| AIR/CLI | `Air2Lean/Air/{Op,Json,Canon}.lean`, `Air2Lean/{Check,Main}.lean`, shared `Emit.childTys` removal, `tests/review/Parser.lean`, `docs/{air-json,generated-code}.md` |
| Names | `Air2Lean/Emit.lean`, `tests/review/Emitter.lean`, `docs/generated-code.md` |
| Float and model claims | `ZigLean/Float/{Ops,CompilerRt}.lean`, float emission, `Proofs/Floatops/{Gen,Proofs}.lean`, `tests/golden/0.15.2/floatops/Gen.lean`, `tests/review/Floats.lean`, `docs/floats.md`, `ZigLean/Mem/Thread.lean`, `docs/std-models.md` |
| Tooling | `scripts/{mutate,review-checks}.sh`, `tests/review/{emitter,exporter-checks,regenerate}.sh`, `zig-patch/{build.sh,README.md}` |

The fixes reject cyclic value types, unavailable instruction references, malformed constants,
markers and flags, unsupported vector reinterpretations/pointer vectors, and omitted spawn
workers. Generated type/function names avoid body binders and the pinned Lean parser's
reserved words. Type validation and binder lookup use indexed membership; repeated float
limb calculations are cached. CLI help, namespace validation and IO errors have smoke checks.

The target float model now includes the genuine compiler-rt f128 lost-carry behavior, f80
remainder representation preservation and pre-0.16 f80 floor/ceil conversion. IEEE operations
remain distinct. The public f80 operation theorem explicitly excludes a pseudo-denormal input;
all selectors remain covered. The concurrency documentation records the existing read-view
transfer overapproximation instead of claiming exact RC11 behavior.

The compiler builds into an adjacent staging directory, locks the binary before publication,
excludes same-prefix writers and retains/restores previous installations on publication
failure. Its default is stripped Debug with one build job. Emission checks generate fresh
fixtures and validate producer completeness; mutation detection requires a clean unmutated
differential baseline and targets the current sentinel-free implementation. Bash 3.2 remains
supported.

PR 53 contains names, PR 54 float/model repairs, PR 55 tooling and PR 56 AIR/CLI. PR 56 is
based on 53; the other three are based on the complete first-wave PR 52. The second integration
base is `codex/review-more-base`, the union of these fixes. Its small integration PR pins all
19 emitter cases and records this review. Every PR is a draft; none is merged. After a
dependency reaches `main`, retarget its child PR to `main` before merging it. Union branches
serve as validation bases, without adding another code-fix PR.

Completed local checks include all 46 shell regressions under current Bash and macOS Bash
3.2; a real staged/locked Zig 0.16 bootstrap (4,315.7 MiB peak, 195.2 s); exact native source
`wideMultiply` checks for Zig 0.15.2 and 0.16.0; full proof/runtime regression checks;
all 25 generated parser/emitter semantic files; input coverage; actual exporter checks;
and CLI help, valid/rejected namespaces and IO error paths. The second-wave cross-version,
golden and native differential results and complete-stack Linux CI status are recorded below.

| Second-wave integration check | Result |
|---|---|
| All version proof variants | 0.14.1, 0.15.2, 0.16.0 full `Proofs` and all 40 handwritten imports passed; Darwin Threadsync passed. Peak 2,188.7 MiB, 66.8 s (`floats-all-versions.log`). |
| Actual 0.16 golden pipeline | Passed AIR comparisons, translation and generated proof builds; peak 679.6 MiB, 51.3 s (`goldens16.log`). |
| Actual 0.15 golden pipeline | Passed after f80-only legacy dispatch; peak 800.5 MiB, 44.1 s (`goldens15.log`). |
| Final fixture policy | All 46 shell checks passed under both Bash versions with 19 required emitter outputs plus six caller parser outputs (`final-shell-policy.log`). |
| Final integrated regressions | After the final reserved-token merge, the full proof/runtime/parser/input suite, all 25 emitted semantic fixtures, actual 0.15/0.16 exporter round trips, no-sorry, CLI namespace/IO smoke checks and byte-identical checked-AIR regeneration passed. Peak 728.6 MiB, 27.7 s (`integration-final-tokens.log`). |
| Matching-version native 0.15 differential | Passed 85,801 selected cases: 78,304 `ok`, 4,975 matching failures, 1,077 pinned unspecified, zero capped/mismatch, 1,445 host differences. Peak 778.8 MiB, 191.9 s (`diff15.log`). |
| Matching-version native 0.16 differential | Passed 85,861 selected cases: 79,049 `ok`, 4,975 matching failures, 1,077 pinned unspecified, zero capped/mismatch, 760 host differences. Peak 756.1 MiB, 190.8 s (`diff16.log`). |
| Real allocator mutations | Clean lists baseline passed all 1,500 cases. Mutation h produced 414 mismatches; repaired sentinel mutation s changed a pinned count and was detected. Source restoration checked; peak 765.7 MiB, 65.8 s (`mutations-lists.log`). |
| Complete-stack Linux CI | All eight jobs passed at `c19a260`: full 0.15.2/0.16.0 native differential jobs, the 0.14.1 exporter/translation/proof job and all five mutation shards ([run 37159767654](https://github.com/riventic/air2lean/actions/runs/37159767654)). The final reserved-token follow-up is locally checked above; its CI run is tracked on PR 57. Mac host exception lists remain unchanged. |

## Merge reconciliation with current main

Before merging the review PRs, current main `2848b84` also contained PR 46's RwLock
proof and semaphore changes. The complete review stack at `3ffb793` had passed all eight
Linux jobs ([run 37161282164](https://github.com/riventic/air2lean/actions/runs/37161282164));
that run preceded this reconciliation.

Independent GPT-6.1 Sol agents `merge_sync_compat` and `merge_policy_compat` checked
the synchronization API, proof-discovery and documentation interactions. The former
read the entire newly added `Proofs/Sync/RwLock.lean` (4,559 lines before the fix).
This adds one supplemental covered file, making 866 tracked files; the original
838-file ledger remains unchanged.

The RwLock join proof now supplies `Thread.joinValid` from its existing invariant,
without weakening its theorem or the runtime API. `tests/review/AllProofs.lean` now
imports RwLock, bringing the aggregate check to 41 handwritten modules. A separate
static verification confirmed both changes.

Serialized local checks passed all three version-specific full `Proofs` builds
(104 jobs each), all 41 aggregate imports, Darwin Threadsync, all 46 shell checks,
runtime/parser/input regressions, all 25 emitted semantic fixtures, actual 0.15/0.16
exporter round trips and no-sorry. The guarded run peaked at 2,210.7 MiB; generated
proofs and goldens were restored unchanged. The intentional RwLock source fix was
the sole remaining proof diff before commit.
