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
the emission driver preserves the six parser fixtures, adds 15 emitter fixtures, and
elaborates all 21 generated files serially without nested compiler launches. CI invokes it
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

Linux CI reruns remain pending. An earlier PR 50 run lacked PR 48's `target_endian`
normalization dependency; its base and head ancestry now include that dependency. Local
passes do not imply a completed Linux CI run.

## Supplemental coverage for added files

The baseline ledger remains 838 files. The baseline-to-integration `HEAD` added-file
inventory (`git diff --diff-filter=A --name-only BASELINE HEAD`) contains these 27 files.
Every added path has an owner and final-review assignment; none is uncovered. Assignments
record review scope separately from the completed local checks and pending Linux CI.

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
