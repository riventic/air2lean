# Outcome taxonomy for claims and coverage (V06)

`scripts/outcomes.py` holds one outcome taxonomy, shared by `scripts/claims.py check --diff`
and `scripts/project.py coverage`. It maps the typed differential observations of
[outcome-accounting.md](outcome-accounting.md) (`model_kind`, `status` and `schedule` of each
case row) onto these outcomes. Names agree with the preflight `outcomes` record of
`scripts/project.py`.

| Outcome | Source | Absence claims refused |
| --- | --- | --- |
| `valid` | model `value` without schedule search | none |
| `nondeterministic_valid` | model `value` chosen by a schedule search | none |
| `error_return` | model `error_return` (a Zig `E!T` error is a returned value) | none |
| `panic` | model `model_panic` | `no-panic`, `guaranteed-return` |
| `illegal_behavior` | model `illegal` (illegal behavior that no safety check catches; [illegal-behavior.md](illegal-behavior.md)) | both |
| `unspecified_behavior` | model `unspecified` (Zig leaves the result open) | both |
| `unspecified_timer` | model `unspecified_timer`: `Zig.Error.unsupportedTimer`, a clock or timed wait the model has no semantics for ([TMR-01](premises.md#tmr-01)) | both |
| `deadlock` | model `deadlock` | both |
| `hardware_trap` | model `trap` (an allowlisted inline-asm fault: `Zig.asmTrap`, [ASM-04](premises.md#asm-04)); `trap_match` against a native `SIGFPE` | both |
| `stack_overflow` | model `stack_overflow` (`Zig.Error.stackOverflow`): a frame or a stack block did not fit in the thread's selected stack budget (`Mem.withStack`, [STK-01](premises.md#stk-01)), or a block without an allocator found no room in the address space. The differential runner reports it as `stack_overflow_exclusion`, pinned like `unspecified` | both |
| `divergence` | `bounded_no_result` or a search with a no-result branch: scheduler fuel ran out; divergence is not established | both |
| `search_cap` | a `capped` schedule search | both |
| `unsupported_semantics` | exporter-marked unsupported AIR (coverage), or an unknown model kind | both |

Input and harness failures and native-only kinds are comparison failures, not model outcomes.
A comparison that ends in `search_cap` also counts its model value; a witness beside a
no-result branch counts both `nondeterministic_valid` and `divergence`.

## Absence claims

`no-panic` denies `panic`, `illegal_behavior`, `unspecified_behavior`, `unspecified_timer`,
`deadlock`, `hardware_trap` and
`stack_overflow`, since `Zig.Triple` is false on every `Zig.Error`. `guaranteed-return` also denies
`divergence`. Each claim is also refused by incomplete evidence: `search_cap`, `divergence`,
`unspecified_behavior`, `unspecified_timer` and `unsupported_semantics`. A capped search, a
fuel-bounded run or an unclocked timer therefore never supports a proved absence of a failure.
A refusal reason names each blocking class (`unsupported timer`, `unspecified result`,
`capped schedule search`, ...), so a timer refusal is distinguishable from an unspecified one.

`claims.py check --diff SUMMARY` accepts only evidence bound to the current tree: the
summary's `runner_runtime_sources` must equal the fingerprints `scripts/diff-report.py`
computes for this checkout (runner, harness, `ZigLean`, `Proofs`, examples, toolchain pins;
an added or removed file also counts), and its `cases_sha256` must equal the case file beside
it. Stale, unbound or tampered evidence is an input error (exit 2), never a pass.

Sampled evidence only refuses. Without a theorem a claim is `not_proved`, however clean the
tests. In coverage reports, a refused claim blocks `correct_if_returns` and `functionally_verified_total`. In claim checks,
it rejects the goal. An observed panic is a refusal even if the theorem's precondition
excludes that input: domains are not machine-checked.

`tests/roadmap/outcome-taxonomy/Taxonomy.lean` shows that the contract types already
keep error returns and model failures apart. A partial triple (`FTriple`) holds for an
`Except ErrName` error return and fails, on every admissible input, for `.panic`, `.illegal`,
`.unspecified`, `.unsupportedTimer`, `.deadlock` and `.trap`; divergence and a stack overflow
(`.stackOverflow`, STK-01) satisfy it vacuously. `.unsupportedTimer` is its own `Zig.Error`
constructor: generated `time.Timer.start`/`.read`/`Thread.Futex.timedWait` calls and the
timed scheduler's no-clock, wrong-clock and unselected-timeout paths throw it instead of
`.unspecified`.

## Goal outcome contracts

The taxonomy is also the vocabulary of contracts, not only of reports. Every manifest goal has an
outcome contract: the set of outcomes it admits. Undeclared, a `safety`, `partial_correctness` or
`total_correctness` goal admits `valid`, `nondeterministic_valid` and `error_return` (a returned
error is an admitted outcome of its own, never a model failure); failures are admitted only by
declaration. `resource_bound` and `correspondence` goals claim nothing about failures and admit every
program outcome. A goal may declare
`"outcomes": {"admits": ["valid", "error_return", "panic"]}` to document a function that panics on
bad input, or `["valid"]` to say it never returns an error. The manifest is refused (fail closed) when
a declaration names an unknown or duplicate outcome, is empty, admits an outcome its own strength
rules out (`safety` and `partial_correctness` rule out the failures of `no-panic`;
`total_correctness` adds `divergence`), or admits an incomplete-evidence class (`search_cap`,
`divergence`, `unspecified_behavior`, `unspecified_timer`, `unsupported_semantics`), which are
properties of the evidence or the model, not of a program.

`project.py coverage` judges each goal's contract against the root's outcome counts
(`goals[].outcome_contract`): `refuted` when an outcome it does not admit was observed (a blocker for
`correct_if_returns` and `functionally_verified_total`), `unassessed` when an incomplete class was
observed, `no_evidence` without differential cases, else `not_refuted`. Only direct goals block a
level (other goals already do), and the judged counts are the root function's, not a per-goal slice:
two goals of one root cannot carry opposite contracts about its sampled outcomes. Sampled evidence never proves
a contract, and the contract is separate from correspondence: it neither relies on nor establishes
native agreement.

An explicitly declared `outcomes.admits` is also checked against the audited theorem, without
requiring any samples. `tools/Assurance.lean` records `statement.outcomes` through the plain
helper in `tools/OutcomeContracts.lean`. For the registered full-state heads it partitions the
return type into source error returns and ordinary values, including nested `Option` and
`Except ErrName` wrappers, and reads the postcondition at each constructor class. Conjunctions,
disjunctions, existentials, conditionals and constructor-disjoint equalities give a conservative
upper bound. Resource constraints may narrow a class further; the extractor does not claim
satisfiability. Abstract return types, opaque or unsupported result predicates, and exhausted
inspection limits remain `unsupported` and cannot back an explicit contract. It never infers a
postcondition from the implementation, a theorem name, a comment or sampled runs.

`claims.py check` and receipt-bound coverage report `theorem_outcome_contract`: `verified`
when the declaration equals that bound, `under_claim` when it admits more, and `rejected`
when it omits a permitted outcome or extraction is unsupported/missing. A rejected explicit
contract rejects the claim and prevents a functional coverage level. For example, a total
triple returning `Except ErrName T` with postcondition `fun _ => emp` does not establish
`admits: ["valid"]`, even if the code and every test return `.ok`; a postcondition requiring
`v = .ok x` can establish it. A postcondition requiring `.error "Timeout"` admits only
`error_return`, never `panic`. Exact `Result` equations keep panic, illegal behavior,
unspecified behavior, unsupported timers, deadlock, hardware trap and stack overflow separate.

A partial triple's postcondition is conditional on returning successfully. Its extraction
reports `scope: "conditional_on_return"` and separately lists `divergence` and `stack_overflow`
as `unexcluded`; a liveness witness for one input does not exclude either for all inputs.
An explicit contract omitting these outcomes is rejected. The manifest forbids admitting
divergence because its observation is only bounded evidence, so a partial theorem alone cannot
establish an explicit complete outcome set. Concurrent values also retain
`nondeterministic_valid`, the schedule-search observation class. The implicit defaults keep
their existing meaning relative to the goal strength: they are labelled `strength_default`,
with the extracted return scope and unexcluded outcomes shown, and are never labelled a
theorem-verified complete outcome contract.

## Validation

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/roadmap/outcome-taxonomy -p 'test_*.py'
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/roadmap/coverage-report -p 'test_*.py'
bash tests/roadmap/outcome-taxonomy/check.sh
```

The Python tests include a drift guard: every `Kind` and model `Status` of
`scripts/diff-report.py` must be mapped. Negative controls cover capped, fuel-bounded,
unspecified, unsupported-timer (with its own refusal reason), panic, illegal and deadlock
evidence, and stale, unbound or tampered `--diff` summaries. Error-return evidence is a positive
control that must leave `no-panic` intact.
`Contracts.lean` is compiled and kernel-audited by `check.sh`; its actual conclusion structures
exercise narrower, equal, wider, optional, error-only, opaque, conditional and exact-failure
contracts through the claim gate. Coverage regressions exercise the same gate in receipt
binding, and `outcome-contract-ignores-theorem` must be killed by the no-samples negative test.
