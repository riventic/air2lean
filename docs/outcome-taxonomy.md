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
| `illegal_behavior` | model `illegal` (unchecked undefined behavior) | both |
| `unspecified_behavior` | model `unspecified`, including the no-clock timer path ([TMR-01](premises.md#tmr-01)) | both |
| `deadlock` | model `deadlock` | both |
| `divergence` | `bounded_no_result` or a search with a no-result branch: scheduler fuel ran out; divergence is not established | both |
| `search_cap` | a `capped` schedule search | both |
| `unsupported_semantics` | exporter-marked unsupported AIR (coverage), or an unknown model kind | both |

Input and harness failures and native-only kinds are comparison failures, not model outcomes.
A comparison that ends in `search_cap` also counts its model value; a witness beside a
no-result branch counts both `nondeterministic_valid` and `divergence`.

## Absence claims

`no-panic` denies `panic`, `illegal_behavior`, `unspecified_behavior` and `deadlock`, since
`Zig.Triple` is false on every `Zig.Error`. `guaranteed-return` also denies `divergence`.
Each claim is also refused by incomplete evidence: `search_cap`, `divergence`,
`unspecified_behavior` and `unsupported_semantics`. A capped search, a fuel-bounded run or an
unclocked timer therefore never supports a proved absence of a failure.

Sampled evidence only refuses. Without a theorem a claim is `not_proved`, however clean the
tests. In coverage reports, a refused claim blocks `correct_if_returns` and `functionally_verified_total`. In claim checks,
it rejects the goal. An observed panic is a refusal even if the theorem's precondition
excludes that input: domains are not machine-checked.

`tests/roadmap/outcome-taxonomy/Taxonomy.lean` shows that the contract types already
keep error returns and model failures apart. A partial triple holds for an `Except ErrName`
error return and fails for `.panic`, `.illegal`, `.unspecified` and `.deadlock`; divergence
satisfies it vacuously. No Lean definitions changed.

## Validation

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/outcome-taxonomy/test_taxonomy.py
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/roadmap/coverage-report -p 'test_*.py'
lake build ZigLean.Sep.Triple && lake env lean tests/roadmap/outcome-taxonomy/Taxonomy.lean
```

The Python tests include a drift guard: every `Kind` and model `Status` of
`scripts/diff-report.py` must be mapped. Negative controls cover capped, fuel-bounded,
unspecified/timer, panic, illegal and deadlock evidence. Error-return evidence is a positive
control that must leave `no-panic` intact.
