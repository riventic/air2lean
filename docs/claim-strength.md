# Claim strength from theorem types

`scripts/claims.py` classifies theorems from an assurance report
(`scripts/assumptions.py`, see `docs/assumptions-audit.md`). The extractor in
`tools/Assurance.lean` records each theorem's `conclusion`: the kernel type with binders and
hypotheses stripped. No definition is unfolded, and only an equation's right-hand side is
expanded (through `Option.some` and `Pure.pure`, whose monad is recorded: `pure` in `Option`
can wrap a safety error). Theorem names, comments and manifest labels are not inputs.

| Conclusion head (exact kernel name) | Claims | Derived strength |
|---|---|---|
| `Zig.Triple`, `Zig.TTriple` | no-panic, correct-if-returned | `partial_correctness` |
| `Zig.Returns` | no-panic, guaranteed-return | `safety` |
| `Zig.TotalTriple` | no-panic, correct-if-returned, guaranteed-return | `total_correctness` |
| `Eq` with right side `pure _` in `Zig.Result`, `Zig.MemM`, `Zig.MM` or `Zig.M`, or `some (Except.ok _)` / `pure (Except.ok _)` in `Option` | all three (exact result) | `total_correctness` |
| anything else (`Not`, `And`, `Exists`, `Iff`, wrapper definitions, `Eq` to `ite`/`throw`, `pure` in another monad) | none | none |

Partial triples are false on a safety error but are satisfied by divergence, so they state
no-panic and correct-if-returned only. `Returns` has a trivial postcondition, so it is a
guaranteed-return claim without functional correctness. Zig error-union values are ordinary
returned values. A conjunction is not classified even if its parts would combine into total
correctness, since the parts may concern different programs; state `TotalTriple` instead.

`python3 scripts/claims.py report --assurance REPORT` lists `claims`, `claim_class` (the
strongest claim) and `derived_strength` for every audited theorem.
`python3 scripts/claims.py check MANIFEST --assurance REPORT` checks every project goal
(`docs/project-workflow.md`). A goal is rejected (exit 1) if its theorem name is not an exact
audited theorem, the theorem has assurance violations, the declared strength is
`resource_bound` or `correspondence` (not derivable from these interfaces), or the declared
strength exceeds the derived one in the order `safety < partial_correctness <
total_correctness`. Malformed inputs and reports without conclusion shapes exit 2.

`check --diff SUMMARY` (repeatable) adds differential outcome evidence for each
`example.function` root, classified by the shared [outcome taxonomy](outcome-taxonomy.md).
Every declared strength asserts `no-panic`; `total_correctness` also asserts
`guaranteed-return`. A goal is rejected when its root's evidence includes a capped search,
a fuel-bounded no-result run, an unspecified (including no-clock timer) or unsupported
outcome, or an observed failure the claim denies. Error returns never reject a goal. Evidence
can only reject: an incomplete summary exits 2, and clean evidence adds nothing to the
type-derived strength.

## Vacuity

A diverging program cannot satisfy a `TotalTriple` goal: `TotalTriple` demands an explicit
`c.run m = pure (v, m')` witness for every admissible input. `tests/roadmap/claims/Fixture.lean`
proves `diverge_not_total` and a partial triple for the same diverging program with a false
postcondition; the check rejects a `total_correctness` goal for the latter.
`tests/roadmap/proof-tools/Total.lean` also rejects panics. An unsatisfiable precondition
remains vacuous, as in ordinary Hoare logic: the check does not inspect preconditions or the
manifest's `domain` string.

## Scope

Concurrent total correctness (`Zig.Conc.Total.EventuallyReturns`) is not classified.
Resource-bounded and correspondence claims have no type-derived evidence here. An `Exists`
conclusion is unclassified even when its body states a successful run.

Every derived strength assumes that the native stack does not overflow
([STK-01](premises.md#stk-01)): a theorem about the generated `mem0` sets no stack budget, so
`no-panic` and `guaranteed-return` do not exclude a native stack overflow, which ReleaseSafe
does not check. The premise index lists STK-01 for each theorem that recursion reaches. A
statement that bounds `Mem.stackLimit` itself can exclude `.stackOverflow` for that budget.

## Tests

`python3 tests/roadmap/claims/test_claims.py` runs fast classification and manifest
regressions over `fixture-report.json`, including negative controls for overstated goals,
renamed theorems, wrapper definitions, conjunctions and panicking runs.
`tests/roadmap/claims/check.sh` builds `ZigLean.Sep.Total`, compiles the fixture, extracts its
actual conclusions with `scripts/assumptions.sh`, requires them to match the checked-in report,
and checks an accepted and a rejected manifest end to end.
