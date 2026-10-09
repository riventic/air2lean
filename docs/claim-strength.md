# Claim strength from theorem types

`scripts/claims.py` classifies theorems from an assurance report
(`scripts/assumptions.py`, see `docs/assumptions-audit.md`). The extractor in
`tools/Assurance.lean` records, from each theorem's kernel type and nothing else:

* `conclusion`: the conclusion shape with binders and hypotheses stripped. No definition is
  unfolded, and only an equation's right-hand side is expanded (through `Option.some` and
  `Pure.pure`, whose monad is recorded: `pure` in `Option` can wrap a safety error);
* `statement`: the binder telescope (name, binder kind, whether it is a hypothesis, the
  computational definitions it mentions, the earlier binders it uses); the conclusion head as a
  declaration (defining module and a 128-bit fingerprint of its kernel type and value); for each
  head argument, the computation it runs (runners such as `StateT.run`, `StateT.run'`,
  `ExceptT.run` and `Zig.call` are peeled; the applied constant, its parameter kinds and each
  argument as a bound variable of the telescope, a closed term or an open term); and the status
  of the companion witnesses below.

Theorem names, comments and manifest labels are not inputs.

## Heads

A conclusion head counts only as a registered declaration. `assurance/claim-heads.json` lists
each head with its defining module, fingerprint, claims, and the argument positions of the
computation and of its initial state. `tools/Assurance.lean` imports every listed module, so a
contract that declares a same-named head fails to load next to it (name clash); a head that the
audit does not import (for example a head registered by a later branch) is still rejected when
its module or fingerprint differs. `python3 scripts/claims.py heads --assurance REPORT` prints
the declarations seen, for adding a head; `tests/roadmap/claims/check.sh` requires the registry
to match the extracted declarations.

| Conclusion head | Claims | Type-derived strength |
|---|---|---|
| `Zig.Triple`, `Zig.TTriple` | no-panic, correct-if-returned | `partial_correctness` |
| `Zig.Returns` | no-panic, guaranteed-return | `safety` |
| `Zig.TotalTriple` | no-panic, correct-if-returned, guaranteed-return | `total_correctness` |
| `Zig.TotalTripleWithin` (bound: `loop_body_runs`) | no-panic, correct-if-returned, guaranteed-return | `total_correctness` |
| `Zig.Conc.Total.EventuallyReturns` | no-panic, correct-if-returned, guaranteed-return | `total_correctness` |
| `Zig.Conc.Total.ReturnsWithin` (bound: `scheduler_turns`) | no-panic, correct-if-returned, guaranteed-return | `total_correctness` |
| `Zig.Conc.Total.EventuallyReturnsUnder` | guaranteed-return-under-premise | none |
| `Eq` with right side `pure _` in `Zig.Result`, `Zig.MemM`, `Zig.MM` or `Zig.M`, or `some (Except.ok _)` / `pure (Except.ok _)` in `Option` | all three (exact result) | `total_correctness` |
| anything else (`Not`, `And`, `Exists`, `Iff`, wrapper definitions, unregistered heads, `Eq` to `ite`/`throw`, `pure` in another monad) | none | none |

Partial triples are false on a safety error but are satisfied by divergence, so they state
no-panic and correct-if-returned only. `Returns` has a trivial postcondition, so it is a
guaranteed-return claim without functional correctness. Zig error-union values are ordinary
returned values. The concurrent heads quantify over every scheduling oracle inside their
definitions. `EventuallyReturnsUnder Fair` covers only the oracles satisfying the premise
`Fair` stated in its conclusion. Other schedules are unconstrained, and an unsatisfiable
premise makes it vacuous (`Zig.Conc.Total.under_false`). Its claim
`guaranteed-return-under-premise` therefore implies none of the three unconditional claims,
and every declared strength is rejected for it with a reason naming the premise. Bounded
heads report a `bound` object with the unit of the bound (`loop_body_runs`: `LoopRuns` body
runs; `scheduler_turns`: scheduler fuel). Other theorems report `bound: null`. The bound's
value is in the theorem statement and is not extracted. A conjunction is not classified even if its parts would combine into total
correctness, since the parts may concern different programs; state `TotalTriple` instead.

## Witnesses

A theorem `T : ∀ xs, H xs → C xs` is vacuous when its premises cannot be met, and a partial
triple says nothing about a program that never returns. `ZigLean/Witness.lean` computes two
companion statements from `T`'s kernel type; the premise telescope is `T`'s binders followed by
the binders of its conclusion head unfolded once (for a triple: `m`, `hP`, `hF`, disjointness,
the heap split, `P hP`, `m.Seq`):

* `nonvacuity_witness T := proof` adds `T.nonvacuous : ∃ telescope, True`;
* `liveness_witness T := proof` adds `T.returns : ∃ telescope, ∃ r, d = some (.ok r)`, where
  `d` is the result the unfolded partial head matches on (`(c.run m).run`).

The extractor recomputes both statements and reports a companion `verified` only if its kernel
type is exactly that statement (`mismatch` otherwise); `claims.py` also requires the companion
to be an allowed theorem of the same audit. A telescope without hypotheses whose binder types
all have `Nonempty` instances is `trivial` (no companion needed). `ZigLean/Sep/Witness.lean`
provides an admissible memory (`{}` with `Mem.seq_default`, `Mem.heap_default_split`).

The companions of the shipped theorems are concrete: arguments, a memory that satisfies the
precondition (`Witness.mem1 bs`, one block holding `bs`, and `Witness.mem2`, in
`ZigLean/Mem/Witness.lean`; `Witness.Admit`/`Witness.Live` and their thread-triple versions
`TAdmit`/`TLive` in `ZigLean/Sep/Witness.lean` and `ZigLean/Conc/Witness.lean`), and for a
partial triple a run that the kernel evaluates (`ok_of_okb (by decide +kernel)`) or that a
total triple of the same program gives (`Live.of_total`). `Zig.loop` is a `partial_fixpoint`,
which the kernel does not unfold, so a loop's run comes from a total triple or an input that
skips the loop. A `Proofs/` theorem has its companions next to it; the library lemmas of
`ZigLean/` have theirs in `ZigLean/Witnesses/*.lean`, since modules that generated code imports
must not import the witness commands. A premise about an `opaque` function (the assembly
theorems of `Proofs/Asm/Proofs.lean`) has no companion: the kernel cannot evaluate it, so those
theorems stay at `safety`.

The strength after caps (`derived_strength`) is the type-derived strength, reduced to `safety`
when a partial or total claim has no non-vacuity witness, or a partial claim has no liveness
witness; `caps` lists why.

## Goals

`python3 scripts/claims.py report --assurance REPORT` lists `claims`, `claim_class` (the
strongest claim), `type_strength`, `derived_strength`, `bound`, `subject`, `witnesses` and
`caps` for every audited theorem, and `premises`: what a claim rests on beyond its type (a
theorem whose closure contains an inline-asm opaque carries [ASM-01](premises.md#asm-01), and a
no-panic or guaranteed-return claim over one also [ASM-04](premises.md#asm-04), the allowlist
fault conditions, S7). `python3 scripts/claims.py check MANIFEST --assurance REPORT` checks
every project goal (`docs/project-workflow.md`) against its root's generated definition
`namespace.(function without prefix)`. A goal is rejected (exit 1) when:

* its theorem name is not an exact audited theorem, the theorem has assurance violations, or
  the report lacks the theorem's closure (`opaque_dependencies`);
* the declared strength is `resource_bound` or `correspondence` (not derivable from these
  interfaces), or exceeds the derived strength in the order `safety < partial_correctness <
  total_correctness`, or the theorem only guarantees a return under a schedule premise
  (`guaranteed-return-under-premise`, rejected for every declared strength);
* the conclusion head is a same-named declaration other than the registered one;
* the conclusion is not about the root: the computation at the head's program position (an
  equation's left side) is not the root definition. A root that appears only in a
  postcondition, a hypothesis or an ignored argument does not bind;
* a hypothesis mentions a generated definition (any definition of the root's generated module)
  or a claim head, unless that definition is one of the root's declared `assumptions`;
* the derived domain is scoped and the declared domain does not start with `scoped`.

The domain is derived from the subject: each explicit root argument and initial state is
reported as the quantified variable it is, or `fixed`. It is `universal` only when every one is
a distinct quantified variable, no hypothesis uses one of them, and the premises are witnessed
non-vacuous; a ground instance (`root 3 = pure 4`), a fixed initial memory, a repeated variable
or a hypothesis such as `0 < v` makes it `scoped`. `project.py coverage` caps a scoped root at
`proved_scoped`. A triple's precondition is the contract's stated precondition: it is witnessed
non-vacuous but does not scope the domain. Malformed inputs and reports without conclusion or
statement structures exit 2.

`check --diff SUMMARY` (repeatable) adds differential outcome evidence for each
`example.function` root, classified by the shared [outcome taxonomy](outcome-taxonomy.md).
Every declared strength asserts `no-panic`; `total_correctness` also asserts
`guaranteed-return`. A goal is rejected when its root's evidence includes a capped search,
a fuel-bounded no-result run, an unspecified result, an unsupported timer (`unspecified_timer`,
reason `unsupported timer`), an unsupported outcome, or an observed failure the claim denies.
Error returns never reject a goal. Evidence can only reject: an incomplete summary exits 2, and
clean evidence adds nothing to the type-derived strength. Each summary must be bound to the
current tree: its `runner_runtime_sources` must equal the fingerprints `scripts/diff-report.py`
computes now and its `cases_sha256` the case file beside it; stale or unbound evidence exits 2.

## Vacuity

A diverging program cannot satisfy a `TotalTriple` or `TotalTripleWithin` goal: `TotalTriple` demands an explicit
`c.run m = pure (v, m')` witness for every admissible input. `tests/roadmap/claims/Fixture.lean`
proves `diverge_not_total` and a partial triple for the same diverging program with a false
postcondition; without a liveness witness that triple derives only `safety`. `spin_not_within`
refutes every bound for a loop that never exits, and `stuck_not_total` refutes
`EventuallyReturns` for a concurrent program that never returns. `stuck_under_false` proves
`EventuallyReturnsUnder` with an unsatisfiable premise for that same program, and the check
rejects every goal for it.
`tests/roadmap/proof-tools/Total.lean` also rejects panics. An unsatisfiable precondition or
hypothesis has no non-vacuity witness, so it caps the claim at `safety`.

## Scope

A schedule premise stated as a theorem hypothesis over all oracles (such as `∀ o, Fair o`)
is a hypothesis: without a non-vacuity witness it caps the claim at `safety`, and with one it
scopes the derived domain; it is false in the model whenever some legal oracle violates it.
State conditional termination with `EventuallyReturnsUnder` instead. The concurrent heads fix
the initial memory, so their derived domain is scoped (`scoped: ...` must be declared). The
`resource_bound` and `correspondence` manifest strengths remain non-derivable. A bounded head
reports its unit, but the bound's value is not checked against a manifest. An `Exists`
conclusion is unclassified even when its body states a successful run.

## Tests

`python3 tests/roadmap/claims/test_claims.py` runs fast classification, binding, domain,
hypothesis, witness and manifest regressions over `fixture-report.json`, including negative
controls for overstated goals, renamed theorems, spoofed heads, wrapper definitions,
conjunctions and panicking runs. `tests/roadmap/claims/check.sh` builds the fixture's imports,
compiles it, extracts its statements with `scripts/assumptions.sh`, requires them and the head
registry to match, and checks an accepted and a rejected manifest end to end.
`tests/roadmap/architecture-audit/claims/check.sh --require-fixed=S2,S3,S4,S5,S6` replays the
architecture-audit counterexamples through `claims.py` and `project.py coverage`.
