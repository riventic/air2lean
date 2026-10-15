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

The legacy judgments' heads are **reserved names** (`reserved` in the registry): `Zig.Triple`,
`Zig.TTriple`, `Zig.TotalTriple`, `Zig.Returns`, `Zig.TotalTripleWithin` and
`Zig.Conc.Total.{EventuallyReturns, ReturnsWithin, EventuallyReturnsUnder}`. The audit does
not import their modules, so a contract may declare one without a name clash. `claims.py`
rejects every theorem that concludes in a reserved name, whatever its module and fingerprint,
and a hypothesis that mentions one is rejected like one that mentions a registered head. A
reserved name is never registered again. `tests/roadmap/claims/Fixture.lean` declares spoofs of
the three `Zig.Conc.Total` names as negative fixtures. The other reserved names are checked on
extracted statements in `test_claims.py`.

| Conclusion head | Claims | Type-derived strength |
|---|---|---|
| `Zig.Full.FTriple`, `Zig.Full.CTriple`, `Zig.Full.FTTriple` | no-panic, correct-if-returned | `partial_correctness` |
| `Zig.Full.FTotalTriple`, `Zig.Full.FTTotalTriple` | no-panic, correct-if-returned, guaranteed-return | `total_correctness` |
| a reserved name | none (rejected, with a reason naming the reserved head) | none |
| `Eq` with right side `pure _` in `Zig.Result`, `Zig.MemM`, `Zig.MM` or `Zig.M`, or `some (Except.ok _)` / `pure (Except.ok _)` in `Option` | all three (exact result) | `total_correctness` |
| anything else (`Not`, `And`, `Exists`, `Iff`, wrapper definitions, unregistered heads, `Eq` to `ite`/`throw`, `pure` in another monad) | none | none |

`Zig.Full.CTriple` reads its concurrent function in the caller's thread. That reading answers
only solo stops (`yield`, a `choose`, an atomic op's `pick`); a stop at a spawn, join, futex wait
or wake, gate or async choice fails closed (`.illegal`), so a `CTriple` holds only if no run
from a state that meets its precondition reaches such a stop, and its claims are those of
`FTriple` (`tests/roadmap/sep-full/SoloSpawnCX.lean`; audit `structure-2026-10-13.md` #1).

Partial triples are false on a safety error but are satisfied by divergence, so they state
no-panic and correct-if-returned only. Zig error-union values are ordinary returned values. A
conjunction is not classified even if its parts would combine into total correctness, since the
parts may concern different programs; state `FTotalTriple` instead.

The registry keeps two mechanisms that no registered head uses today; the tests exercise them
through the fixture's spoofs, registered in a test-only registry. A head whose claim is
`guaranteed-return-under-premise` (a return only for the schedules that satisfy a premise stated
in its conclusion) implies none of the three unconditional claims, so every declared strength is
rejected for it with a reason naming the premise. A head with a `bound` (unit `loop_body_runs`
or `scheduler_turns`, argument `bound_arg`) reports a `bound` object with the unit and, from the
extracted argument, its closed value or printed form. Other theorems report `bound: null`.

## Witnesses

A theorem `T : ∀ xs, H xs → C xs` is vacuous when its premises cannot be met, and a partial
triple says nothing about a program that never returns. `ZigLean/Witness.lean` computes the
companion statements from `T`'s kernel type; the premise telescope is `T`'s binders followed by
the binders of its conclusion head unfolded once (for a triple: `m`, `hP`, `hF`, disjointness,
the heap split, `P hP`, `m.Seq`). When the unfolded head is itself a judgment (a definition that
unfolds to a `∀`), or a conjunction whose left half is one, its binders follow too: a total
full-state triple `FTotalTriple P c Q = FTriple P c Q ∧ FReturns P c` and a concurrent one
`CTriple P x Q = ∀ n, FTriple P (soloRun n x) Q` have the full-state triple's premises (`m`, `r`,
`rF`, `Holds m r rF`, `P r`, `m.FSeq`), so an unsatisfiable precondition is not trivially
inhabited. A total head's other half states the return, so it has no liveness obligation:

* `nonvacuity_witness T := proof` adds `T.nonvacuous : ∃ telescope, True`;
* `liveness_witness T := proof` adds `T.returns : ∃ telescope, ∃ r, d = some (.ok r)`, where
  `d` is the result the unfolded partial head matches on (`(c.run m).run`);
* `reachability_witness T := proof` adds `T.reachable : ∃ σ, ∃ telescope, True` with the
  telescope's memory binder replaced by `N.mem0 σ`, where `N.f` is the first constant of the
  conclusion whose namespace defines `mem0` (a generated module's memory at program start). It
  exists only for a claim that names such a start memory and has a memory premise; otherwise the
  extractor reports it `not_required`.

The extractor recomputes the statements and reports a companion `verified` only if its kernel
type is exactly that statement (`mismatch` otherwise); `claims.py` also requires the companion
to be an allowed theorem of the same audit. A telescope without hypotheses whose binder types
all have `Nonempty` instances is `trivial` (no companion needed). `ZigLean/Sep/Witness.lean`
provides an admissible memory (`{}` with `Mem.seq_default`, `Mem.heap_default_split`).

The companions of the shipped theorems are concrete: arguments, a memory that satisfies the
precondition (`Witness.mem1 bs`, one block holding `bs`, and `Witness.mem2`, in
`ZigLean/Mem/Witness.lean`; `Witness.Admit`/`Witness.Live` and their thread-triple versions
`TAdmit`/`TLive` in `ZigLean/Sep/Witness.lean` and `ZigLean/Conc/Witness.lean`; for the
full-state heads `FAdmit`/`FLive`, `CAdmit`/`CLive` and `FTTAdmit`/`FTTLive` in
`ZigLean/Sep/Full/Witness.lean`, over `Mem.FSeq` memories such as `fseq_default` and
`mem1_fseq`), and for a
partial triple a run that the kernel evaluates (`ok_of_okb (by decide +kernel)`) or that a
total triple of the same program gives (`Live.of_total`). `Zig.loop` is a `partial_fixpoint`,
which the kernel does not unfold, so a loop's run comes from a total triple or an input that
skips the loop (a run of the scheduler can cut each loop instead: `unroll_sched`,
[proof-tools.md](proof-tools.md#concrete-runs-of-programs-with-loops-unroll_sched)). A `Proofs/` theorem has its companions next to it; the library lemmas of
`ZigLean/` have theirs in `ZigLean/Witnesses/*.lean`, since modules that generated code imports
must not import the witness commands. A premise about an `opaque` function (the assembly
theorems of `Proofs/Asm/Proofs.lean`) has no companion: the kernel cannot evaluate it, so those
theorems support no claim.

A precondition over an allocator's invariant holds ghost state (extent shares, byte-range claims,
the vtable's knowledge) that only updates create. `ZigLean/Sep/Full/WitnessStart.lean` shows it
admissible in the memory at program start: `FAdmit.init_claims` (the globals with the claim on
every global's bytes), carried by updates that keep the memory (`FAdmit.eupd`), with leftovers in
the frame (`FAdmit.frame`). A theorem whose premise is an allocator contract (`CAllocSpec` of
the environment) gets its companion from a proved allocator through
`CAllocSpec.env_ofRaw` (`docs/interfaces.md`). `tests/roadmap/lists-fba` does both for
`Lists.Append.append_spec`, `Lists.Alloc.push_spec` and `Lists.Alloc.freeAll_spec` with the translated
`FixedBufferAllocator`; the companions live in that fixture (the allocator's translation is a
test fixture), so its `check.sh` runs the extractor over the proof modules and the fixture and
requires `verified`. The audit of the shipped modules alone (`scripts/assumptions.py` without
`--module`) does not load the fixture and reports those companions `absent`.

**No witness, no claim.** A theorem whose non-vacuity witness is not `verified` or `trivial`
derives no strength (`derived_strength: null`), whatever its head: unsatisfiable premises make
it prove nothing, so it cannot back `safety` or `no-panic` either (audit
[soundness-2026-10-14](architecture-audit/soundness-2026-10-14.md) S1). `project.py coverage`
binds such a goal as `unwitnessed`, never `direct`, so it backs no level and no absence claim.
A partial claim whose premises are witnessed but which has no liveness witness is reduced to
`safety`. `caps` lists why.

**Entry points start at `mem0`.** A manifest goal is a claim about an entry-point root, so its
premises must hold where the program starts, not only in some memory (audit F3). `claims.py
check_goal` rejects a goal, and `project.py coverage` binds it `unwitnessed`, unless its
reachability companion is `verified` or `trivial` (or `not_required`: the claim names no start
memory or no memory, as for a pure function's equation). A library function's theorem keeps the
non-vacuity witness: it may be called in any memory that satisfies its premises. An allocator
implementation is tied to the program through its creation triple and that triple's `FAdmit`
companion ([invariant-synthesis.md](invariant-synthesis.md), maintainer decision 2026-10-15), not
through this companion.

## Goals

`python3 scripts/claims.py report --assurance REPORT` lists `claims`, `claim_class` (the
strongest claim), `type_strength`, `derived_strength`, `bound`, `subject`, `witnesses` and
`caps` for every audited theorem, and `premises`: what a claim rests on beyond its type (a
theorem whose closure contains an inline-asm opaque carries [ASM-01](premises.md#asm-01), and a
no-panic or guaranteed-return claim over one also [ASM-04](premises.md#asm-04), the allowlist
fault conditions, S7; a theorem whose closure reaches the scheduler or the atomics model, by the
audit's per-theorem `runtime_modules`, carries [ORD-06](premises.md#ord-06), the memory-model
adequacy premise, C12). An audit without `runtime_modules`, or with a runtime module that has no
premise mapping, leaves `premises` null and rejects the goal. `python3 scripts/claims.py check MANIFEST --assurance REPORT` checks
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

An explicit `outcomes.admits` is checked against the audited kernel postcondition's constructor
upper bound, independently of tests. A narrower or unsupported contract rejects the goal;
a wider contract is reported as `under_claim`. Partial postconditions keep divergence and
stack overflow unexcluded and cannot establish an explicit complete outcome set. Implicit
defaults remain labelled `strength_default` and follow the declared strength, including its
conditional-on-return meaning. See [outcome-taxonomy.md](outcome-taxonomy.md#goal-outcome-contracts).

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

A diverging program cannot satisfy an `FTotalTriple` goal: its `FReturns` half demands a
successful run for every admissible input. `tests/roadmap/claims/Fixture.lean` proves
`fdiverge_not_total` and a partial triple for the same diverging program with a false
postcondition; without a liveness witness that triple derives only `safety`. `ffalse_total`
holds for the diverging program under an unsatisfiable precondition and, without a non-vacuity
witness, supports no claim.
`tests/roadmap/sep-auto/Total.lean` also rejects panics (`panic_not_partial`). An unsatisfiable precondition or
hypothesis has no non-vacuity witness, so the theorem supports no claim.

## Scope

A schedule premise stated as a theorem hypothesis over all oracles (such as `∀ o, Fair o`)
is a hypothesis: without a non-vacuity witness the theorem supports no claim, and with one it
scopes the derived domain; it is false in the model whenever some legal oracle violates it. A
fixed initial memory in the conclusion also scopes the derived domain (`scoped: ...` must be
declared). The `resource_bound` and `correspondence` manifest strengths remain non-derivable.
An `Exists`
conclusion is unclassified even when its body states a successful run.

Every derived strength assumes that the native stack does not overflow
([STK-01](premises.md#stk-01)): a theorem about the generated `mem0` sets no stack budget, so
`no-panic` and `guaranteed-return` do not exclude a native stack overflow, which ReleaseSafe
does not check. The premise index lists STK-01 for each theorem that recursion reaches. A
statement over a memory with a stack budget (`Mem.withStack`, MM-18) can exclude `.stackOverflow`
for that budget (premise STK-01 in its budgeted form, STK-02).

## Tests

`python3 tests/roadmap/claims/test_claims.py` runs fast classification, binding, domain,
hypothesis, witness and manifest regressions over `fixture-report.json`, including negative
controls for overstated goals, renamed theorems, spoofed heads, wrapper definitions,
conjunctions and panicking runs. `tests/roadmap/claims/check.sh` builds the fixture's imports,
compiles it, extracts its statements with `scripts/assumptions.sh`, requires them and the head
registry to match, and checks an accepted and a rejected manifest end to end.
`tests/roadmap/architecture-audit/claims/check.sh --require-fixed=S2,S3,S4,S5,S6` replays the
architecture-audit counterexamples through `claims.py` and `project.py coverage`.
