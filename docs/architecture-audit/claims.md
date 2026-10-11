# Architecture audit 4/6: proof, claim and evidence layer

Scope: Lean proofs over generated code, `Triple`/`TotalTriple`/`Returns`, `tools/Assurance.lean`,
`scripts/assumptions.py`, `scripts/claims.py`, `scripts/project.py coverage|check`,
`scripts/proof-receipt.py`, `scripts/premises.py`, the theorem inventory, the mutation map, the
trust report, the release record and the differential allow-lists.
Base: `origin/main` at `af9ddc30`. Already known and not repeated here: B1 (fqn without module),
float `@divExact` unchecked illegal behavior (`codex/fix-unchecked-illegal`).

Question: can a user be told "verified" (a goal `accepted`, a root at
`functionally_verified_total`/`_partial`) when the claim is false or says nothing about the root?

Answer: yes, through ten independent routes. Each was built as a kernel-extracted fixture and fed
through the shipped tools (no mocked classifier input):

| Fixture theorem | Assurance | `claims.py` | Binding | Coverage level |
|---|---|---|---|---|
| `unchecked_total` (false: `root 255 = pure 0`) | pass, axioms `[]` | total | direct | functionally_verified_total |
| `spoofed_total` (own `Zig.TotalTriple := True`) | pass, axioms `[]` | total | direct | functionally_verified_total |
| `hyp_is_claim` (`h : root x = pure (x+1)` ⊢ same) | pass, axioms `[]` | total | direct | functionally_verified_total |
| `unsat_pre` (`x.toNat > 300` for `x : BitVec 8`) | pass | total | direct | functionally_verified_total |
| `total_false_pre` (`TotalTriple (fun _ => False) spin Q`) | pass | total | direct | functionally_verified_total |
| `ground_instance` (`root 3 = pure 4`, domain "all inputs") | pass, axioms `[]` | total | direct | functionally_verified_total |
| `root_in_post` (triple about `pure ()`, root only in post) | pass | total | direct | functionally_verified_total |
| `root_ignored` (`pure 5 = pure (const 5 (root 255))`) | pass, axioms `[]` | total | direct | functionally_verified_total |
| `spin_partial` (never returns, post `False`) | pass | partial | direct | functionally_verified_partial |
| `asm_divmod_total` (`divl` with divisor 0 traps natively) | pass | total | direct | functionally_verified_total |

`root x = Zig.add false x 1` panics at `x = 255`, and `spin` never returns
(`tests/roadmap/architecture-audit/claims/AuditClaims/Gen.lean`).

Reproduce: `lake build ZigLean ZigLean.Sep.Total AssuranceTools Proofs.Asm.Gen` (through
`scripts/build-guard.py`), then `tests/roadmap/architecture-audit/claims/check.sh`. That script
compiles the fixtures into `.lake/architecture-audit` (not `.lake/build/lib/lean`, where proof
receipts reject untracked oleans) and runs `scripts/assumptions.py --module`, as
`project.py check` does. It then requires the extraction to equal `exposure-report.json` and runs
`test_exposure.py`. That test feeds each entry through `claims.check_goal`,
`project.bind_receipt` and `project.coverage_level`, and pins every verdict as `EXPOSED`. A fix
flips its row. `test_exposure.py --require-fixed` is the gate for a hardening branch.
`kernel-replay.sh` shows the structural fix for S1: the toolchain's `leanchecker` rejects
`unchecked_total` and re-checks the honest fixtures.
`assurance/premises.json` excludes the fixture directory, as it does `tests/roadmap/assurance/`.

## Fix status (soundness batch)

`tests/roadmap/architecture-audit/claims/check.sh --require-fixed=S1,S2,S3,S4,S5,S6,S7,F1,F2,F3,H1`
gates every finding below in CI.

| Finding | Status | Fix |
|---|---|---|
| S1 | fixed | leanchecker kernel replay of every audited module (receipts record it) |
| S2 | fixed | registered claim heads (module + kernel fingerprint, `assurance/claim-heads.json`); the extractor imports them, so a same-named contract fails to load |
| S3 | fixed | hypotheses about generated code or claim heads reject a goal; functional strength needs a non-vacuity witness |
| S4 | fixed | derived domain: a fixed or constrained root argument scopes the claim |
| S5 | fixed | the conclusion's subject must be the root definition |
| S6 | fixed | partial correctness needs a liveness witness (`correct_if_returns`) |
| S7 | fixed | allowlisted asm carries its fault condition (`Zig.asmTrap`, premise ASM-04) |
| F1 | fixed | coverage accepts exactly the receipt schema proof-receipt seals and verifies (3) |
| F2 | fixed | one theorem universe: every indexed theorem file is compiled and audited |
| F3 | fixed | typed host differences; model exclusions pinned per input (SHA-256) |
| F4 | partly | caller obligations (ALC-09, IOM-01) and asm premises are surfaced per goal |
| H1 | fixed | reports and diff summaries are bound to the tree (freshness, `--allow-dirty` recorded) |
| H2 | fixed | batch-8 heads are registered with fingerprints, bounds and the conditional-return claim |
| H3, H4 | open | hardening |

## Ranked findings

Severity order: SOUNDNESS (a false or irrelevant claim reported as verified), then FAIL-OPEN /
EVIDENCE INTEGRITY, then HARDENING.

### S1 — SOUNDNESS, critical: kernel bypass is accepted (confirmed)

`AuditClaims/Unchecked.lean` adds a theorem through `addDecl` with `debug.skipKernelTC` set. The
proof is `True.intro` for the false statement `root 255 = pure 0`. Lean writes it to the olean.
`collectAxioms` reports no axioms, `assumptions.py` passes, and `claims.py` derives
`total_correctness`. `scripts/no-sorry.sh` greps only for `sorry|admit|native_decide`. TRU-01
("the kernel checks the proof") is therefore not enforced: nothing replays the environment. The
same hole is open to any metaprogram in a contract or proof file that bypasses the kernel, such
as a `modifyEnv` that inserts a constant.

Structural fix: kernel replay is part of the audit. Run `leanchecker` (it ships in the pinned
toolchain's `bin/`; `--fresh` also replays imports) on every audited module, or call
`Lean.Environment.replay` in `tools/Assurance.lean`. Record the result per module in the audit and
the receipt. A theorem whose module was not replayed has `allowed = false`. Also reject
`debug.skipKernelTC` and `set_option debug.*` in source, as defense in depth. The probe in
`kernel-replay.sh` takes under a second per fixture module.

### S2 — SOUNDNESS, critical: claim heads are matched by name only and can be spoofed (confirmed)

`claims.py` trusts `Zig.TotalTriple`, `Zig.Triple`, `Zig.TTriple`, `Zig.Returns` and the
`SUCCESS_MONADS` names because "a redefinition elsewhere has a different full name". That holds
only when the real definition is in the same environment. Every `Gen.lean` imports `ZigLean`,
and `ZigLean.lean` does not import `ZigLean.Sep.Total` or `ZigLean.Sep.Triple`
(`import ZigLean; #check @Zig.TotalTriple` gives "Unknown identifier"). `project.py check` audits
only the contract modules (`--module`). A contract can therefore declare
`def Zig.TotalTriple … := True` (`AuditClaims/Shadow.lean`) and get `total_correctness`.
`codex/roadmap-batch8` adds `Zig.TotalTripleWithin` and the `Zig.Conc.Total.*` heads under the
same name-only rule.

Structural fix: a claim head is identified by its declaration, not its name. Pin each head's
defining module and a fingerprint of its kernel type and value (the audit graph has the node), or
require `audit.nodes[head].module` to be in a fixed set. The project audit always imports
`ZigLean.Sep.Total`/`ZigLean.Sep.Triple`/`ZigLean.Conc.Own`, so that a redefinition is a name
clash, and fails if the head node's module is wrong. This is about 5 lines in `claims.classify`,
which already receives `report['nodes']`. It is not applied here because `project.py` calls
`claims.claims_of` without nodes, so both call sites need to change together.

### S3 — SOUNDNESS, high: hypotheses are discarded, so vacuous and circular theorems classify as total (confirmed)

`stripBinders` drops every `∀`/`→`, and neither `claims.py` nor `project.py` inspects the
dropped premises. Three fixtures reach `functionally_verified_total`. In `hyp_is_claim` the claim
is its own hypothesis. In `unsat_pre` the precondition cannot be satisfied. In `total_false_pre`
the triple's precondition is `False`. `docs/claim-strength.md` calls this ordinary Hoare
vacuity, but the user-facing level does not mention it: `contract_domain.review =
declared_not_checked` is the only trace. Shipped proofs routinely carry hypotheses over runtime
state (`Proofs/Pointers/Proofs.lean` `swap_spec`: `hp : m.access p 4 4 = pure …`, and 24 such
binders in `Proofs/`). Nothing distinguishes a satisfiable hypothesis from one that assumes the
result.

Structural fix: a mandatory non-vacuity witness. For each goal, the extractor emits the premise
telescope. The manifest goal must name a companion audited theorem
`∃ args, H₁ args ∧ … ∧ Hₙ args`; for triples, `∃ m hP hF, Disjoint ∧ m.heap = hP ∪ hF ∧ P hP ∧
m.Seq`. Generate it with a `#nonvacuous goal` command, so the companion is the telescope of the
goal itself and not a hand-written lookalike. Also deny by default any hypothesis whose type
mentions a generated definition or a `*.run` of one: `statement_dependencies` minus
`conclusion_dependencies`, intersected with generated nodes, must be empty or listed in the root's
`assumptions`.

### S4 — SOUNDNESS, high: the declared domain is free text; a single ground instance is "fully verified" (confirmed)

`ground_instance : root 3 = pure 4` (proved by `rfl`), declared `total_correctness` with domain
"all inputs", gives `fully_functionally_verified: true`, although `root 255` panics. Nothing
compares `domain` with the theorem's quantifiers.

Structural fix: derive the domain from the kernel type. The extractor records, for the subject
application (S5), which arguments are bound variables of the outer telescope and which are closed
terms. The report shows that machine domain (bound arguments plus their hypotheses) in place of,
or next to, the manifest string. A goal that fixes any root argument to a closed term is capped
at `proved_scoped`.

### S5 — SOUNDNESS, high: binding means "the root occurs anywhere in the conclusion", not "the conclusion is about the root" (confirmed)

`statement_reference` tests `definition in conclusion_dependencies`. `root_in_post` is a
`TotalTriple` about `pure ()` with the root only inside the postcondition.
`root_ignored : (pure 5 : Result Nat) = pure (Function.const _ 5 (root 255))` has the root only
as an ignored argument on the right-hand side. Both bind `direct` and reach
`functionally_verified_total`. The "wrapper or True statement" guard in
`tests/roadmap/coverage-report` only covers conclusions that do not mention the root at all.

Structural fix: bind by position. The extractor emits a `subject`: for `Eq`, the head of the
left-hand side after peeling `StateT.run`/`StateT.run'`/`ExceptT.run`/`Zig.call`; for a triple
head, its computation argument `c` after the same peeling. Binding requires
`subject == definition`. Occurrences elsewhere are reported as `mentions`, not `direct`.

### S6 — SOUNDNESS, medium-high: a program that never returns is "functionally_verified_partial" (confirmed)

`spin_partial : Triple emp spin (fun _ _ => False)` holds because `spin` never returns.
Coverage reports `functionally_verified_partial`, and with it the no-panic absence claim as
proved. The partial meaning is documented (SEM-03), but the level name suggests function, and no
witness shows that the root ever returns. The concurrent counterpart: `Sched.run … fuel` specs,
and the theorem inventory's `all-schedules` scope (32 theorems), count fuel exhaustion as success
(`ZigLean/Conc/Logic.lean`: "No result (out of fuel) is still allowed"). A protocol that spins
forever satisfies them.

Structural fix: a partial level needs a liveness witness. Either an audited `Returns`/exact-success
theorem for some admissible input of the same root, or a typed differential `value_match` for the
root; otherwise cap the root at `safety_only`. Rename the levels `correct_if_returns` and
`functionally_verified_total`. In the inventory, require an `all-schedules` theorem to have an
`EventuallyReturns`/`ReturnsWithin` companion (added on `codex/roadmap-batch8`), or label it
`all-schedules-safety`.

### S7 — SOUNDNESS, high: inline asm is a total pure opaque, so trapping code is provably total (confirmed)

`Proofs/Asm/Gen.lean` models register-only asm as
`opaque airAsm_N : BitVec 32 → BitVec 32 → BitVec 32 × BitVec 32`. That is a total function, so
the model cannot fault. `asm_divmod_total : Asm.divmod a 0 = pure (…)` needs no instruction
hypothesis and classifies `total_correctness`. Natively, `divl` with divisor 0 traps (#DE).
`tests/diff/gen_inputs.zig` excludes `b = 0` because "0 is a CPU fault", so the differential test
cannot refute the claim either. ASM-02 ("instruction behavior as an explicit hypothesis") does
not apply when no hypothesis is needed.

Structural fix: emit asm as a `Zig.Result`-valued opaque (`airAsm_N : … → Result (…)`), so that
success is itself an instruction premise. Alternatively, `claims.py` refuses `no-panic` and
`guaranteed-return` for any goal whose closure contains an `ASM-01` opaque unless the theorem's
hypotheses mention that opaque. The same rule applies to every allowlisted opaque that models an
effect, including `Float.libm`.

### F1 — FAIL-OPEN / INTEGRITY, high: coverage cannot consume a real proof receipt; its tests use a stub (confirmed)

`proof-receipt.py seal` writes `'schema': 2` (F01, `f9384e33`), and its `verify` requires 2.
`project.py load_receipt` requires `schema == 1` (I06, `de86c552`). The two landed in parallel. A
genuine current receipt is therefore always rejected ("not a sealed audited schema-1 receipt").
`tests/roadmap/coverage-report/test_coverage.py` never noticed, because it writes a fake schema-1
receipt and replaces the verifier with a 5-line stub that prints `current`. The failure is
closed today. But the whole receipt-to-coverage path, including every binding check above, has
never run against a real receipt, and a test that passes on fakes would also pass after a
fail-open regression. `codex/roadmap-batch8` changes the check to `schema != 2` (fix pending).

Structural fix: one shared receipt-schema constant imported by both scripts. Add an end-to-end
test that seals a real receipt over a tiny contract module (explicit-modules scope) and runs
`project.py coverage --receipt` with the real `proof-receipt.py verify`.

### F2 — FAIL-OPEN, high: theorems outside `ZigLean/` and `Proofs/` are checked by exit code only; `sorry` passes

`lake env lean F.lean` exits 0 on `declaration uses 'sorry'` (checked: `theorem t : 1 = 2 := by
sorry` exits 0). `scripts/tutorials.py check` (Main/Solution), the CI steps for
`tests/roadmap/vcs/*.lean`, and 15 `tests/roadmap/*` theorem directories whose scripts neither
audit axioms nor grep for `sorry` compile this way. `no-sorry.sh` and `assumptions.py
shipped_modules()` cover only `ZigLean/` and `Proofs/`. Yet `premises.py` indexes `tutorials/`,
`tests/roadmap/` and `case-studies/` theorems in `docs/premise-index.md` as if they were proved.
Exceptions: `flow-time.sh` greps `sorry|axiom`, and a few check.sh scripts `#print axioms`.

Structural fix: one theorem universe. Every module that `premises.py` indexes (`theorem_roots`)
is compiled to an olean and audited by `assumptions.py` (it already accepts `--module`). Tutorial
and roadmap checks fail on any `sorryAx`/non-standard axiom/S1 replay failure, not on the exit
code. `premises.py check` fails for an indexed theorem that is absent from a passing audit.

### F3 — FAIL-OPEN, medium: differential allow-lists mask whole functions and pin counts, not cases (confirmed)

Off Linux x86_64, `host.txt` turns any disagreement of a listed function into `host_difference`.
That includes a model overflow panic against a native value (`test_exposure.py`:
`host-allowlist-masks-panic`). This is the mechanism that hid mutant (d) in `floatops` on macOS.
A model `illegal`/`unspecified` result is an exclusion whatever the native side returned
(`model-illegal-masks-native-value`), and `unspecified.txt`/`capped.txt` pin per-function counts
only. A mutation that moves an exclusion from one input to another, or replaces a value with
`illegal` while removing another exclusion, keeps the count. `project.py` coverage does treat
`host_difference` as a failed `tested` stage, but `diff.sh` exits 0.

Structural fix: type the host allowance. Allow only specific kinds of difference (NaN payload,
sign of zero, f80 padding), each through a value comparator that is itself unit-tested; a
panic/value or error/value disagreement is never `host`. Pin exclusions by `input_sha256` (the
typed report already records it) instead of by count.

### F4 — FAIL-OPEN, medium: premises are neither deny-by-default nor surfaced per goal

Coverage goal rows list only `axioms/opaque_dependencies/extern_dependencies/
compiler_redirections` (`audited_assumptions`). They list no premise IDs. `premises.py` derives
premises from name regexes (`ALC-02` = `allocPolicy\.(maxBytes|…)`, `THR-09` = `Cooperative`)
over a source parse, and over the kernel graph only for shipped theorems
(`compiled --strict` in CI). A project contract (any path in the manifest) is not in
`theorem_roots`. A hand-written model `def` in a contract file has no premise at all. A
hypothesis that constrains an oracle (`m.allocPolicy.fails`, a schedule `o`, a clock) yields a
premise only if its tokens match a regex. The manifest's `assumptions` are compared only with
axioms/opaques/externs (`audit_goal`), not with premises. `DEV-01` (device contracts) is not in
`docs/premises.md`.

Structural fix: deny-by-default premise accounting on the kernel graph. Every node in a goal's
closure is one of three things. It is a standard Lean node. It is a runtime node mapped by
`runtime_modules`. Or it is a non-generated, non-runtime project `def`/`opaque`/hypothesis
binder, which must map to a premise ID or a manifest `assumptions` entry. Otherwise the goal is
`unaccounted`. Emit `premises` in each coverage goal row and in the receipt.

### H1 — HARDENING, medium: `claims.py check` and `--no-build` audits trust their inputs' freshness

`claims.py check --assurance REPORT` classifies any JSON with `status` `pass`. Nothing binds the
report to the current tree (`project.py check` and receipts do). `assumptions.py --no-build`
audits whatever oleans are present. During this audit a copied build contained a stale
`Proofs/Asm/Gen.olean` whose opaque was `airAsm_2482283570`, while the source has
`airAsm_3653072158`. Lean elaborated against the stale olean without complaint.
`proof-receipt.py` records `tracked_dirty` but does not refuse a dirty tree.

Fix: the audit records per-module source and olean hashes and the Lake trace check result.
`claims.py check` requires a receipt (or `project.py check` record) and recomputes those hashes.
Coverage shows `tracked_dirty`.

### H2 — HARDENING, medium: `Exists`, `And` and concurrent heads are fail-closed today, but batch8 widens the trusted head set

`codex/roadmap-batch8` adds `EventuallyReturns`, `ReturnsWithin`, `EventuallyReturnsUnder` and
`TotalTripleWithin` as total heads. These take a fixed initial `m : Mem` argument, so S4 (one
ground memory) and S2/S3/S5 apply to them unchanged. Land S2 and S5 before or together with the
batch8 heads.

### H3 — HARDENING, low-medium: mutation evidence is existence-only on `main`

On `main`, `scripts/mutation-map.py` checks only that designated mutants exist ("does not show
that a mutant is killed"). The kill ledger lives on `codex/roadmap-mutation-kills` and is not
rechecked offline beyond the mutation block hash. A host-dependent kill counts only on Linux
x86_64 (F3).

Fix: merge the ledger. Bind each kill to the hashes of the killed target (module olean or diff
summary `runner_runtime_sources`), not only to the mutation text.

### H4 — HARDENING, low: hypothesis-level opaques and `partial def`

None are exploitable today. `partial def` occurs only in meta code (`Sep/Automation.lean`
`atoms`, policy-listed), and generated recursion uses `partial_fixpoint` (kernel-checked CCPO).
`implemented_by` (`Float.libm`) is policy-listed and not kernel-visible. `native_decide` and
`ofReduceBool` are rejected by policy. Keep the policy, and add the S1 replay so that these
checks rest on the kernel rather than on the elaborator.

## Related unmerged work

- `codex/roadmap-batch8` fixes F1 (`schema != 2`) and binds diff summaries to the current tree in
  `claims.py check` (part of H1, for diffs only). It widens the head set (H2) without S2/S5.
- `codex/roadmap-mutation-kills`: kill ledger (H3); its commit message records the F3 masking of
  mutant (d).
- `codex/roadmap-coverage-evidence` (I06 export links), `codex/roadmap-manifest-receipt` (I07
  provenance), `codex/roadmap-bounded-total` (P05), `codex/roadmap-step-lemmas` (P07),
  `codex/roadmap-counterexamples` (P08): none of them changes theorem binding, classification or
  vacuity. S1 to S7 remain open on all of them.

## Fix order

1. S1 kernel replay and S2 head identity: small changes that close both critical routes.
2. S5 subject binding and S4 machine domain: one extractor change (`subject` plus bound-argument
   map).
3. S3 non-vacuity witnesses and hypothesis deny-by-default; S6 liveness witness and level rename.
4. S7 `Result`-valued asm opaques.
5. F1 shared schema plus a real end-to-end receipt test; F2 one theorem universe; F4 graph
   premises; F3 typed host allowance.
