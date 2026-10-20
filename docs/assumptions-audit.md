# Theorem dependency and assumption audit

Run `scripts/assumptions.sh` after selecting the intended generated program/profile. The
command builds every `.lean` module under `ZigLean/` and `Proofs/`, plus `ZigLean.lean`,
then imports them into Lean and inspects the **checked environment**. It discovers theorem
names from `ConstantInfo.thmInfo`, including private and generated theorems, rather than
matching theorem declarations in source text. It fails if no checked theorem is found.

The default report is `.lake/assurance/assumptions.json`. Use `--output <path>` to retain a
release artifact. Exit codes are 0 for an allowed report, 1 for a policy violation, and 2
for a build, extraction, or policy error. Errors replace an old successful report with an
error report; they do not leave stale success evidence at that output path.

`scripts/no-sorry.sh` remains a separate source-level gate. Run all three:

```sh
scripts/no-sorry.sh
scripts/assumptions.sh --output .lake/assurance/assumptions.json
python3 scripts/theorem_universe.py audit --output-dir .lake/theorem-universe \
  --shipped .lake/assurance/assumptions.json
tests/roadmap/assurance/check.sh
```

## Kernel replay (S1)

An elaborator option such as `debug.skipKernelTC` (or a metaprogram that edits the
environment) writes declarations the kernel never checked into the olean, and
`collectAxioms` then reports nothing. The audit therefore replays every module of the
audited dependency closure that does not ship with the toolchain (`Init`, `Std`, `Lean`,
`Lake`) through the pinned toolchain's own `leanchecker`, and records the result as
`kernel_replay` (tool and `lean` SHA-256, `lean-toolchain`, the replayed module list and its
digest, rejections). A declaration in a rejected module is `kernel-replay-rejected`, one in a
module outside the replayed set is `kernel-replay-missing`; either fails the report. A toolchain
module shadowed by a project olean is an error. Proof receipts require a passing, uncached replay
by the planned toolchain's `leanchecker` and copy its summary into `receipt.json`; receipts
without it are not current. Replaying the shipped scope takes about 40 s on 8 cores (about
280 s of CPU; `AIR2LEAN_REPLAY_JOBS` sets the parallelism, default `min(4, cores)`).
`--replay-cache FILE` lets the theorem-universe run skip modules whose olean bytes passed
earlier in the same build; the architecture-audit fixtures' four audits
(`tests/roadmap/architecture-audit/claims/build.sh`) share one file per run in the same way, and
so do the `theorem_universe.py gate --replay-cache` calls of a gate script (a fresh file in its
temporary directory; no gate caches by default).
Receipts reject reused replays.

Existing replay-cache hits also require the current installed runtime/logical/IR input digest
from `toolchain_runtime_sha256`, the same byte traversal the extractor uses. Missing or changed
cache bindings trigger fresh replay. The digest is recomputed after the replay batch, before a
cache record or successful result is published. Extraction's recorded runtime must match at
replay entry. This tightens existing admission; it does not expand the cacheable module set or
authenticate complete project/private import closures.

`no-sorry.sh` (`theorem_universe.py scan`) also rejects `debug.skipKernelTC` and
`set_option debug.*` anywhere in the theorem universe, and environment edits, `unsafe`,
`extern` and `implemented_by` outside the reviewed counts in `assurance/kernel-escapes.json`.

## One theorem universe (F2)

`scripts/theorem_universe.py` defines the theorem universe once: the shipped `ZigLean/` and
`Proofs/` modules plus every module `docs/premise-index.md` indexes (`premises.theorem_files`:
tutorials, case studies, `tests/roadmap` theorem directories). Lean exits 0 on
`declaration uses 'sorry'`, so `audit` compiles each indexed module outside the Lake targets
to an olean under `--output-dir`, fails on any `sorry` warning (examples never reach an olean),
and runs this audit (axiom policy, `sorryAx`, kernel replay) over all of them, packing modules
that do not share declaration names into one extractor run. `--shipped REPORT` also requires a
passing, replayed all-shipped-modules report. A file that imports a module generated at gate
time is listed in `GATES`; its gate script runs `theorem_universe.py gate` on its copy. `lake env` searches
`.lake/build/lib/lean` before the universe libraries, so the audit refuses to run while a
non-Lake top-level name there (the `tests/` fixture oleans of `tests/roadmap/claims` and
`tests/roadmap/assurance`) could shadow a universe module; CI removes that directory first.

## Freshness (H1)

Each report records `freshness`: the Git revision and whether tracked files were dirty, the
SHA-256 of every replayed module's olean (and of its source for Lake modules), and Lake's trace
check (`lake --rehash build --no-build` over the Lake-built modules, also under `--no-build`, so
a stale olean fails the audit). `claims.py check` recomputes these digests and refuses a report
from another revision, a changed artifact, or a dirty report or tree unless `--allow-dirty` is
given (recorded in its output). `proof-receipt.py prepare` refuses a dirty tree unless
`--allow-dirty` (`AIR2LEAN_RECEIPT_ALLOW_DIRTY=1` for `tests/roadmap/proof-receipts/check.sh`);
the receipt records `tree.dirty_allowed`.

Freshness also records the canonical `lean_sysroot` and `toolchain_runtime_sha256` connected to
the extractor's existing runtime identity. Verification requires matching extractor/freshness
bindings, resolves the current sysroot through the existing `lake env printenv` path and
freshly hashes its installed inputs. A different selected root is rejected even while the old
bound installation still exists. Sysroot resolution does not request a build.
Missing bindings require a new audit; changing only an installed standard module, IR/signature
or shared library makes a report stale even if every recorded project artifact stays fixed.
This does not establish external source/compiler correspondence or registered-witness closure.

The regression command compiles intentionally untrusted fixtures outside the shipped
source scope. It checks that a clean wrapper importing a hidden `sorry` fails, a new
project axiom fails, an unlisted ordinary opaque fails, a runtime redirection fails, and
a compiler-dependent native proof fails, and an unlisted extern-backed ordinary definition
fails. The same extern definition passes only with its exact reviewed backend/symbol contract.
The positive fixture verifies standard classical reasoning and an allowlisted opaque
with a kernel-checked value. The fast policy tests also check unused project axioms,
incomplete graphs, and compiler proof axioms.

## What the gate checks

`tools/Assurance.lean`, built as the separate `AssuranceTools` Lake library, walks the constants occurring in each theorem's type and proof,
then transitively walks referenced declaration types and bodies. Inductive constructors
and recursor rules are included. All project axioms, opaques, and compiler redirections
are also inspected even if no shipped theorem references them. Dependencies are read
from imported compiled declarations, so moving a bad proof into an imported module does
not avoid the audit.

Lean 4.34's `collectAxioms` supplies a second, transitive axiom inventory for each theorem.
It uses the axiom dependency summaries recorded during module compilation. Every reported
axiom is checked against the same policy, including one hidden behind an imported theorem.
An unresolved declaration or an axiom inventory inconsistent with the extracted graph
fails closed.

`assurance/policy.json` is the reviewed allowlist. Its three standard logical axioms are
exactly `propext`, `Classical.choice`, and `Quot.sound`. `sorryAx`, `Lean.ofReduce*`, and the generated
`..._native.<tactic>.ax_*` compiler proof axioms cannot be allowlisted. The current project axiom allowlist is empty.
Project opaque, runtime-redirection, and extern entries identify both the defining module and
user name, with an explicit reason. Private declarations use their user names for these
keys; the actual kernel name remains in the report. Runtime replacement targets and the
two macro-generated simp-extension handles use exact compiled identities under the
pinned Lean release, as does the label-extension handle of `vc_contract`. A changed private
counter or hygienic name fails until reviewed.

The current allowed project opaques are `Zig.Float.libm`, and the individual private extern primitives used by its executable
libm implementation, plus the `SimpExtension` and `SimprocExtension` handles generated
by `register_simp_attr zig_unfold` in `ZigLean/SimpAttr.lean`. Lean's
`Lean.Meta.Tactic.Simp.RegisterCommand` macro creates these checked meta initialization
handles; neither occurs in a shipped theorem dependency closure in the qualified report.
Their two exact module/hygienic-name keys allow no other generated opaque. The
`LabelExtension` handle generated by `register_label_attr vc_contract` in
`ZigLean/VC/ContractAttr.lean` is allowed the same way; it only selects which proved
contract theorems VC extraction (`ZigLean/VC/Extract.lean`, whose meta code uses bounded
recursion rather than `partial`) may apply. The private
partial `Zig.SepAutomation.atoms.collect` helper is separately allowed by its exact
module/user-name key. It computes candidate frame syntax for `sep_frame`; the tactic
constructs ordinary proof terms using `Zig.Triple.frame`, `Zig.Triple.conseq`, and
separation equalities that Lean checks. Its opacity is a meta-computation boundary,
not an additional logical axiom. Dependencies and execution attributes still undergo
the same audit. Each private
libm primitive also has an exact extern backend/symbol
contract; changing a target or adding an ordinary extern-backed definition fails unless
its exact contract is reviewed. Assembly theorems state the necessary instruction behavior as
hypotheses. Libm remains unspecified in the logical model; `implemented_by` provides
runtime behavior, not a theorem of numerical accuracy. A new project opaque requires
an explicit policy entry even when it has a perfectly ordinary checked value.

### Generated declarations

The translator emits axioms and opaques of its own: an inline asm op is an opaque
`airAsm_<hash>` (ASM-01) or `airAsmFx_<hash>` (ASM-03), and a `trust: "assumed"` model binding
gets an evidence axiom `air2lean_model_<i>_evidence` (EXT-02). These are classified by the
premise they stand for, not listed by name: each entry of the policy's
`generated_declarations` names a kind, a name template (`<n>` a number, `<binding>` the index
of a model binding; a template without a placeholder is rejected, so no entry names one
declaration) and the premises. A declaration matches only if

- its module's source is a generated module that `scripts/gen-integrity.py` retranslates (one
  of its cases, `assumptions.retranslated`), so preflight and CI hold it to fresh translator
  output, and it looks generated (`premise_markers.is_generated`: `Gen.lean`, `Gen-<os>.lean`
  or a first-line `-- air2lean-profile:` record, outside the architecture-audit stand-ins). A
  hand-written axiom posing under a generated name, even in a file that copies the profile
  record or is named `Gen.lean`, is not one: no retranslation rule covers that file, and
  gen-integrity rejects it as well;
- that source declares it under the namespace it records (the olean and the source agree);
- for `<binding>`, the module's `-- air2lean-models:` record has that binding with the entry's
  `trust` (`assumed`, no proof).

The `<implementation>` entry classifies the opaque a retranslated module's model binding names as
its `implementation` (an unknown foreign callback such as `CallbackModel.visit`, EXT-01). A
binding's own premise (`extern.premise`, EXT-03 for an extern symbol) joins the entry's. The
classified node records `premises`, and each theorem lists the premises of the generated
declarations it reaches as `declaration_premises`; `scripts/premises.py compiled` and
`scripts/claims.py` (`premises`) report them. Everything else stays `unexpected-axiom` or
`unexpected-opaque`. Lake modules resolve to their library path;
`scripts/theorem_universe.py` passes every universe unit's source (`--sources`). A module
without a known source (a gate's temporary translation) is never classified.

An opaque that is compiled code needs no entry: the tactic and elaborator implementation of the
proof framework (`partial def` over `MetaM`/`TacticM`, an `initialize`d environment extension or
cache). Lean gives such a constant a kernel opaque as a handle and its meaning through the
compiler, an unsafe `_unsafe_rec` twin or an `[init]` function; the extractor records this as the
node's `backing` (`partial` or `init`). The audit classifies an opaque `meta-code-opaque` when it
has such a backing, carries no compiler redirection or extern of its own, is not unsafe, and
**no theorem's dependency closure reaches it** (`is_meta_code`). Name, module and type play no
part. A theorem that reaches the opaque, even a `partial def` named like an engine function,
sees an arbitrary inhabitant of it, so it stays `unexpected-opaque` and needs a premise. The
class is disclosed like the standard-library opaques and needs no manifest entry.

Standard-library opaques and runtime implementation attributes from the installed Lean
`Init.*`, `Std.*`, and `Lean.*` modules are reported as standard-library/runtime entries.
They are not automatically treated as additional axioms. Any actual axiom reached through
them still requires the standard or explicit project axiom policy. The toolchain, build
search path, installed standard-library modules, and environment extractor remain trusted
inputs; the module prefix classification is not a package authenticity check.

CI runs the full audit and environment regressions after building proofs for the complete
Zig 0.16.0 Linux translation. The report is written to
`$RUNNER_TEMP/air2lean-assumptions.json`, outside the cached build directory, and retained
only for the runner's lifetime. Other translation profiles require their own reviewed
policy and audit; the CI step does not qualify them.

## Reading the JSON

The report has a versioned schema and contains:

- `scope`, `modules`, `build_checked`, `lean_toolchain`, and `policy_sha256`: the selected
  module inventory, whether the wrapper built it, and the policy/toolchain identity.
- `extractor`: exact SHA256 hashes of the extractor source, toolchain pin, Lake configuration,
  Lake dependency trace, and imported extractor olean, plus whether validated output was reused.
- `module_imports`: each actually imported module's direct import names, read from Lean's loaded
  module data, including imports unused by the declaration graph. A module loaded only for IR has
  `null` rather than an invented empty import list. An older extractor's absent metadata remains
  `null` in the policy report. This field is observational: it changes neither policy nor replay
  admission and does not authenticate resolved artifact paths, compiled/source correspondence,
  registered-witness completeness or replay-cache freshness by itself.
- `theorems`: every checked theorem name and defining module, its transitive `axioms`,
  direct `dependencies`, transitive `opaque_dependencies`, logical dependencies carrying
  `compiler_redirections` and `extern_dependencies`, per-theorem `violations`, and `allowed` status,
  plus the kernel type's `conclusion` shape used for claim strength (see `docs/claim-strength.md`)
  and its statement-only `statement_dependencies` (constants in the kernel type, without the
  proof term or any unfolding) and `conclusion_dependencies` (the same after dropping binders and
  hypotheses), and the `statement` structure (binder telescope, conclusion-head declaration
  with module and fingerprint, the computation each head argument runs, and companion witness
  status) from which `scripts/claims.py` and `scripts/project.py` bind goals to generated
  definitions. The extractor imports every registered claim head (`assurance/claim-heads.json`),
  so an audited module that redefines one fails with a name clash.
- `nodes`: a shared dependency graph with actual kernel names, stable user names, defining
  modules, declaration kind, direct dependencies, trust class, unsafe/partial flags,
  `implemented_by` targets, and complete extern entries (kind, backend, and symbol/inline
  pattern; adhoc/opaque entries explicitly have no target). Following these edges reconstructs the
  complete transitive declaration dependency set without duplicating it for every theorem.
- `project_declarations`: trust-relevant project declarations checked independently of
  theorem reachability, and `violations`: the gate's global rejection list.
- `float_semantics`: per numerical theorem and as a summary, the float semantics it concerns
  (`ieee`, `compiler-rt@<versions>` or `abstract-spec`, from `assurance/float-semantics.json`).
  An unlabeled numerical theorem or a label that contradicts the graph is a violation
  (`docs/float-semantics.md`).

Logical dependency edges do not include `implemented_by` replacement edges. The report
records those targets separately because execution and kernel proof reduction use different
bodies. An unlisted project replacement fails even if a theorem about its logical body is
valid. The same rule applies to extern attributes on ordinary definitions, including
unreferenced project definitions. This distinction also exposes test-only execution redirections.

Without `--module`, the audit also compiles and loads the witness fixtures registered in
`assurance/witness-fixtures.json` (with the local modules they import), so that companions
declared there count for shipped claims (docs/claim-strength.md, Witnesses). Their theorems go
through the same policy and kernel replay, their oleans are bound to their sources in
`freshness`, and the report lists them separately (`witness_modules`, `witness_theorems`); the
scope stays `all-shipped-modules` with `modules` the shipped inventory.

`--module <module>` (repeatable) selects a **scoped** audit; its report says
`scope: explicit-modules`. `--no-build` is intended for the regression harness and callers
that have independently built current artifacts; its report says `build_checked: false`.
Module arguments, receipt module paths, numerical registry module keys and project contract
paths share `lean-deps.py`'s bounded ASCII module spelling, including `'`, `!` and `?`.
Quoted or escaped spellings are refused. Project paths must end in `.lean`, with one literal
module component per directory or filename: `A.B.lean` cannot stand for `A/B.lean`.
This does not change declaration-name or Zig-namespace validation, module enrollment, policy
or the compiler-owned source/output checks.

Project check records hash the actual project validator and the selected auditor's physical
adjacent `lean-deps.py`, in addition to their declared scripts. A custom auditor stub without
that helper remains supported; no repository helper is substituted. An existing malformed
helper fails, and changes in known-script bytes, presence or physical identity fail the existing
input-stability stage. Each check reloads its project validator before validation. These are
known input checks within the trusted Python runtime, not arbitrary import discovery,
immutable execution, writer authentication or additional receipt qualification.

`--all-declarations` additionally seeds every declaration in the selected modules, including
unused private definitions and compiler-generated recursors, and records their names in
`selected_declaration_roots`. It uses the same dependency traversal, policy and kernel replay.
The default roots remain theorems and project boundary declarations; the flag does not select
every unused declaration in imported modules or certify that a dependency is legacy-free.

The raw opt-in extractor records `selected_declaration_evidence`: one row, in the same order,
for each exact selected root. The CLI report preserves those rows under
`framework_candidates.declarations`, adding the summaries below. A row identifies the
original kernel name, user name, module and declaration kind; the original type/body
constant identities and kernel-expression fingerprint are preserved before reduction.
`is_proof` distinguishes a proof value using the existing kernel signature checker and
kernel equality of its inferred sort to `Prop`, with a theorem shortcut. It does not
inspect a proof body or use normalization of the proposition as a substitute for checking
its sort. Kernel signature checking can reduce types. A free or
metavariable signature, or any kernel API error, fails the audit. This performs a signature
check per non-theorem selected declaration; its cost depends on the selected environment.
A Prop-valued predicate's `prop_valued` and binder
evidence come from opening its full type telescope with transparency `.all`, including
irreducible aliases. Unknown result
sorts remain `null`. Projection, matcher and auxiliary-recursor flags are provenance, not
exemptions. Imported dependencies can occur in `nodes` without being selected roots.

`framework_candidates` propagates the framework gate's canonical computation-family
identities through that same original dependency graph. The opt-in driver first resolves
every canonical identity in its actual Lean environment; a missing name fails the audit.
`program_dependencies` is syntactic positive evidence, not recognition of all computation
types: a written-out `Zig.Mem → Option (Except …)` can have an empty list. **An empty list
means unknown, never ordinary data.** A Prop-valued definition/opaque/inductive with a
computation-family witness has verdict `candidate`; every other row has verdict `unknown`.
Neither verdict approves a framework status or changes policy.

`unresolved_dependency` is a conservative boundary flag: it is true if the declaration's
original dependency closure (including itself) contains an unresolved constant, an opaque,
an axiom, an `implemented_by` redirection or an extern entry. Opaques with checked values and
standard logical axioms still set it, independently of whether policy permits them. The
replacement implementation is recorded separately, not followed as a kernel dependency.
A candidate can have this flag; a false flag does not certify a closed type or complete
execution semantics. This is not a restatement of policy violations.

This evidence is explicitly `scope: selected-modules-only`, `complete: false`, with
`ordinary_exemption: false` in every row and no ordinary exemptions. It establishes no
recursive closed-data classification, status approval, legacy-free result, complete module
enrollment, producer authority or additional source/artifact binding. The existing policy,
kernel replay, freshness and audit-scope requirements still apply. The default extractor
omits `selected_declaration_evidence` and `selected_declaration_roots`; the default CLI
report omits `framework_candidates` and `selected_declaration_roots`.

The extractor always runs `lake --rehash build AssuranceTools` to validate its source,
compiler identity, and imported dependencies. Its separately recorded source/pin/configuration
and exact olean/Lake-trace hashes must match before output can be reused. Missing or corrupt
output and changed source or release pin force rebuilding. There is no skip-compile flag.
These hashes are kept as one record per context (`.lake/assurance/tool-traces/<context
hash>.json`), so invocations with different contexts do not invalidate each other's records; a
context without a valid record unlinks the olean and Lake rebuilds it. All invocations in one
worktree share the olean: an exclusive lock (`.lake/assurance/tool.lock`) is held from
preparation until the `lake env lean` run that imports the olean ends, so parallel audits never
remove or rebuild it under each other. Kernel replay runs outside the lock. A lock or IO error
fails the audit.
The regression harness reuses a validated extractor while still importing every fixture
into a separate real Lean driver, in serial order.
Neither is a substitute for the default complete build-and-audit release gate. The report
covers the currently selected generated Lean translations, not every Zig version/OS
translation stored as goldens. Run it again for each qualified translation/profile.

## Limits of the assurance claim

An opaque declaration can have a checked value. Opacity alone is not a logical assumption;
its trust class records a reviewed boundary rather than inventing an axiom. Theorem types
retain ordinary hypotheses about assembly, allocations, scheduling, and other semantic
premises. This gate inventories constants and axioms, not a semantic interpretation or
human-readable enumeration of all local hypotheses. The semantic premises (profile,
allocator, scheduler, ordering, timer, float, assembly and trust) have stable IDs in
[premises.md](premises.md). [premise-index.md](https://github.com/riventic/air2lean/blob/generated/docs/premise-index.md) maps each theorem to
those IDs. `scripts/premises.py compiled --assurance <this report> --strict` derives the
same mapping from this report's dependency graph and fails if the committed index misses a
premise of any audited theorem; CI runs it after the audit.

The audit demonstrates that the selected compiled theorem inventory obeys the explicit
dependency policy. It does not prove Zig export, AIR normalization/emission, backend
lowering, native code, foreign functions, or source/profile correspondence. Standard
kernel rules (including quotient primitives) remain part of Lean's trusted foundation.
Source/AIR/generated-code provenance and compiler qualification need their own reports.

The current implementation re-traverses the shared graph for each theorem to compute
its opaque/extern dependency lists. This is cycle-safe but can cost time on a large
inventory with many shared dependencies. A local guarded check of 10,429 theorems and
30,401 graph nodes completed the full audit with warm build artifacts in 15.4 seconds,
peaking at 1,565 MiB. Reapplying policy and computing dependency closures on that report
took 5.86 seconds. These are measurements for one checkout and machine, not runtime or
memory guarantees. Retain measurements before changing traversal or introducing
cycle-sensitive memoization.
