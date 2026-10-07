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

`scripts/no-sorry.sh` remains a separate source-level gate. Run both:

```sh
scripts/no-sorry.sh
scripts/assumptions.sh --output .lake/assurance/assumptions.json
tests/roadmap/assurance/check.sh
```

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
pinned Lean release. A changed private counter or hygienic name fails until reviewed.

The current allowed project opaques are the four register-only assembly functions,
`Zig.Float.libm`, and the individual private extern primitives used by its executable
libm implementation, plus the `SimpExtension` and `SimprocExtension` handles generated
by `register_simp_attr zig_unfold` in `ZigLean/SimpAttr.lean`. Lean's
`Lean.Meta.Tactic.Simp.RegisterCommand` macro creates these checked meta initialization
handles; neither occurs in a shipped theorem dependency closure in the qualified report.
Their two exact module/hygienic-name keys allow no other generated opaque. The private
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
- `theorems`: every checked theorem name and defining module, its transitive `axioms`,
  direct `dependencies`, transitive `opaque_dependencies`, logical dependencies carrying
  `compiler_redirections` and `extern_dependencies`, per-theorem `violations`, and `allowed` status.
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

`--module <module>` (repeatable) selects a **scoped** audit; its report says
`scope: explicit-modules`. `--no-build` is intended for the regression harness and callers
that have independently built current artifacts; its report says `build_checked: false`.
The extractor always runs `lake --rehash build AssuranceTools` to validate its source,
compiler identity, and imported dependencies. Its separately recorded source/pin/configuration
and exact olean/Lake-trace hashes must match before output can be reused. Missing or corrupt
output and changed source or release pin force rebuilding. There is no skip-compile flag.
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
human-readable enumeration of all local hypotheses.

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
