# Project manifests and evidence

`scripts/project.py` adds a stdlib-only project boundary around the built translator. It
reads explicitly selected inputs, reports independent malformed AIR files and exporter
`unsupported: true` markers, translates each root and its declared AIR dependencies, and
records hash-bound evidence. It never downloads or builds tools.

Run from a qualified environment with an existing translator:

```sh
python3 scripts/project.py report project.json --out coverage.json
python3 scripts/project.py translate project.json \
  --translator .lake/build/bin/air2lean --out artifacts/run-001
python3 scripts/project.py verify project.json --artifact artifacts/run-001
```

`report` checks bounded JSON syntax, root-name presence and profile metadata. `translate`
runs the actual translator on each root's AIR set, with no shell, passing namespace, prefix,
explicit float semantics and the effective spawn policy. Each root needs every AIR dependency required by the
translator's whole-program check; a standalone function file is not assumed independent.
Translation errors are collected across roots. A root may still have additional semantic
blockers beyond the first error emitted by the existing translator. The wrapper does not
infer instruction support from tag spelling.

Reports and translation artifacts have different publication rules. A report is a JSON
file, created with an atomic no-clobber link by default; `--overwrite` atomically replaces
an existing report. Input files cannot be selected as report destinations. An artifact is
a fresh directory containing `<root-id>/Gen.lean` and `report.json`. An existing artifact
is never intentionally replaced, and translation has no overwrite option. Failed roots,
timeouts, SIGINT or SIGTERM leave no new artifact directory. Prior artifacts remain
available. Publication uses a same-filesystem rename; users must give concurrent runs
different artifact destinations. A final existence check refuses outputs that appeared
while translation ran.

`verify` recomputes every recorded input and generated-file SHA-256, as well as the invoked
translator executable hash. It detects changed manifests, source files, contracts, profile
files, declared toolchain/runtime/patch inputs and generated Lean. It reports
`proof_status: not_attested`: hash agreement is not a proof or authenticity signature.
The stored report is the reference inventory; retain its digest in a trusted release
record when authenticity matters. Git revision and dirty-state availability are recorded
separately. Git HEAD alone does not identify dirty input contents; the input hashes do.

## Manifest schema 1

[The example](../example-project.json) uses an existing legacy AIR
fixture and a declared source closure. All paths resolve relative to the manifest directory,
remain inside that directory after symlink resolution, and name existing regular files.
To place a manifest at a repository root, adjust its paths to that root; parent traversal
and absolute input paths are rejected. Unknown keys, duplicate keys, duplicate list entries,
nonfinite JSON numbers and incorrect JSON scalar types are rejected.

Required top-level keys:

| Key | Meaning |
|---|---|
| `schema` | Integer `1` |
| `profile` | Path to a strict profile JSON artifact |
| `float_semantics` | Runtime model selection: `ieee` or `compiler-rt` |
| `source_closure` | Nonempty declared source-file inventory |
| `components` | Nonempty file lists for `compiler_patch`, `runtime`, `toolchain` |
| `allowed_assumptions` | Allowed assumption identifiers |
| `roots` | Nonempty root records |
| `limits` | Optional stricter resource limits |
| `spawn_policy` | Optional `available` (default) or `fallible` spawn model |
| `check` | Optional proof-checking budget for `check` (below) |

`spawn_policy` selects the translator's spawn model for every root. Both omitted and
explicit `available` manifests pass `--spawn-policy available`; `fallible` passes
`--spawn-policy fallible`. The `report` preflight records the effective selection but
cannot establish that the AIR is supported by that model. Translation retains the
whole-program checker, including its rejection of unsupported fallible concurrent
clients. Selecting a policy does not prove a property, observe a runtime outcome, or
attest source correspondence. The fallible semantics require the composed Spawn
implementation in the selected translator.

New translation receipts record the effective policy and each translation's argv.
`verify` requires both to match the manifest. Historical receipts without a
`spawn_policy` field remain compatible only with the `available` default; they cannot
verify a fallible project. Verification still checks hashes and does not run proofs.

Each root requires `id`, `function`, `air`, `namespace`, `prefix`, `contracts`, `goals`,
`assumptions` and `exclusions`, and may name `generated`: the committed generated Lean
module its contracts import (hashed like every other input; required by `check`). AIR paths include the named function and its dependencies.
IDs are letters followed by letters, digits, underscores or hyphens. Namespaces are
ASCII dot-separated Lean identifiers. Contracts are file paths. Every goal has a theorem
name, a `domain` string and a `strength`: `safety`, `partial_correctness`,
`total_correctness`, `resource_bound` or `correspondence`. Every root assumption must occur
in `allowed_assumptions`. These are declarations for review, not discovered theorem
premises or checked contracts. `scripts/claims.py check` separately rejects a goal whose
declared strength exceeds the strength derived from its audited theorem type
(`docs/claim-strength.md`).

The legacy profile artifact has exactly `name: "legacy-abi64-le"` and `zig_version`.
It preserves explicit missing-target-metadata disclosure. A schema-12 profile artifact is
the exact exported nested `profile` object: `name`, `target_triple`, `pointer_bits`, `endian`,
`abi`, `zig_version`, `backend`, `cpu`, `features`, `build_mode`, `float_mode`,
`error_set_bits`, `error_layout`, `error_tracing` and `export_stage`. The supported explicit
name is `abi64-le-v1`, with the existing x86_64 Linux or aarch64 macOS, 64-bit, little-endian model ABI,
16-bit errors, per-instruction float mode and type-table error layout. Every selected
schema-12 AIR file must match the full profile object. The standalone profile omits the
outer AIR `schema` field. Legacy profiles cannot relabel profile-bearing AIR.

Limits are positive integers no greater than the defaults:

| Limit | Default maximum |
|---|---:|
| `max_file_bytes` | 8 MiB |
| `max_total_bytes` | 64 MiB, including manifest |
| `max_json_depth` | 128 |
| `max_files` | 4096 unique input files |
| `max_roots` | 256 |
| `max_total_output_bytes` | 64 MiB each for generated Lean aggregate and report/log aggregate |
| `timeout_seconds` | 60 per root invocation |
| `max_output_bytes` | 8 MiB per translator log/output file |

The manifest itself has a hard 8 MiB/128-depth bootstrap cap. POSIX process groups ensure
cancellation kills child descendants. A wrapper that exits with surviving descendants fails
the stage and has its remaining process group killed. Then `RLIMIT_FSIZE` bounds translator output files.
This workflow currently requires POSIX; it is not a hostile-code sandbox. A translator
that requires larger files should be configured through a reviewed change to the limits,
not allowed to allocate without a bound.

## What each status means

Every root has separate `analyzed`, `exported`, `translated`, `compiled`, `tested` and
`proved` entries. Only `translated` can pass through this wrapper today. JSON preflight
has its own `input_validation` entry, so accepting JSON does not claim Zig semantic
analysis. Supplied AIR is not evidence that this invocation exported the declared
sources. Declared goals, a wrapper theorem and sampled tests cannot turn `proved` into
`passed`. Export, Lean proof checking, differential execution and incremental caches
remain explicit unavailable capabilities of `report`/`translate`; `coverage` (below) joins
separately recorded proof receipts and differential summaries. The full roadmap
acceptance criteria for I03/I05/I07/I08 are not complete.

Diagnostics have stable wrapper codes, categories, root/path context and optional source
and dependency locations. The current AIR format does not reliably supply those
locations, so `source_span` is null and `dependency_chain` empty; neither is invented.
`AIR_EXPORT_UNSUPPORTED` is distinct from malformed JSON and opaque
`TRANSLATION_FAILED` messages. Success in a subprocess is translation evidence only.

Outcome counts separately name exact matches, host differences, undefined/unspecified
behavior, nondeterministic valid outcomes, unsupported semantics, panic, error returns,
illegal behavior, deadlock, divergence, search caps, skips and proof exclusions. Zero
means no recorded observations, not a proved absence. Unsupported counts record explicit
exporter instruction markers; they are not a count of failed test cases. No differential results are imported
by this version. Proof exclusions count declared exclusion records rather than functions
or test cases. Source closure completeness, backend correspondence, translator preservation
and theorem dependency closure remain trust-boundary obligations printed in every report.

Run the mocked regressions without Zig, Lean or Lake:

```sh
python3 -m unittest discover -s tests/roadmap/project -v
```

The full Zig 0.16 CI job runs these offline regressions after building the translator,
then translates `example-project.json` with that executable and verifies the resulting
artifact hashes. The artifact and JSON reports stay under `RUNNER_TEMP` and are not
uploaded by this gate. This checks translation and stale-input detection; it does not
check the declared Lean proof goals or establish source/export/backend correspondence.

## Verification coverage reports

`coverage` joins each manifest root with independently produced evidence and assigns an
explicit verification level. It runs no compiler, Lake or Lean process itself.

```sh
python3 scripts/project.py coverage project.json \
  --artifact artifacts/run-001 \
  --receipt "$FRESH_ATTEMPT" \
  --diff "$AIR2LEAN_DIFF_REPORT" \
  [--format text] [--out coverage.json] [--require-level functionally_verified_total]
```

Every input is optional; a missing input leaves its stages `not_run`. Evidence sources:

| Stage | Evidence | Pass rule |
|---|---|---|
| `analyzed`, `exported` | none available | always `not_run`; supplied AIR is not export evidence |
| `translated` | `--artifact` | `verify` succeeds: manifest, inputs, generated Lean and translator hashes current |
| `compiled` | `--receipt` ([proof receipt](proof-receipts.md) attempt) | `proof-receipt.py verify` reports `current`; some receipt `after.json` generated profile is byte-identical to the artifact's `Gen.lean`; each contract file's current hash equals the receipt source inventory; generated and contract modules are in the compiled inventory |
| `proved` | receipt `audit.json` | per goal (below); `passed` only when every declared goal is `direct` |
| `tested` | `--diff` (repeatable, typed diff-report summary + `.jsonl`) | summary complete; it hashes at least one declared source-closure file and all such hashes are current; at least one match and no mismatch, host difference, input or harness failure or unrecognized status for `example.function` |

The receipt verifier defaults to `scripts/proof-receipt.py` and can be overridden with
`--receipt-verifier` (tests use a mock). Any nonzero exit or non-`current` answer marks
`compiled` and `proved` failed as a stale receipt. Only the existing receipt/plan/audit/after
files are read; their format is not extended. Differential source binding matches
manifest-relative `source_closure` names against the runner's repository-relative
`runner_runtime_sources`, so place the manifest at the runner root for that binding.

Each goal is bound to an audited theorem named `theorem` or `namespace.theorem`, with
one of these bindings: `direct`, `missing`, `outside_contracts` (module is not a declared
contract file), `policy_violation` (audit `allowed` false or violations),
`wrapper_or_unrelated`, `source_hash_mismatch`, `stale_receipt`, `unbound` or `no_receipt`.
`direct` requires the conclusion of the theorem's statement (its kernel type after binders
and hypotheses, the audit's `conclusion_dependencies`) to reference the generated root
definition `namespace.(function without prefix)`, which must live in the hash-bound
generated module. Proof terms are not consulted: a theorem stated about a wrapper, a
hand-written model, `True`, or with the root only in a hypothesis is `wrapper_or_unrelated`
even when its proof mentions the generated code. An audit without statement dependencies
(an older extractor) leaves goals `unbound`. Statements are not otherwise interpreted, so a
weak conclusion that mentions the root (for example `root x = root x`) still binds; declared
strength and domain remain review obligations. `tests/roadmap/assurance/StatementBinding.lean`
holds a wrapper-statement, a `True`, a hypothesis-only and a genuine theorem; only the last
binds (`tests/roadmap/coverage-report/test_coverage.py`).

Levels, lowest first: `none`, `translated`, `compiled`, `tested_sampled`, `proved_scoped`,
`functionally_verified_partial`, `functionally_verified_total`.

* `functionally_verified_*` requires passed preflight, `translated`, `compiled`, at least
  one declared goal, every goal `direct`, and at least one `partial_correctness` or
  `total_correctness` goal. `_total` additionally requires a direct `total_correctness`
  goal; only that level sets `fully_functionally_verified`.
* `proved_scoped`: translated, compiled and at least one direct goal, but the functional
  rule fails (missing/wrapper goals, or only `safety`, `resource_bound`, `correspondence`).
* `tested_sampled`: translated, compiled and passing differential samples. Differential
  evidence is always `scope: sampled` and never contributes to a higher level.
* A wrapper-only theorem or sampled-only tests therefore cannot reach functional
  verification; `blockers` lists every unmet rule.

Each root also reports `contract_domain` (declared domains, `review: declared_not_checked`),
`theorem_strength` (declared and direct strengths; strengths are manifest declarations, not
machine-classified statements), `assumptions` (declared manifest identifiers plus audited
axioms, opaque, extern and compiler-redirection dependencies of direct theorems) and
`exclusions` (manifest exclusions, differential exclusion/skip counts and the receipt's
`not_attested` trust fields). `outcomes` counts the root's differential cases and
exporter-marked unsupported AIR in the shared [outcome taxonomy](outcome-taxonomy.md);
`absence_claims` reports `no-panic` and `guaranteed-return` as `proved`, `refused` or
`not_proved`. Only a direct goal of matching strength proves one; a capped search, fuel-bounded
no-result run, unspecified (including no-clock timer) or unsupported outcome, or an observed
failure the claim denies, refuses it and adds a blocker, so the root cannot reach
`functionally_verified_*`. Error returns never refuse `no-panic`. `--require-level` exits 1 when any root is below the level;
diagnostics also exit 1, invalid input exits 2. `--out` uses the same no-clobber/`--overwrite`
publication as `report`.

Residual limits: a theorem whose own proof term mentions the generated definition while
its statement concerns a wrapper is still classified `direct`; the declared strength and
domain remain review obligations. The level does not attest export, source
correspondence, backend lowering or native adequacy (see the receipt's trust fields).

```sh
python3 -m unittest discover -s tests/roadmap/coverage-report -p 'test_*.py' -v
```

## Reproducible project check

`check` reproduces translation and proof checking from one committed manifest and writes
a reproducibility record. Run it at the Lake project root (the manifest directory) with a
built translator; it is the only project command that runs Lake.

```sh
python3 scripts/project.py check example-project.json \
  --translator .lake/build/bin/air2lean --out "$RUNNER_TEMP/project-check"
python3 scripts/project.py compare-records machine-a/record.json machine-b/record.json
```

Stages, in order; the first failure stops later stages, which stay `not_run`:

| Stage | Action | Pass rule |
|---|---|---|
| `translate` | `translate` into `<out>/artifact`, then `verify` | every root translated; all hashes current |
| `reproduce` | split each fresh `Gen.lean` and committed `generated` module with `scripts/normalize-generated.py` | fresh profile record agrees with the manifest profile and `float_semantics`; committed record absent or identical; bodies byte-identical |
| `build` | `scripts/build-guard.py --phase proof -- lake build <contract modules>` | guard outcome `success` |
| `audit` | `build-guard.py --phase check -- python3 scripts/assumptions.py --no-build --module <contract modules>` | completed report whose scope equals the contract modules |
| goals | each declared goal's audited theorem (`theorem` or `namespace.theorem`) | `allowed` (below) |
| `claims` | `scripts/claims.py check` on the audit | every declared strength within its type-derived strength |
| `inputs_stable` | re-hash every manifest input | unchanged since the start |

The audit covers whole contract modules, but only goal theorems are judged: a policy
violation in another theorem of a contract module (audit status `fail`) does not fail the
check. A goal is `allowed` only when its theorem lives in a declared contract module, has
no audit policy violation, its root definition `namespace.(function without prefix)` is
defined in the committed `generated` module, the conclusion of its audited statement
references that definition (`references_root`, the same statement binding coverage uses),
and every project assumption it depends on
is named in the root's `assumptions` (which the manifest loader already restricts to
`allowed_assumptions`). Project assumptions are non-standard axioms, dependency nodes
missing from the audit graph, and dependencies with an audited `allowed-project-*` or
`allowed-runtime-redirection` trust class; name each by its Lean declaration or its
`module::name` policy key. Lean's three logical axioms and standard-library opaques,
externs and redirections are listed as `standard_assumptions` without a manifest entry.
Other goal rows are `missing`, `outside_contracts`, `policy_violation`,
`unallowed_assumption`, `unbound` (the audit lacks statement dependencies),
`wrapper_or_unrelated` (the conclusion does not name the root) or `unbound_generated`;
the coverage binding rules above still decide verification levels.

The optional `check` object bounds proof checking: `build_timeout_seconds` and
`audit_timeout_seconds` (default 3600, maximum 21600) and the guard's sampled `rss_mib`
(default 8192, maximum 65536). `--lock` selects the guard lock (default
`AIR2LEAN_BUILD_LOCK`); `--build-guard`, `--assumptions-script` and `--claims-script`
override the tools (tests use a stub audit). `lake` resolves from `PATH`.

`--out` is a fresh directory published by rename after the record is written:
`record.json`, `artifact/`, the guard reports and logs, `assumptions.json` and
`claims.json`. A failed stage still publishes its record and exits 1; invalid
configuration exits 2 and an interrupted run publishes nothing.

`record.json` (`kind: air2lean-project-check-record`) has `status` (`reproduced` or
`failed`), `failures`, a `reproducible` section and a `host` section. `reproducible`
holds the manifest and every input hash, the budget, root modules, the hashes of
`project.py`, `build-guard.py`, `assumptions.py`, `claims.py` and `normalize-generated.py`, the `lean-toolchain`
pin, the float and spawn selections, and every stage result (generated hashes, header profiles and body hashes, guard
outcome, audit policy hash and toolchain, per-goal assumptions and claims). `host` holds
what legitimately differs between machines: platform, Python, Git revision and dirty
state, translator path and hash, the Lake executable and pins from the guard report,
timings and peak RSS. `compare-records` compares only the `reproducible` sections and
exits 0 only when they are identical and both records are `reproduced`; it lists up to
200 differing JSON paths.

Scope: a matching pair of records shows that the same committed inputs translate to the
same committed generated modules and that the same goal theorems check with the same
allowed assumptions and strengths on both machines. It does not establish export, source
correspondence or backend adequacy. Translator binaries are trusted per host, and Lake
dependency revisions are covered only through `lake-manifest.json` when it is listed in
`components`.

```sh
python3 -m unittest discover -s tests/roadmap/project-check -p 'test_*.py' -v
```
