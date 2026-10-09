# Revision-bound theorem audit receipts

A proof receipt binds one successful local build-and-audit attempt to the selected
compiled Lean theorem inventory, dependency policy, source bytes, generated definitions,
compiled artifacts, tools and bounded execution report. It extends the existing
[assumption audit](assumptions-audit.md) and [build guard](build-budgets.md).
It does not change either tool's proof or process-control semantics.
To chain a receipt to source, AIR, compiler patch, runtime and profile identities, record an
[artifact manifest](artifact-manifest.md) with `--receipt`; receipt schema 1 is unchanged.

The receipt is not signed or authenticated. Its executor, source tree, installed Lean
library, Lake dependency validation and environment extractor are trusted local inputs.
Hashes detect drift relative to a retained receipt; a caller able to forge the receipt
and its entire evidence directory is outside that claim. Keep a trusted digest/reference
when sharing evidence. This tool does not upload or publish artifacts.

## Fresh audit

Run the following from the repository root, with no other qualification command active.
Use the same user-wide `AIR2LEAN_BUILD_LOCK` across participating worktrees. The shell
entry point acquires the existing guard itself: **do not nest it inside another guard
using the same lock**. It runs no Zig compiler and never installs toolchains.
The default guard is the repository's exact `scripts/build-guard.py`. A separately
reviewed guard can be selected by explicit path and SHA256; its identity is part of
the receipt. The selected guard retains its documented platform requirements.

```sh
bash tests/roadmap/proof-receipts/check.sh \
  --guard "$REVIEWED_GUARD" --guard-sha256 "$REVIEWED_GUARD_SHA256" \
  "$FRESH_ATTEMPT" "$REAL_LEAN_TOOLCHAIN" selected-generated-state
```

The pin is mandatory for an external guard. Preparation, guarded inputs, final report
and sealing must all agree with that file identity; changes or mismatches fail closed.

```sh
# REAL_LEAN_TOOLCHAIN is the physical installed directory containing bin/lean,
# bin/lake and lib/lean. Select the release pinned in lean-toolchain.
# FRESH_ATTEMPT is an absolute path that does not exist; its parent must exist.
bash tests/roadmap/proof-receipts/check.sh \
  "$FRESH_ATTEMPT" "$REAL_LEAN_TOOLCHAIN" selected-generated-state
```

Without module arguments the existing auditor selects every shipped `ZigLean/` and
`Proofs/` module, plus `ZigLean.lean`. For a scoped check, append exact module names:

```sh
bash tests/roadmap/proof-receipts/check.sh \
  "$FRESH_ATTEMPT" "$REAL_LEAN_TOOLCHAIN" basic-selected-state Proofs.Basic.Proofs
```

The final argument before the modules is a run-context label, not proof of a target
profile. Select the intended generated translation before running. A fresh receipt
always uses the auditor's build path; it does not accept `--no-build`. Before preparing
the attempt, `check.sh` runs `scripts/gen-integrity.py attest` (built translator required)
and stops if a tracked generated module is not a fresh translation of its committed AIR
([generated-code.md](generated-code.md#generated-module-integrity)); the guarded worker
binds that script's identity as an input.

A tree with uncommitted tracked changes is refused unless `--allow-dirty`
(`AIR2LEAN_RECEIPT_ALLOW_DIRTY=1` for `check.sh`) is given; the receipt then records
`tree.dirty_allowed: true`. Release consumers refuse such a receipt:
`proof-receipt.py verify --release`, `artifact-manifest.py check-manifest` for a chained receipt
(unless its own `--allow-dirty`), and `scripts/release-record.py`, which rejects a workflow whose
gate permits a dirty-tree receipt. CI never needs the permission: no verification step writes a
tracked file ([generated-code.md](generated-code.md#check-trees)), and its last step fails if
`git status --porcelain` is not empty.

Tool, artifact, lock, attempt and receipt paths must be absolute and physical, with no
symlink components. Every tracked source file is fingerprinted, including dirty/staged
contents. A tracked source alias records its literal relative link and the content identity
of its tracked regular target inside the repository; external targets, alias chains and
directory aliases are rejected. Generated profiles are read through that same validated
source alias. Missing sources or nonregular targets, untracked Lean/JSON/TOML/Python/shell build inputs, `lakefile.lean` overriding the
selected TOML configuration, and external Lake packages are rejected. Stage newly added
source files before qualification. Relevant inputs must be tracked, not ignored overlays.

The worker rejects `LEAN`/`LAKE`, `ELAN_TOOLCHAIN`, library-loader overrides, and
all `LEAN_*`/`LAKE_*`/`DYLD_*` overrides except the guard's `LEAN_NUM_THREADS`. Its selected toolchain bin directory is first on PATH.
The receipt records that toolchain's entire `lib/lean` inventory and exact Lean/Lake
binary identities. The repository's compiled library is also inventoried; olean files
without tracked corresponding source, or repository copies of Init/Std/Lean modules,
are rejected. Selected module oleans and Lake traces, plus the extractor artifacts,
must exist. This bounded initial interface supports the repository's empty-package
Lake manifest; adding package dependencies needs a separately reviewed closure rule.
It is not an authenticity check of the installed toolchain or dependency store.

## Attempt states and recovery

The entry point creates a new directory with `plan.json`, then the worker runs under the
acquired lock. The worker checks the planned revision/source identities, writes
`before.json`, performs the existing audit, and requires the source/tool/library context
to remain unchanged before writing `after.json`. The compiled artifacts and generated
profile inventory belong to the post-build snapshot. The guard writes its final JSON
and log after cleanup and reaping. Only then does the receipt tool seal the attempt.

A passing receipt requires exact requested/executed argv, cwd, lock, run label, phase,
revision, input/output/tool/guard/pin identities, successful child and guard exits,
untruncated complete log evidence, and a passing nonempty build-checked audit. The
receipt tool reapplies the existing dependency policy to the extracted graph; changing
an `allowed` flag cannot conceal hidden sorry, a new axiom or other policy violation.

Publication uses an atomic no-clobber link. Neither a second finalizer nor a retry can
overwrite a prior receipt. A failed audit, timeout, signal, cleanup failure, missing
artifact or changed context leaves the attempt incomplete, with retained diagnostic
files when available. SIGKILL/host failure can leave an incomplete attempt, which is
never treated as current success. Retry using a different fresh attempt directory.
Source, tool or library drift visible at the recorded identity checks rejects the attempt
even if the compiler command returned zero. There is no continuous watcher: a transient
edit restored between checks may go undetected and is not attested by the receipt.

The entry point uses the guard's existing 900-second workload timeout and reactive
sampled 8192 MiB RSS threshold, single-thread Lean setting, and process-group cleanup.
Their limitations remain exactly those documented in build-budgets.md. Receipt hashing
and verification use streaming reads and explicit per-file/inventory limits; they are
not another compiler process controller or incremental build cache. JSON is capped at
256 MiB/64 nesting levels, with duplicate keys and oversized/nonfinite numbers rejected.
Identity files are capped at 512 MiB each, 30000 files and 16 GiB per inventory. The
remaining inventory allowance limits each streaming read; excess bytes stop hashing
immediately rather than being checked after the whole inventory is consumed.

## Verify current identities

```sh
python3 scripts/proof-receipt.py verify "$FRESH_ATTEMPT"
```

Exit 0 reports `status: current`, `checking: not_rerun`,
`authentication: not_attested` and `tree` (`clean` or `dirty-allowed`); with `--release` a
`dirty-allowed` receipt exits 2. Exit 2 means evidence is unavailable, invalid or stale;
read stderr. Verification rereads the source, tool/library, compiled/profile and receipt
artifact inventories and reapplies the policy. It does not run Lake or Lean, rebuild
proofs, assert a digital signature, or turn an incomplete attempt into success.
Unrelated tracked edits or compiled-library changes can invalidate the receipt: these
are conservative byte identities, not semantic fingerprints or dependency-aware caches.

`after.json` names each tracked generated `Gen.lean` and its raw byte identity. A valid
first-line profile record remains attached to that particular generated module/file.
No header means `legacy-or-unannotated`; a run label cannot relabel it as a qualified
schema12 export. Most committed translations carry no header (it is host-specific, and
verification no longer writes it into the checkout), so a receipt records them as
`legacy-or-unannotated`; the profile validated for the run is in `scripts/check.sh`'s
`.lake/check-reports/<version>/<example>.json`, which the receipt does not yet bind. Different historical translations remain separately identified.
The existing audit names theorem modules and contains their dependency graph; the
receipt does not infer theorem domains or all-schedules properties from their names.

## What the result establishes

The selected compiled theorem inventory passed the existing Lean dependency/assumption
policy in this recorded attempt. Standard logical axioms, project opaque/extern/runtime
boundaries and allowed assumptions remain in `audit.json`. Ordinary theorem hypotheses
and property domains require reading the theorem and its reviewed documentation.

This is evidence about generated Lean and its checked environment. The receipt states
`source_correspondence: not_attested` and `native_adequacy: not_attested`. Receipt schema 2
also carries `float_semantics`: the audit's label summary plus each stated numerical theorem's
label (`ieee`, `compiler-rt@<versions>` or `abstract-spec`), with
`binary_correspondence: not_claimed` (`docs/float-semantics.md`). It does not
prove original Zig export, normalization/emission preservation, backend lowering,
shipping native binaries, foreign behavior, fairness, termination or exhaustive testing.
A scoped audit is not an all-shipped audit, and one selected translation does not qualify
all Zig versions or platforms. Full release gates and unavailable checks need their own
records; this receipt alone does not establish complete release qualification.

Offline regressions use tiny files and mocked auditor execution only:

```sh
python3 tests/roadmap/proof-receipts/test_receipt.py
```

Root qualification should additionally run a genuine small proof/audit, a policy-rejected
fixture, a genuine build failure and an interrupted guarded attempt before the complete
selected shipped audit. Keep all evidence under an uncached run directory such as
`RUNNER_TEMP`; no upload step is added by this scope.

At local revision `f18e0e6`, the guarded all-shipped audit passed for 10,621 compiled
Lean theorems and 30,930 declarations. Small-scope receipts and disposable-copy drift,
restoration and no-clobber checks passed; hidden-sorry and project-axiom fixtures were
rejected by their intended violations, a type-error fixture failed its build, and
pre-audit self-interruption produced no receipt. These are historical checks of that
recorded revision and compiled Lean policy; they do not establish original-source
correspondence, native adequacy or CI success for later revisions.
