# Zig 0.17.0 in CI and release metadata

Zig 0.17.0 (released 2026-10-01, LLVM 22) is **in qualification**. CI runs it, and the
release metadata lists it, but Zig 0.16.0 stays the default and every gate that is
qualified only on particular versions stays on those versions. This page covers the CI,
metadata and version-list part of the 0.17.0 work. The exporter pin and hook
(`zig-patch/`), the coverage inventory (`coverage/0.17.0.json`), the translator's
`supportedVersions` and CLI help, and the example and std-model version lists are owned
by the other 0.17.0 tracks.

## CI matrix

| Row | Decision |
|---|---|
| `0.17.0` full job | Added (`full: true`, every example `scripts/example-selection.sh` selects for 0.17.0). It runs every gate that applies to every version: the compiler inventory check, the float probe, the patched compiler build, golden AIR/translation/diff (`scripts/check.sh`), proofs, VCs, exporter review (`AIR2LEAN_REVIEW_ZIG17`), allocation policy, progress kernel and `no-sorry`. |
| Mutation shards | Stay on 0.16.0, the default, until 0.17.0 is qualified. |
| 0.16.0 / 0.15.2 / 0.14.1 rows | Unchanged. |

The 0.17.0 job is a blocking job, not `continue-on-error`. Its gates fail until the
other tracks have merged: the exporter pin and hook, `coverage/0.17.0.json`, golden
overrides under `tests/golden/0.17.0/` where AIR or translations differ, and a
`tests/floatprobe/expected.0.17.0.txt` if the reference target changes a probed case.

Steps gated to one version (mostly `matrix.zig == '0.16.0'`, plus `0.15.2 || 0.16.0` for
the proof API and typed outcomes) stay as they are. Their source/native qualification
is version-specific (class b below), so they do not run on 0.17.0. One step ran on every
row but rejects unknown versions. Its condition now lists the qualified versions:

- **Loop-switch dispatch regressions**: `tests/roadmap/dispatch/check.sh` accepts only the
  0.14.1/0.15.2/0.16.0 profiles. The step runs on `0.14.1 || 0.15.2 || 0.16.0`. It uses
  only `==`/`&&`/`||`/`!` because `scripts/local-ci-steps.py` and
  `scripts/release-record.py` evaluate conditions with that grammar.

`tests/review/exporter-checks.sh` also checks `AIR2LEAN_REVIEW_ZIG17` and expects
0.16.0's packed-constant export shape there, because packed structs stay integers after 0.16.

## Metadata (I09)

`compatibility.json` lists 0.17.0 first, matching the newest-first order of
`zig-patch/versions.toml` and `supportedVersions`:

| Field | 0.17.0 |
|---|---|
| `status` | `in-qualification` (new field; all other versions are `qualified`) |
| `hosts` | `x86_64-linux`, `aarch64-macos` |
| `source` | `https://ziglang.org/download/0.17.0/zig-0.17.0.tar.xz`, sha256 `b6c7f1728f043700d6529bac980800792f824256a9d2f1839b3d62beed0b8abd` |
| `hook` | `0.17.0/hook.patch` |
| `llvm` | `22` |
| `ci_host_zig` | `https://ziglang.org/download/0.17.0/zig-x86_64-linux-0.17.0.tar.xz`, sha256 `1cbe9df9f27e6b78d14ccbca43b6703a404ef79ef1c463de901d7f088d4e2026` |

Both checksums match `index.json`. They were also confirmed by downloading each tarball
and hashing it on 2026-10-07. `scripts/compat.py check` now also requires a `status`
of `qualified` or `in-qualification` for every version, and requires `zig.default` to be
`qualified`. `scripts/doctor.py` adds a `zig-version-status` note when the selected
version is in qualification. `scripts/support-matrix.py` reads the status, labels
0.17.0 "(in qualification)" in the README/PLAN regions, adds a Status column to
`docs/support-matrix.md`, and checks that `compatibility.json` lists the same versions as
`supportedVersions`.

Version lists updated to include 0.17.0: `scripts/workflow-common.sh` (the
`workflow_version` case), `scripts/local-ci.sh`, `scripts/translate.sh` usage, the CI matrix,
`compatibility.json`, and the README/PLAN prose.
`assurance/target-matrix.json`, `assurance/build-modes.json` and `scripts/accounting.py`
are not on the base branch, so they were not changed.

## Classification of `0.16.0` mentions

Search: `grep -rn '0\.16\.0'` over `*.py *.sh *.json *.toml *.lean *.yml *.md`, excluding
`tests/golden`, `coverage/`, `*/air/`, `.lake` and `.claude`: **681 lines in 205 files**
(after this change).

| Class | Lines | Files | Action |
|---|---:|---:|---|
| (a) version enumeration, this track | 38 | 10 | 0.17.0 added (CI full row and review env, workflow-common/local-ci/translate lists, `compatibility.json` entries, README/PLAN/support-matrix lists, the version-list tests) |
| (a) version enumeration, other tracks | 10 | 5 | left for their owners: `zig-patch/versions.toml`, `zig-patch/README.md` LLVM list (Z1), `Air2Lean/Air/Normalize.lean` `supportedVersions` and `Air2Lean/Main.lean` help (Z3), `docs/coverage.md` inventory list (Z2) |
| (c) default version | 46 | 12 | left on 0.16.0: `AIR2LEAN_ZIG_VERSION:-0.16.0` in check/mutate/translate, `local-ci.sh`'s default, `doctor.py` usage, `zig.default`, `clean-env.sh`, getting-started/README/distribution bootstrap instructions, doctor tests of the default, the five 0.16.0 mutation shard rows, and the "once per run" CI steps on the default row (support matrix, release record) |
| (b) qualified on specific versions | 587 | 178 | left: the evidence and gates are scoped to the versions they were run on |

Class (b) by area: `tests/roadmap` 323 lines/95 files (per-feature qualification gates,
fixtures, provenance and qualified compiler checks such as `dispatch`, `byte-permutation`,
`error-storage`, `thread-tuples`, `progress`, `weak-cas`, `spawn-failure`, `try-pointers`);
`docs` 101/28 (scoped qualification reports and per-version semantics); `.github/workflows/ci.yml`
39 (steps gated to 0.16.0 or 0.15.2/0.16.0); `Air2Lean` 18/7 (per-version
semantics such as `divRt016`, `Check.lean`'s audited fallible-spawn versions and
`TimedCheck`'s retained 0.16.0 profile); `Proofs` 18/15 and `ZigLean` 15/7 (per-version
translation notes); `assurance` 15/2 (float labels `compiler-rt@0.14.1,0.15.2,0.16.0`,
perf budgets); `scripts` 15/7 (`flow-time.sh`, `diff.sh` notes, `normalize-generated.py`
audited versions, `build-guard.py`, `abi-probe.py`, `review-checks.sh` fixtures);
`REVIEW_STRATEGY.md` 12, `tests/*` 11/7, `case-studies` 6/2, `zig-patch` TAGS 5/2, and
historical PLAN/README/ROADMAP/remaining-acceptance rows 9. Extending any of these to 0.17.0 is
qualification work. It needs fresh evidence on 0.17.0, not a list edit.

## Integration

At integration, before CI can pass:

1. Merge the exporter pin (`["0.17.0"]` first, `[ci.host-zig."0.17.0"]`, `zig-patch/0.17.0/hook.patch`),
   `coverage/0.17.0.json`, `supportedVersions` with 0.17.0 first, and CLI help that names 0.17.0.
2. Run `python3 scripts/support-matrix.py generate`. The committed regions here are generated
   from the pre-integration tree.
3. Run `python3 scripts/compat.py check`, `python3 scripts/support-matrix.py check`, and the
   `distribution` and `support-matrix` unittest suites.

The tests find versions by name, derive the hook list from `compatibility.json`, and
read example cells by version column. They pass once those inputs are merged. A
simulation of the merged inputs on this tree passed `compat.py check`, `support-matrix.py generate`,
and both suites.

To qualify 0.17.0 later: set `status` to `qualified`, extend each class (b) gate after
running it on 0.17.0, and then decide whether to move the default and the mutation shards.
