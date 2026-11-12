# Zig 0.17.1 in CI and release metadata

Zig 0.17.1 (released 2026-11-02, LLVM 22) is **qualified**: `qualification/0.17.1.json`
(from 0.17.0, `scripts/qualify-upgrade.py check` exit 0) records its upgrade obligations as
passed, and `compatibility.json` gives it `status: qualified`. 0.17.1 replaced 0.17.0
(released 2026-10-01, qualified from 0.16.0) on 2026-11-12: the patch release exports the same
AIR for every example except generic-instance numbers and std `decl_line`s, so the 0.17.0
translations, goldens and proofs carried over; the 0.17.0 record is in the git history. Zig 0.17.1 is the default
(`compatibility.json` `zig.default`, read through `scripts/compat.py default`), and every gate that is qualified only on particular versions stays on those versions
(the 0.17.1 job does not run them). This page covers the CI,
metadata and version-list part of the 0.17.1 work. The exporter pin and hook
(`zig-patch/`), the coverage inventory (`coverage/0.17.1.json`), the translator's
`supportedVersions` and CLI help, and the example and std-model version lists are owned
by the other 0.17.1 tracks.

## CI matrix

| Row | Decision |
|---|---|
| `0.17.1` full job | Added (`full: true`, every example `scripts/example-selection.sh` selects for 0.17.1). It runs every gate that applies to every version: the compiler inventory check, the float probe, the patched compiler build, golden AIR/translation/diff (`scripts/check.sh`), proofs, VCs, exporter review (`AIR2LEAN_REVIEW_ZIG17`), allocation policy, progress kernel and `no-sorry`. |
| Once-per-run parts and mutation shards | Run on `zig.ci_once` (0.16.0), not on the default: their steps gate on the version they were qualified on and the T06 build-mode records exist for it. Moving them to 0.17.1 needs fresh evidence and is a separate decision. |
| 0.16.0 / 0.15.2 / 0.14.1 rows | Unchanged. |

The 0.17.1 job is a blocking job, not `continue-on-error`. Its inputs are the exporter pin
and hook, `coverage/0.17.1.json`, golden overrides under `tests/golden/0.17.1/` where AIR or
translations differ, and `tests/floatprobe/expected.0.17.1.txt`.

Steps gated to one version (mostly `matrix.zig == '0.16.0'`, plus `0.15.2 || 0.16.0` for
the proof API and typed outcomes) stay as they are. Their source/native qualification
is version-specific (class b below), so they do not run on 0.17.1. One step ran on every
row but rejects unknown versions. Its condition now lists the qualified versions:

- **Loop-switch dispatch regressions**: `tests/roadmap/dispatch/check.sh` accepts only the
  0.14.1/0.15.2/0.16.0 profiles. The step runs on `0.14.1 || 0.15.2 || 0.16.0`. It uses
  only `==`/`&&`/`||`/`!` because `scripts/local-ci-steps.py` and
  `scripts/release-record.py` evaluate conditions with that grammar.

`tests/review/exporter-checks.sh` also checks `AIR2LEAN_REVIEW_ZIG17` and expects
0.16.0's packed-constant export shape there, because packed structs stay integers after 0.16.

## Metadata (I09)

`compatibility.json` lists 0.17.1 first, matching the newest-first order of
`zig-patch/versions.toml` and `supportedVersions`:

| Field | 0.17.1 |
|---|---|
| `status` | `qualified` (was `in-qualification` until the qualification record passed; `zig.default` is 0.17.1; `zig.ci_once` stays 0.16.0) |
| `hosts` | `x86_64-linux`, `aarch64-macos` |
| `source` | `https://ziglang.org/download/0.17.1/zig-0.17.1.tar.xz`, sha256 `1e89bf06610b769a8c77676c6c8d54b093a0db60f4891f2f91014829012f0e24` |
| `hook` | `0.17.1/hook.patch` |
| `llvm` | `22` |
| `ci_host_zig` | `https://ziglang.org/download/0.17.1/zig-x86_64-linux-0.17.1.tar.xz`, sha256 `3581863e3cbcfd0fce0efc682ce7e9e93da96668a977791d356a26d2a7e9b17a` |

Both checksums match `index.json`. They were also confirmed by downloading each tarball
and hashing it on 2026-11-12 (the build host's sha256-checked fetch). `scripts/compat.py check` now also requires a `status`
of `qualified` or `in-qualification` for every version, and requires `zig.default` to be
`qualified`. `scripts/doctor.py` adds a `zig-version-status` note when the selected
version is `in-qualification` (no pinned version is at present). `scripts/support-matrix.py`
reads the status, labels a version in qualification "(in qualification)" in the README/PLAN
regions, adds a Status column to
`docs/support-matrix.md`, and checks that `compatibility.json` lists the same versions as
`supportedVersions`.

Version lists updated to include 0.17.1: `scripts/workflow-common.sh` (the
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
| (a) version enumeration, this track | 38 | 10 | 0.17.1 added (CI full row and review env, workflow-common/local-ci/translate lists, `compatibility.json` entries, README/PLAN/support-matrix lists, the version-list tests) |
| (a) version enumeration, other tracks | 10 | 5 | left for their owners: `zig-patch/versions.toml`, `zig-patch/README.md` LLVM list (Z1), `Air2Lean/Air/Normalize.lean` `supportedVersions` and `Air2Lean/Main.lean` help (Z3), `docs/coverage.md` inventory list (Z2) |
| (c) default version | 46 | 12 | moved to 0.17.1 (one source: `zig.default`, read by `scripts/compat.py default`; `scripts/version-literals.py` rejects a default literal): check/mutate/translate, `local-ci.sh`, `doctor.py`, `clean-env.sh`; the rest was left on 0.16.0 (getting-started/README/distribution bootstrap instructions, doctor tests of the default, the five 0.16.0 mutation shard rows, and the "once per run" CI steps on the default row (support matrix, release record) |
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
historical PLAN/README/ROADMAP/remaining-acceptance rows 9. Extending any of these to 0.17.1 is
qualification work. It needs fresh evidence on 0.17.1, not a list edit.

## Integration

The 0.17.1 inputs (exporter pin, `coverage/0.17.1.json`, `supportedVersions`, CLI help) are
merged. `python3 scripts/compat.py check`, `python3 scripts/support-matrix.py check` and the
`distribution` and `support-matrix` unittest suites pass on the committed tree. After a change to
the version metadata, run `python3 scripts/support-matrix.py generate` to refresh the committed
README/PLAN/support-matrix regions.

0.17.1 is qualified (`status: qualified`, `qualification/0.17.1.json`). Still open: extending each
class (b) gate after running it on 0.17.1, and the decision whether to move the default and the
mutation shards.

## Probe contracts (0.17.1)

`scripts/abi-probe.py observe` selects `tests/roadmap/abi-probes/<version>/<profile>.json` for
the stock compiler's `zig version`. The 0.17.1 contracts were recorded by running the probe with
stock Zig 0.17.1 (checksums from `index.json`): aarch64-macos natively, aarch64-linux in a
`linux/arm64` container, and x86_64-linux in a `linux/amd64` container (Rosetta; ReleaseFast, a
[build mode](build-modes.md) the probe only observes, ran without the `bss_size overflow` that 0.14.1 hit). Layouts, offsets and values equal
0.16.0's. The Linux contracts differ only in `zig_version`; the macOS ones also in LLVM 22's
apple_m1 feature names. `tests/floatprobe/expected.0.17.1.txt` comes from the x86_64-linux
container run: the same two `f128 sqrt` lines as 0.16.0's override.
