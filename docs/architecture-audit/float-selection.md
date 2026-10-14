# Finding: differential result depends on the example selection (stale link, under-reported totals)

Class: SOUNDNESS of the differential evidence (two defects). Status: fixed. The float model is
correct. No premise and no upstream report are needed.

## Report

On aarch64-macos with Zig 0.16.0 (stock `AIR2LEAN_ZIG=~/.cache/air2lean/host-0.16.0/zig`, the
CAS-patched zig-air, `AIR2LEAN_CAS_DIR` set, `AIR2LEAN_CI=1 AIR2LEAN_DIFF=1`):

- `AIR2LEAN_EXAMPLES=floatops scripts/check.sh`: rc 0, `TOTAL floatops: ok=38063 ... mismatch=0`.
- `scripts/check.sh` (every example): rc 1, `TOTAL floatops: ok=36632 ... mismatch=0 host=1431`,
  and 1407 `MISMATCH (typed)` lines (`op80` 661, `op128` 746), all for `@sin`, `@cos` and `@tan`
  (`sel` 18, 19, 20). The model's `f80` result had its low 11 mantissa bits zeroed
  (native `0x3ffea2f9ffb0be2b88f9`, model `0x3ffea2f9ffb0be2b8800`), and subnormal arguments gave
  zero (native `0x00007fffffffffffffff`, model `0x00000000000000000000`). Every counter line still
  said `mismatch=0`: `TOTAL: ok=77394 fail_match=4922 unspecified=2463 capped=0 mismatch=0 host=1431`.

## Defect 1: the model side ran a stale executable (selection-dependent result)

`tests/diff/lakefile.toml` linked the libm and asm archives that `scripts/diff.sh` builds with the
stock Zig through `moreLinkArgs`. A path there is a linker flag, not a build input: the trace of
`difftest`, which is also its key in Lake's artifact cache, did not depend on the archives' content.
`scripts/diff.sh` deleted the old binary before `lake build difftest`, but under `scripts/cas.py run`
(`LAKE_ARTIFACT_CACHE`, `LAKE_RESTORE_ARTIFACTS`) Lake restored the executable from the shared cache
for the same Lean inputs instead of linking it again.

The restored binary (artifact `552a7402ea1f599c`) came from an earlier all-examples `check.sh` run
on the same Zig 0.16.0 check tree whose native side was a stock Zig 0.15.2: that run linked
`difftest` against Zig 0.15.2's compiler-rt (`__sinx`, `cosx`, `tanx` and the `f128` routines
evaluate in `f64`, flushing subnormals) and then failed the `check_models` gate, which runs after
the build so that a cache-warming run still builds `tests/diff` (`soft-float-darwin.md`). The Lean
inputs of `difftest` depend on which `Proofs/<Ex>/Gen.lean` the check tree replaces, that is on the
selected examples: an all-examples run (Floatconv and Floatops replaced) hit the poisoned entry, a
floatops-only run (Floatops replaced) had another key and linked afresh. Hence the result depended
on the selection, and the "model" results were Zig 0.15.2's libm, not the 0.16.0 one.

Counterexample (a scratch Lake package, Lean 4.34.0, with the artifact-cache environment of
`scripts/cas.py run`): an executable `m` calling `@[extern "xval"]`, linked with
`moreLinkArgs = ["./out/x.a"]`. Build with `x.a` returning 1, replace `x.a` by one returning 2,
delete the binary, build again: `m` prints 1. With `[[input_file]] path = "out/x.a"` and
`moreLinkObjs` instead it prints 2 (and 1 again for the first archive, restored from the cache).

Fix (one mechanism): every archive the model side links is an `[[input_file]]` of
`tests/diff/lakefile.toml`, linked through `moreLinkObjs` (`difftest`: libm and asm, `schedules`:
libm). Its content is part of each executable's trace and cache key, so a changed archive relinks
and the cache can only restore an executable linked against the same bytes. The binary deletion in
`scripts/diff.sh` and in the CI step before `lake build schedules` is gone.

## Defect 2: the counter lines under-reported mismatches (fail-open accounting)

`scripts/diff.sh` had its own comparison loop beside the typed classifier `scripts/diff-report.py`.
On a host other than x86_64-linux the shell counted every disagreement of two returned values of a
function listed in `tests/diff/<ex>/host.txt` as `host`, without checking the listed kinds
(`nan_payload`, `zero_sign`, `libm_ulp`). The typed classifier checks each differing float and
found 1407 mismatches, so the run exited 1, but every per-function, per-example and `TOTAL:` line
was the shell's and said `mismatch=0`. The two classifiers also disagreed elsewhere: equal values
of different kinds (an error return against a value) were `ok` in the shell's counters and in the
summary's `legacy_counts` while the typed status was `mismatch`.

Fix (one mechanism): `scripts/diff-report.py` is the only classifier. The shell loop is removed;
`diff-report.py compare` prints the counter lines, and a case whose typed status is `mismatch` is
counted as `mismatch` there and in `legacy_counts`, never as `ok`, `unspecified` or `host`. The
per-input exclusion pins still count the observed exclusions, so an unpinned exclusion is both a
mismatch and a pin violation, as before.

## Regressions

`tests/roadmap/outcome-accounting/test_report.py`:

- `LinkedArchives.test_cached_executable_follows_the_archive` (selection independence): builds a
  scratch package with `tests/diff/lakefile.toml`'s own `input_file` tables and `difftest` link
  fields under the artifact-cache environment, and requires archives returning 1, 2, 1 to give
  1, 2, 1. With the old `moreLinkArgs` it gives 1, 1, 1.
  `test_every_executable_links_the_archives_as_traced_inputs` checks that no executable has
  `moreLinkArgs` and that the input files are exactly the archives `scripts/diff.sh` copies.
- `Outcomes.test_every_typed_mismatch_is_counted_in_the_totals` (accounting): runs the
  comparison step of `scripts/diff.sh` as on Darwin-arm64 with every host kind allowed, on the two
  `f80` cases above, an error return against a value and an unpinned exclusion; each must exit 1,
  print a `MISMATCH (typed)` line and count `mismatch=1` in the function, example and `TOTAL:`
  lines. A zero-sign difference stays `host=1` with exit 0.
- `scripts/review-checks.sh` runs the same comparison step on a healthy, a mismatching and a
  truncated output.

With the fix, on the host and configuration of the report: `AIR2LEAN_EXAMPLES=floatops` and every
example both give `TOTAL floatops: ok=38063 fail_match=23 unspecified=1539 capped=0 mismatch=0`
(see the pull request for the full logs).
