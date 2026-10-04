# Differential outcome accounting

The differential runner preserves its JSONL result files, `TOTAL:` counters and per-function count pins. It additionally writes typed observation sidecars (`<function>.jsonl.outcomes`) and a schema-1 report. Set `AIR2LEAN_DIFF_REPORT` to choose the summary path; the default is `tests/diff/out/report.json`. Case evidence is stored beside it as `<summary>.jsonl`. The report always records `qualified: false`: agreement on these fixtures is not a proof of translation correctness or runtime adequacy.

The Lean producer classifies `Zig.Result` and `Zig.Sched.Out` directly. Source `Except Zig.ErrName` error returns, including optional wrappers, are values tagged `error_return`. Runtime safety constructors are tagged `model_panic`, `illegal`, `unspecified` or `deadlock`. The native producer classifies source error unions before rendering and sends a private typed byte through its child-result pipe. The parent distinguishes returned values, reported native panics and harness failures. Harness allocation failures receive their own tag. This does not change the runtime model or claim that native allocation failures follow the model's policy.

| Comparison status | Meaning |
| --- | --- |
| `value_match`, `error_return_match` | Typed returned values agree, including modeled buffers and live allocation counts. |
| `panic_match` | A reported native panic agrees with the corresponding model safety constructor. |
| `illegal_exclusion`, `unspecified_exclusion` | The model produced that constructor; the native value is excluded from semantic agreement. |
| `search_cap` | The schedule search reached its run cap. |
| `bounded_no_result` | A run returned no result, or an unmatched search contained such a branch. |
| `host_difference` | A declared host-dependent result differs outside the reference Linux x86_64 host. |
| `mismatch` | Comparable typed outcomes disagree. |
| `input_failure`, `native_harness_failure` | An input or harness failure prevents comparison. |
| `skipped` | An example was not selected; the selection record explains host, version or explicit selection constraints. |

`deadlock` remains a distinct model observation even when its comparison status is `mismatch`. The historical `{"diverge":true}` wire field is retained for compatibility, but its typed observation is `bounded_no_result`; scheduler fuel exhaustion does not establish divergence. A concrete matching schedule is a witness despite other bounded branches. An unmatched search with a no-result branch is inconclusive. No matching witness establishes all-schedule agreement.

The legacy counters remain a compatibility projection: `illegal` and `unspecified` share the historical `unspecified` counter. Pinned caps may still give the legacy runner exit zero. The typed counts keep those cases distinct and excluded from mutation detection. The report validates exact sidecar/wire binding, producer tags, row counts and pins; missing, stale, malformed or unsupported metadata causes a setup failure. It does not infer runtime categories from diagnostic messages. Unsupported translator inputs that never reach this runner remain outside this protocol.

Mutation detection requires a failing run with typed semantic mismatch evidence, or an unspecified-count pin change without capped, bounded, host-dependent or setup-failure cases in that function. Cap changes, missing baselines, host exclusions and unsupported setup never count as detections. The old counter-only fallback is retained for isolated legacy mock runners that produce no report; the real differential runner initializes a report before building. Proof mutation gates retain their existing separate baseline/build accounting. This branch does not include later weak-CAS proof-import and mutation-target repairs; integrating those changes must preserve both patches.

`check.sh`, `diff.sh` and `mutate.sh` share default host/version example selection. Explicit `AIR2LEAN_EXAMPLES` selections bypass filtering and may fail setup if unsupported. Mutation selection uses the declared exporter version; callers must align it with the stock native compiler. A host-excluded float mismatch cannot qualify a float mutation on that host.

Reports bound each JSONL record to 8 MiB, combined case count to 100,000 and emitted case evidence to 128 MiB. Summaries contain input/native/model wire hashes, case indices, selected schedule prefix/options, runs/fuel/cap, source fingerprints and actual host/version arguments. Fingerprints cover producer scripts, the runtime, proof/example source files and native test sources; they do not authenticate compiled artifacts, compiler binaries, external libraries or theorem applicability. Schedule data supports investigation, not a new replay command. Run initialization discards stale sidecars and case evidence. Set `AIR2LEAN_MUTATION_REPORT_DIR` to retain separate report directories for differential mutants; otherwise those temporary reports are removed. Retained evidence has per-run bounds, so its total grows with the selected run count.

## Validation

Offline checks, requiring no compiler:

```sh
python3 tests/roadmap/outcome-accounting/test_report.py
bash -n scripts/check.sh scripts/diff.sh scripts/mutate.sh scripts/example-selection.sh
git diff --check
```

The offline suite executes only Python and bounded shell mocks. Lean/Zig producer compilation, real native differential checks, preservation of real pinned counts, selected semantic mutations and Linux reference-host checks require the normal bounded toolchain queue. No such checks have been run by this implementation agent.

After a real `scripts/diff.sh` build, the package checks are:

```sh
(cd tests/diff && lake env lean ../roadmap/outcome-accounting/Check.lean)
(cd tests/diff && lake env lean ../roadmap/outcome-accounting/Search.lean)
```

Run the real differential gate with explicit matching `AIR2LEAN_ZIG`, exporter version and eligible example selection. Retain its report outside build caches. Run selected differential mutations with `AIR2LEAN_MUTATION_REPORT_DIR` after reconciling the later accepted mutation repairs; baseline or setup failures are failures of qualification, not mutation detections. Native version matrices and cross-host validation remain necessary before claiming those scopes passed.
