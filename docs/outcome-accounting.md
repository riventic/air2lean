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

The legacy counters remain a compatibility projection: `illegal` and `unspecified` share the historical `unspecified` counter. Pinned caps may still give the legacy runner exit zero. The typed counts keep those cases distinct and excluded from mutation detection. The report validates exact sidecar/wire binding, producer tags, row counts and pins. Binding compares decoded JSON recursively with exact types: booleans differ from integers, integers differ from floating numbers, signed floating zero is preserved, and object key order is irrelevant. Equivalent float spellings such as `1.0` and `1e0` decode to the same value; lexical number spelling is not retained. The legacy quoted/bare decimal compatibility applies only to a top-level returned payload after binding validation. Native memory bytes must be lowercase hexadecimal; model masks allow hexadecimal and `?` nibbles, with equal even lengths. Unresolved `pp` pointer fragments remain mismatches. Arbitrary glob masks cannot establish memory agreement. The native panic mapping lives in `scripts/panic-policy.tsv` and is loaded once by each consumer; an unknown reported panic remains a mismatch.

Missing, stale, malformed or unsupported metadata causes a setup failure. It does not infer runtime categories from diagnostic messages. Unsupported translator inputs that never reach this runner remain outside this protocol.

Mutation detection requires a failing run with typed semantic mismatch evidence, or an unspecified-count pin change without capped, bounded, host-dependent or setup-failure cases in that function. Raw capped/bounded/no-result search metadata blocks pin-change detection even when the selected model constructor is `illegal`; a concrete matching value or panic witness remains a match. Cap changes, missing baselines, host exclusions and unsupported setup never count as detections. The old counter-only fallback is retained for isolated legacy mock runners that produce no report; the real differential runner initializes a report before building. Proof mutation gates retain their existing separate baseline/build accounting. The composed branch retains the weak-CAS proof-import isolation and current mutation-target repairs. Typed scheduler observations flow through the bounded FIFO probes and original DFS fallback; qualification of this composition remains pending.

`check.sh`, `diff.sh` and `mutate.sh` share default host/version example selection. Explicit `AIR2LEAN_EXAMPLES` selections bypass filtering and may fail setup if unsupported. Mutation selection uses the declared exporter version; callers must align it with the stock native compiler. A host-excluded float mismatch cannot qualify a float mutation on that host.

Reports bound each JSONL record to 8 MiB, combined case count to 100,000 and emitted case evidence to 128 MiB. Summaries contain input/native/model wire hashes, case indices, selected schedule prefix/options, runs/fuel/cap, source fingerprints and actual host/version arguments. Fingerprints cover producer scripts, the runtime, proof/example source files and native test sources; they do not authenticate compiled artifacts, compiler binaries, external libraries or theorem applicability. Schedule data supports investigation, not a new replay command. Run initialization replaces any old completed summary and discards stale case evidence before compiler/version/selection setup. Validated selection then clears its old sidecars. Setup failure cannot reuse old input-failure sidecars or completed comparison evidence. Set `AIR2LEAN_MUTATION_REPORT_DIR` to retain separate report directories for differential mutants; otherwise those temporary reports are removed. Retained evidence has per-run bounds, so its total grows with the selected run count.

## Validation

Offline checks, requiring no compiler:

```sh
python3 tests/roadmap/outcome-accounting/test_report.py
bash -n scripts/check.sh scripts/diff.sh scripts/mutate.sh scripts/example-selection.sh
git diff --check
```

The offline suite executes only Python and bounded shell mocks. Lean/Zig producer compilation, real native differential checks, preservation of real pinned counts, selected semantic mutations and Linux reference-host checks require the normal bounded toolchain queue. No such checks have been run by this implementation agent. Coordinator attempts compiled the selected native harnesses and the new Outcome module, then exposed package-registration, constructor and record-layout build failures. Those failures remain recorded as failures. A later repaired default Zig16 producer/report run passed; its exact scope is recorded below. Cross-host/version matrices and remaining semantic mutations remain pending; selected b/g checks are recorded below.

After a real `scripts/diff.sh` build, the package checks are:

```sh
(cd tests/diff && lake env lean ../roadmap/outcome-accounting/Check.lean)
(cd tests/diff && lake env lean ../roadmap/outcome-accounting/Search.lean)
```

Run the real differential gate with explicit matching `AIR2LEAN_ZIG`, exporter version and eligible example selection. Retain its report outside build caches. Run selected differential mutations with `AIR2LEAN_MUTATION_REPORT_DIR` after reconciling the later accepted mutation repairs; baseline or setup failures are failures of qualification, not mutation detections. Native version matrices and cross-host validation remain necessary before claiming those scopes passed.

## Native producer boundary regressions

`Native.zig` plus `test_native.py` exercise the buffered valid-row prefix before malformed input, post-call renderer allocation failure, mutation ineligibility and the unchanged tested-source panic category. The renderer fixture passes a zero-capacity fixed-buffer allocator only to result rendering; it does not alter the tested function's allocator or allocate large amounts of memory. The native fixture has not been executed by this implementation agent. Root's serialized queue should compile and run it for each claimed native harness version:

```sh
"$AIR2LEAN_ZIG" build-exe -OReleaseSafe -lc --dep common \
  -Mroot=tests/roadmap/outcome-accounting/Native.zig \
  -Mcommon=tests/diff/common.zig -femit-bin="$NATIVE_FIXTURE_BINARY"
python3 tests/roadmap/outcome-accounting/test_native.py "$NATIVE_FIXTURE_BINARY"
```

The Python wrapper executes only the supplied precompiled binary in a temporary directory with a five-second timeout. It verifies the second metadata record is the malformed-input failure, runs real native renderer evidence through report accounting, requires zero mutation eligibility, and checks the tested function's panic still has the native-panic tag. Offline tests check that this verifier rejects a lost metadata prefix and a renderer failure mislabeled as a panic.

## Recorded local evidence

At source revision `8ab1718303e6b6e3ca507e480d94ac41b43433cf`, the coordinator ran the default Zig 0.16.0 differential selection on Darwin arm64. The full native/model/report gate passed in 175.3 seconds with 665.5 MiB sampled peak memory. Its report is complete, has zero setup failures, no pin violations, zero mismatches and zero mutation eligibility. It continues to record `qualified: false`.

| Typed status | Cases |
| --- | ---: |
| `value_match` | 78,159 |
| `error_return_match` | 890 |
| `panic_match` | 4,975 |
| `host_difference` | 760 |
| `illegal_exclusion` | 497 |
| `unspecified_exclusion` | 580 |
| Total observed cases | 85,861 |

The 84,024 exact returned-value/panic matches exclude the 1,837 host/illegal/unspecified cases. Two whole examples were skipped: x86-only `asm` on arm64 and version-ineligible `threadsync` under Zig16. These exclusions and skips do not qualify those semantics or count as mutation detections. Linux reference-host full CI and a full Zig15 differential/report run remain pending.

The source-bound local summary is `/private/tmp/air2lean-outcome-8ab-default16-report.json` (SHA-256 `7ff7e43ca6e3ccd74efe3779dfa1e9187a3fe7e84a290a314b8a4e22dfd925b7`); case evidence is the adjacent `.jsonl` file. The coordinator log is `/opt/dev/air2lean/.lake/review-resume/roadmap/outcome-8ab-default16-typed.log` (SHA-256 `efd86c537930a54e346887d38f899b6ba44653b5173eaf4573da4fce1175c9cf`). These local paths are evidence locations, not portable artifacts or compiler-authentication claims.

At producer revision `1b5cdde53ac95c3addf16abf41c39410c60934a1`, the coordinator separately compiled and ran the deterministic producer regressions with native Zig15 and Zig16. Both passed the valid metadata prefix, malformed-input failure index, renderer-only allocation-failure classification, zero mutation eligibility and tested-source panic checks. Their logs are `outcome-1b5c-native15.log` and `outcome-1b5c-native16.log` under the same coordinator log directory; both have SHA-256 `1efaec9d4128cd6985be80972d91119b5848b8d948d875a423cb1fda2260b415`. This is narrow failure-boundary evidence, separate from the default Zig16 full run and the pending full Linux/version matrix.

## Selected mutation evidence

At source revision `347bfd5fd4f6fe598763c87777a9e976b342c0c3`, the coordinator ran only differential mutants b and g on Darwin arm64 with stock/legacy Zig16 and the explicit `basic slices` selection. The isolated validation passed in 215.5 seconds with 791.8 MiB sampled peak memory; the restored healthy selection also passed.

| Run | Cases | Value matches | Panic matches | Mismatches | Mutation eligible |
| --- | ---: | ---: | ---: | ---: | ---: |
| b | 2,400 | 1,663 | 571 | 166 | 166 |
| g | 6,003 | 4,787 | 1,028 | 188 | 188 |
| Restored healthy | 8,403 | 6,638 | 1,765 | 0 | 0 |

All three reports record `complete: true`, `qualified: false`, zero setup failures and no pin violations. Exactly b/g were detected. Before/exit snapshots agree on source hashes, Git modes, filesystem modes and tracked symlink identity; the coordinator independently rehashed all 40/105/145 retained file entries and all three summary hashes.

Evidence is local at `/private/tmp/air2lean-outcome-347-selected-mutants-v2`. The frozen validation script SHA-256 is `47154532bd6e0f68e3166dffdee64d9e689ad9ec622a1cf5190b5fccc9c83bb3`; b/g/healthy summary hashes are respectively `0382181de019044006ff514b6a4155afdf13cf43384f059f5cdbd24bbbd7589f`, `88e55f629c3a760a55cf045acfa10bcf3493385c73a96688731508ddeba86b6d` and `f97d9e058cbf69a872ae04e9243cd0bd3114e2fe7d9b2661bfaec3453f92b11e`. The earlier pre-toolchain snapshot failure remains separate evidence. Full Linux CI, the full Zig15 differential matrix, remaining mutants and final stacked FIFO compatibility remain pending; these selected checks establish no universal correspondence claim.
