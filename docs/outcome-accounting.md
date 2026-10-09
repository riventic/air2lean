# Differential outcome accounting

The differential runner preserves its JSONL result files, `TOTAL:` counters and per-function count pins. It additionally writes typed observation sidecars (`<function>.jsonl.outcomes`) and a schema-1 report. Set `AIR2LEAN_DIFF_REPORT` to choose the summary path; the default is `tests/diff/out/report.json`. Case evidence is stored beside it as `<summary>.jsonl`. The report always records `qualified: false`: agreement on these fixtures is not a proof of translation correctness or runtime adequacy.

The Lean producer classifies `Zig.Result` and `Zig.Sched.Out` directly. Source `Except Zig.ErrName` error returns, including optional wrappers, are values tagged `error_return`. Runtime safety constructors are tagged `model_panic`, `illegal`, `unspecified`, `unspecified_timer` (`Zig.Error.unsupportedTimer`, a clock the model lacks), `deadlock` or `trap` (an allowlisted inline-asm fault, ASM-04). The native producer classifies source error unions before rendering and sends a private typed byte through its child-result pipe. The parent distinguishes returned values, reported native panics and harness failures. Harness allocation failures receive their own tag. This does not change the runtime model or claim that native allocation failures follow the model's policy.

| Comparison status | Meaning |
| --- | --- |
| `value_match`, `error_return_match` | Typed returned values agree, including modeled buffers and live allocation counts. |
| `panic_match` | A reported native panic agrees with the corresponding model safety constructor. |
| `trap_match` | A native `SIGFPE` during the tested call agrees with a model `trap` (`panic-policy.tsv`: `SIGFPE` → `trap`). |
| `illegal_exclusion`, `unspecified_exclusion` | The model produced that constructor on an input pinned for it in `tests/diff/<ex>/unspecified.txt` (`<fn> <input_sha256> <count>\|<min>-<max> <reason>`); the native outcome is excluded from semantic agreement. On an unpinned input the case is a `mismatch` (F3). |
| `unspecified_timer_exclusion` | The model threw `Zig.Error.unsupportedTimer` (a clock it lacks); the native value is excluded from semantic agreement. |
| `search_cap` | The schedule search reached its run cap. |
| `bounded_no_result` | A run returned no result, or an unmatched search contained such a branch. |
| `host_difference` | Outside the reference Linux x86_64 host, two returned values differ only in float leaves, and each differing leaf pair satisfies a kind listed for the function in `tests/diff/<ex>/host.txt` (`<fn> <kind>[,<kind>]`): `nan_payload` (both NaN of one format), `zero_sign` (both zero, opposite signs), `libm_ulp` (both finite of one format, at most one ulp apart). The case row records `host_kinds`. A panic, error, exclusion or untyped value difference is a `mismatch` (F3). |
| `mismatch` | Comparable typed outcomes disagree. |
| `input_failure`, `native_harness_failure` | An input or harness failure prevents comparison. |
| `skipped` | An example was not selected; the selection record explains host, version or explicit selection constraints. |

`deadlock` remains a distinct model observation even when its comparison status is `mismatch`. The historical `{"diverge":true}` wire field is retained for compatibility, but its typed observation is `bounded_no_result`; scheduler fuel exhaustion does not establish divergence. A concrete matching schedule is a witness despite other bounded branches. An unmatched search with a no-result branch is inconclusive. No matching witness establishes all-schedule agreement.

The legacy counters remain a compatibility projection: `illegal`, `unspecified` and `unspecified_timer` share the historical `unspecified` counter. Pinned caps may still give the legacy runner exit zero. The typed counts keep those cases distinct and excluded from mutation detection. The report validates exact sidecar/wire binding, producer tags, row counts and pins. Binding compares decoded JSON recursively with exact types: booleans differ from integers, integers differ from floating numbers, signed floating zero is preserved, and object key order is irrelevant. Equivalent float spellings such as `1.0` and `1e0` decode to the same value; lexical number spelling is not retained. The legacy quoted/bare decimal compatibility applies only to a top-level returned payload after binding validation. Native memory bytes must be lowercase hexadecimal; model masks allow hexadecimal and `?` nibbles, with equal even lengths. Unresolved `pp` pointer fragments remain mismatches. Arbitrary glob masks cannot establish memory agreement. The native panic mapping lives in `scripts/panic-policy.tsv` and is loaded once by each consumer; an unknown reported panic remains a mismatch.

Native `native_signal` observations carry the signal's name (`SIGFPE`, `SIGILL`, `SIGSEGV`, `SIGBUS`) as their legacy failure marker. The child
writes checked phase bytes before the tested call and after it returns. Only an exact
call-start marker, a successful pipe read and a wait status for SIGILL, SIGFPE, SIGSEGV
or SIGBUS admit this category. It can be excluded by a model `illegal` or `unspecified`
constructor on a pinned input; it does not establish panic agreement, `SIGFPE` matches only a
model `trap`, and a valid model result is a mismatch.
SIGKILL/SIGTERM and other interruption/resource signals, missing or malformed transport,
pipe errors, and renderer-stage failures remain fatal `native_harness_failure`, even when
the model reports `illegal`. These observations are test evidence, not proof of signal cause.

Missing, stale, malformed or unsupported metadata causes a setup failure. It does not infer runtime categories from diagnostic messages. Unsupported translator inputs that never reach this runner remain outside this protocol.

Mutation detection requires a failing run with typed semantic mismatch evidence, or an unspecified-count pin change without capped, bounded, host-dependent or setup-failure cases in that function. Raw capped/bounded/no-result search metadata blocks pin-change detection even when the selected model constructor is `illegal`; a concrete matching value or panic witness remains a match. Cap changes, missing baselines, host exclusions and unsupported setup never count as detections. The old counter-only fallback is retained for isolated legacy mock runners that produce no report; the real differential runner initializes a report before building. Proof mutation gates retain their existing separate baseline/build accounting. The composed branch retains the weak-CAS proof-import isolation and current mutation-target repairs. Typed scheduler observations flow through the bounded FIFO probes and original DFS fallback; the bounded Linux Zig15/Zig16 checks of the repaired composition passed as recorded below; final composed-source CI remains pending.

`check.sh`, `diff.sh` and `mutate.sh` share default host/version example selection. Explicit `AIR2LEAN_EXAMPLES` selections bypass filtering and may fail setup if unsupported. Mutation selection uses the declared exporter version; callers must align it with the stock native compiler. A host-excluded float mismatch cannot qualify a float mutation on that host.

Reports bound each JSONL record to 8 MiB, combined case count to 100,000 and emitted case evidence to 128 MiB. Summaries contain input/native/model wire hashes, case indices, selected schedule prefix/options, runs/fuel/cap, source fingerprints and actual host/version arguments. Fingerprints cover producer scripts, the runtime, proof/example source files and native test sources; they do not authenticate compiled artifacts, compiler binaries, external libraries or theorem applicability. Replay validates this source context and the selected raw input; it does not authenticate a compiled binary or prove native/model correspondence. Run initialization replaces any old completed summary and discards stale case evidence before compiler/version/selection setup. Validated selection then clears its old sidecars. Setup failure cannot reuse old input-failure sidecars or completed comparison evidence. Set `AIR2LEAN_MUTATION_REPORT_DIR` to retain separate report directories for differential mutants; otherwise those temporary reports are removed. Retained evidence has per-run bounds, so its total grows with the selected run count.

## Bounded schedule enumeration and replay

`tests/diff/Concurrent.lean` is the shared registry used by observed-result matching and the `schedules` executable. It covers the existing Threads, Atomics, Sync, Threadsync and Iogroup examples. It uses their current generated dispatchers, initial memory and runtime scheduler; it introduces no alternate model or partial-order reduction. Version eligibility remains the differential selection's responsibility; explicitly selecting a model entry does not qualify it for a native version.

After the normal differential build creates the libm archive, build the schedule executable and explore one input row:

```sh
(cd tests/diff && lake build schedules)
python3 scripts/schedules.py enumerate --example atomics --function mpRelAcq \
  --input-index 1 --fuel 1000 --node-cap 128 --prefix-cap 4096 --output schedules.json
python3 scripts/schedules.py replay --receipt schedules.json --execution-index 0 --output replay.json
python3 scripts/schedules.py replay --summary tests/diff/out/report.json \
  --example threads --function claimOnce --input-index 1 --output witness.json
```

Input indices start at one; execution indices start at zero. Enumeration follows a deterministic DFS of the model's oracle tree and retains every attempted execution and its distinct typed outcome. Limits are explicit: fuel at most 100,000 scheduler steps per execution, node cap at most 2,000 executions, prefix cap at most 4,096 choices, response at most 64 MiB, and command timeout at most 900 seconds (default 60). Node cap zero is permitted and explores nothing. `truncated`, `node_cap_reached`, `prefix_cap_reached`, `runs`, `choice_count` and `trace_complete` disclose the retained coverage. `exploration_complete` means only that this fuel-bounded oracle tree was traversed without node/prefix truncation. It establishes neither fuel-independent exhaustion, an exhaustive set of program outcomes, native correspondence nor liveness. The historical matching runner still stops at an observed-result witness.

Summary coverage counters for observed matching and bounded enumeration, capped-scope accounting and the reduction statement are described in [schedule-caps.md](schedule-caps.md).

Reproducible failure bundles, and the counterexample/unsolved distinction, are described in [counterexamples.md](counterexamples.md).

Replay requires the complete recorded choice trace, including zero choices, and checks the returned typed kind, wire result and option counts. Missing, extra or out-of-range choices are rejected. An observed matching witness's shorter stored prefix is extended only by the original oracle's default zero choices, to its recorded option count. Capped/unmatched observations and truncated enumeration traces cannot serve as replay witnesses. The Python CLI binds current raw input bytes and runner/runtime source fingerprints before and after execution; stale inputs, source changes or mismatched replay results fail without publishing a new receipt. Receipts always record `qualified: false`. Rebuild the executable after changing generated modules or archives: these source fingerprints do not attest to its build or compiler.

Summaries publish `exact_matches` separately from host differences, illegal/unspecified exclusions and caps. Selection records list each skipped function and `skipped_functions` counts them outside observed `case_count`. `proof_applicability` is explicitly `not_evaluated_by_differential_runner`; `proof_exclusions` lists each selected example's proof source scope as unevaluated. A source fingerprint, replay or exact differential match cannot establish theorem applicability. The separate kernel proof gates remain necessary. [host-accounting.md](host-accounting.md) publishes these fields per version/target, with a headline of exact matches only, and checks the README's legacy-version claims against the runs.

## Validation

Offline checks, requiring no compiler:

```sh
python3 tests/roadmap/outcome-accounting/test_report.py
python3 tests/roadmap/outcome-accounting/test_schedules.py
bash -n scripts/check.sh scripts/diff.sh scripts/mutate.sh scripts/example-selection.sh
git diff --check
```

The offline suite executes only Python and bounded shell mocks. The coordinator has also compiled and exercised the added enumeration/replay core and CLI against the real model executable on Linux with Zig 0.15.2 and 0.16.0, including the plain Lean classification/search/schedule fixtures and native producer boundaries. The full Zig15/Zig16 CI jobs run these checks after the differential build. Earlier package-registration, constructor, record-layout and fixture compilation failures remain failed attempts; the repaired bounded passes are recorded below. Cross-host/full-version matrices, remaining semantic mutations and final composed-source CI remain pending; selected b/g checks retain their separate historical scope below.

After a real `scripts/diff.sh` build, build the new executable before importing its protocol in the package checks:

```sh
(cd tests/diff && lake build schedules)
(cd tests/diff && lake env lean ../roadmap/outcome-accounting/Check.lean)
(cd tests/diff && lake env lean ../roadmap/outcome-accounting/Search.lean)
(cd tests/diff && lake env lean ../roadmap/outcome-accounting/Schedule.lean)
```

Run the real differential gate with explicit matching `AIR2LEAN_ZIG`, exporter version and eligible example selection. Retain its report outside build caches. Run selected differential mutations with `AIR2LEAN_MUTATION_REPORT_DIR` after reconciling the later accepted mutation repairs; baseline or setup failures are failures of qualification, not mutation detections. Native version matrices and cross-host validation remain necessary before claiming those scopes passed.

## Native producer boundary regressions

`Native.zig` plus `test_native.py` exercise the buffered valid-row prefix before malformed input, post-call renderer allocation failure, mutation ineligibility and the unchanged tested-source panic category. The renderer fixture passes a zero-capacity fixed-buffer allocator only to result rendering; it does not alter the tested function's allocator or allocate large amounts of memory. Compile and run the fixture for each native harness version being qualified:

```sh
"$AIR2LEAN_ZIG" build-exe -OReleaseSafe -lc --dep common \
  -Mroot=tests/roadmap/outcome-accounting/Native.zig \
  -Mcommon=tests/diff/common.zig -femit-bin="$NATIVE_FIXTURE_BINARY"
python3 tests/roadmap/outcome-accounting/test_native.py "$NATIVE_FIXTURE_BINARY"
```

The Python wrapper executes only the supplied precompiled binary in a temporary directory with a five-second timeout. It verifies the second metadata record is the malformed-input failure, runs real native renderer evidence through report accounting, requires zero mutation eligibility, and checks the tested function's panic still has the native-panic tag. Offline tests check that this verifier rejects a lost metadata prefix and a renderer failure mislabeled as a panic.

## Recorded local evidence

The coordinator's repaired Linux Zig 0.15.2 and 0.16.0 runs each recorded 1,020 native/model matches, 300 typed `illegal_exclusion` cases and zero mismatches. The 300 exclusions appear as `unspecified` in the legacy counters; they are not demonstrated result matches. Both versions passed the real `schedules` executable build, plain Lean classification/search/schedule fixtures, finite enumeration and exact replay, fuel-zero no-result and node-zero cap checks, a source-bound observed witness replay, and native producer valid-prefix/renderer-failure/source-panic checks. These checks establish neither exhaustive program outcomes, divergence, all-schedule correspondence nor a theorem about a proof domain. Reports continue to record `qualified: false`; source fingerprints do not authenticate the compiler or executable build.

Zig15 initially rejected AppleDouble snapshot sidecars as invalid skipped-function names. The coordinator removed only identified archive metadata, verified all 1,130 tracked members byte-for-byte, and rebuilt the typed report from the exact retained native/model rows under unchanged production source. The cleaned source archive SHA-256 is `4619b46bada17df9940fe5b8ac5bffa29395a437b5f627457669408b4b0c5e2b`; no validator relaxation or new differential comparison was used. The version passes are separate from the historical default-run and mutation receipts below, and do not qualify a future source composition. Final CI remains pending.

The local summaries are `/private/tmp/air2lean-outcomes-local15-passed/report.json` (SHA-256 `22eac29feafc9949ef880250c72918bb4f534f1b26a6dcf54e593c9ac9d0d1fa`) and `/private/tmp/air2lean-outcomes-local16-passed/report.json` (SHA-256 `a96189f52542df0fa493da54c2f005d5b2f4d677eeac1eaadb9b8e7bdee8c6e3`); each has adjacent `report.json.jsonl` case evidence. Both summaries are complete, have zero setup failures and pin violations, retain zero mutation eligibility, and record proof applicability as `not_evaluated_by_differential_runner`. These local receipts retain their checked source scope and do not attest to a later composition.

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

Before calling the tested function, only the forked child resets the inherited Zig crash dispositions for FPE/ILL/SEGV/BUS to their defaults. This preserves the original fault signal instead of Zig's debug handler converting it into ABRT; renderer faults still occur after the return marker and remain harness failures. Explicit ABRT also remains a harness failure. This runner does not qualify source functions that depend on custom signal handlers or inherited signal masks.

Parent output-buffer allocation errors also close the result reader, terminate the still-owned child and reap it before propagating the error. Once the normal wait has reaped the child, later allocation errors do not signal its former PID. The parent-OOM regression injects a failing allocator into a temporary producer copy, keeps the tested call blocked, and requires no child to remain waitable; it leaves repository sources and the production allocator unchanged. ROOT executed the native boundary and parent-OOM regressions on producer revision `a5be97b064bbc8172b156bf5189e279736da5048` with both Zig15 and Zig16; both passed. The same revision completed the full Zig15 generation command (52 jobs) and differential command with exit zero. Its complete typed report contains 87,004 cases: 80,060 value matches, 892 error-return matches, 4,975 panic matches, 497 illegal exclusions and 580 unspecified exclusions. ROOT inspected the original pins and confirmed no pin failures. Full Zig16 differential testing, all five mutation shards, and the subsequent public C06 composition remain pending; these fixture results do not establish source adequacy or exhaustive schedule coverage.

## Selected mutation evidence

At source revision `347bfd5fd4f6fe598763c87777a9e976b342c0c3`, the coordinator ran only differential mutants b and g on Darwin arm64 with stock/legacy Zig16 and the explicit `basic slices` selection. The isolated validation passed in 215.5 seconds with 791.8 MiB sampled peak memory; the restored healthy selection also passed.

| Run | Cases | Value matches | Panic matches | Mismatches | Mutation eligible |
| --- | ---: | ---: | ---: | ---: | ---: |
| b | 2,400 | 1,663 | 571 | 166 | 166 |
| g | 6,003 | 4,787 | 1,028 | 188 | 188 |
| Restored healthy | 8,403 | 6,638 | 1,765 | 0 | 0 |

All three reports record `complete: true`, `qualified: false`, zero setup failures and no pin violations. Exactly b/g were detected. Before/exit snapshots agree on source hashes, Git modes, filesystem modes and tracked symlink identity; the coordinator independently rehashed all 40/105/145 retained file entries and all three summary hashes.

Evidence is local at `/private/tmp/air2lean-outcome-347-selected-mutants-v2`. The frozen validation script SHA-256 is `47154532bd6e0f68e3166dffdee64d9e689ad9ec622a1cf5190b5fccc9c83bb3`; b/g/healthy summary hashes are respectively `0382181de019044006ff514b6a4155afdf13cf43384f059f5cdbd24bbbd7589f`, `88e55f629c3a760a55cf045acfa10bcf3493385c73a96688731508ddeba86b6d` and `f97d9e058cbf69a872ae04e9243cd0bd3114e2fe7d9b2661bfaec3453f92b11e`. The earlier pre-toolchain snapshot failure remains separate evidence. Full Linux CI, the full Zig15 differential matrix, remaining mutants and final stacked FIFO compatibility remain pending; these selected checks establish no universal correspondence claim.
