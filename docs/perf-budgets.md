# Translation and proof performance budgets

Status: **pending**. The workload suite, recorder, baseline derivation and
regression gate exist. No real-module baseline has been recorded yet, so
`assurance/perf-budgets.json` has `"status": "pending"` and every workload has
`"budget": null`. Until a baseline is committed, the gate reports `pending` and
cannot catch a regression.

## Workloads

`assurance/perf-budgets.json` lists representative real modules. Each one is a
committed golden AIR set, the example's committed proof modules, and a reference
translation (`reference_gen`).

Golden AIR folders are comparison artifacts. `scripts/check.sh` compares fresh dumps
against them after normalization, so a shared `tests/golden/<ex>/air` folder plus a
`tests/golden/<version>/<ex>/air` overlay can mix Zig versions and profile schemas.
The translator rejects mixed sets ("mixed AIR profiles"). Each workload therefore
lists only folders that form one uniform set: one `zig_version`, schema and profile,
declared as `air_zig_version`. `validate` (in CI) and `record` both refuse a mixed
or mismatched set.

| Workload | AIR | Reference translation | Why |
| --- | --- | --- | --- |
| `basic` | shared (0.15.2) | `Proofs/Basic/Gen.lean` | small scalar functions, several proof modules |
| `slices` | shared + 0.15.2 overlay | `tests/golden/0.15.2/slices/Gen.lean` | slice/pointer memory model, separation proofs |
| `layout` | shared (0.16.0) | `Proofs/Layout/Gen.lean` | largest AIR set (51 files), struct/error-union layout |
| `vectors` | shared (0.16.0) | `Proofs/Vectors/Gen.lean` | SIMD lanes (31 files) |
| `variants` | shared (0.15.2) | `Proofs/Variants/Gen.lean` | tagged unions, optionals |
| `floatops` | shared (0.15.2) | `tests/golden/0.15.2/floatops/Gen.lean` | floats with `--float-semantics compiler-rt` |
| `threadsync` | shared (0.15.2) | `tests/golden/0.15.2/threadsync/Gen-darwin.lean` | thread/mutex/wait-group models, concurrency proofs |

The golden AIR is legacy schema 11 (no target profile), so the translation step does
not depend on the host. The proof phases build the committed `Proofs/<Ex>` modules
(the reference-host 0.16.0 translation where it differs from the golden AIR). Those
modules are proof workloads, not outputs of the measured translation.

## Phases

`scripts/perf-budgets.py record` measures, per workload:

| Phase | Measured | Source |
| --- | --- | --- |
| `parse`, `normalize`, `check`, `emit` | wall time, median of warm runs | `air2lean --timing-json` |
| `translate.cold` | wall time, peak RSS of the first translator process | `wait4` |
| `translate.warm` | median wall, max peak RSS of `--repeat` further runs | `wait4` |
| `elaborate` | `lake env lean` on the freshly emitted Lean | `wait4` |
| `proof.cold` | `lake build` of the example's proof modules after deleting only their build outputs | `wait4` |
| `proof.warm` | the same build again (up-to-date trace check) | `wait4` |

It also records the emitted file's size and SHA-256, and `matches_reference`.
`matches_reference` means the definitions are byte-identical to `reference_gen`,
ignoring only the first-line `-- air2lean-profile:` record, as in
`scripts/normalize-generated.py`. A workload fails if repeated runs emit different
bytes. `baseline` refuses a workload whose output does not match its reference.

`air2lean --timing-json PATH` writes `{"schema": "air2lean-timing/1", "files",
"functions", "input_bytes", "output_bytes", "phases_ns": {read, renumber, parse,
normalize, check, emit, write}}` after a successful run. The path must differ from
`-o`. Times are monotonic
nanoseconds summed over files; `check` includes the program-level checks. The flag
only observes the stages. Pure stages run in the same order and the Lean output is
unchanged. `tests/roadmap/perf-budgets/timing_cli.py` (built translator only) checks
on every workload that output is byte-identical with and without the flag, and
that it matches the reference translation.

Limits:
- Peak RSS is the kernel high-water mark of the largest single process in a step,
  including reaped descendants (`lake` → `lean`). It is not a sum.
  `scripts/build-guard.py` reports the sampled sum.
- "Cold" proof builds remove only the selected modules' `.olean`/`.ilean`/trace/IR
  outputs. `ZigLean` and other dependencies stay built.
- `translate.cold` is the first process start of the run. The OS file cache is not
  flushed.
- Times depend on the host. A budget applies only on its `reference_platform`
  (system and machine). The gate reports `platform-mismatch` elsewhere.

## Recording (heavy; one serial lane)

Run the whole suite once under the shared build lock (`docs/build-budgets.md`).
The guard sets `LEAN_NUM_THREADS=1`, and `record` refuses to run without it. Start
from a clean tracked tree:

```sh
export AIR2LEAN_BUILD_LOCK="$HOME/.cache/air2lean/build.lock"
python3 scripts/build-guard.py --cwd "$PWD" --profile perf-budgets --phase proof \
  --cache unspecified --timeout 14400 --rss-mib 12288 \
  --report /tmp/air2lean-perf-guard.json --log /tmp/air2lean-perf-guard.log \
  -- python3 scripts/perf-budgets.py record --out /tmp/air2lean-perf.json
python3 tests/roadmap/perf-budgets/timing_cli.py
python3 scripts/perf-budgets.py baseline --measurement /tmp/air2lean-perf.json
python3 scripts/perf-budgets.py gate --measurement /tmp/air2lean-perf.json
```

`record` first runs `lake build ZigLean air2lean` (`--no-build` skips it). It writes
the measurement JSON and a step log next to it (`.log`). `--workload ID`
(repeatable), `--repeat N` (default 3), `--skip-elaborate` and `--skip-proof`
narrow a run. A gate run with skipped phases fails `missing-phase` against a full
baseline.

`baseline` refuses a measurement from a dirty tracked tree, with failed workloads,
with skipped phases (`--skip-elaborate`/`--skip-proof`), or without
`LEAN_NUM_THREADS=1`. It writes per-phase limits
`max(baseline × ratio, baseline + slack)` using the file's `tolerance` classes:

| Class | Phases | Time | Peak RSS |
| --- | --- | --- | --- |
| `translator` | parse/normalize/check/emit, translate.* | ×2.0 or +0.25 s | ×1.5 or +64 MiB |
| `lean` | elaborate, proof.* | ×1.5 or +10 s | ×1.3 or +256 MiB |

After a full baseline it sets `"status": "recorded"` and `reference_platform`.
Commit the updated file together with the measurement's revision.

## Gate

```sh
python3 scripts/perf-budgets.py gate --measurement M.json [--json findings.json]
```

Exit 0: every budgeted workload passed. Exit 1: any failure. Exit 3: no failure,
but some budget is still pending (`--allow-pending` turns this into 0; pending never
masks a failure). Findings:

| Kind | Meaning |
| --- | --- |
| `time-regression` / `memory-regression` | phase exceeds `max_seconds` / `max_peak_rss_kib` |
| `missing-workload` | budgeted workload absent from the measurement |
| `missing-phase` | budgeted phase (or its time/RSS) absent |
| `failed-workload` | translation, elaboration or proof build failed |
| `unbudgeted-workload` | measured workload not in the budgets file |
| `output-changed` | emitted Lean SHA-256 differs from the baseline |
| `platform-mismatch` | measurement host differs from `reference_platform` |
| `unserialized-measurement` | not recorded with `LEAN_NUM_THREADS=1` |
| `pending` | no baseline for the workload |

## Optimizations and preservation

A performance change must keep every workload's emitted Lean byte-identical (the
gate's `output-changed` check), or carry separate preservation evidence. For
example, `scripts/check.sh` golden/committed-translation comparison and proof
builds on the changed output. Rebaseline a changed output with
`baseline --workload ID` only in the same commit as that evidence.

No lookup/indexing or modularization optimization is claimed here. Measurements
must first show where time goes.

`python3 tests/roadmap/perf-budgets/test_perf_budgets.py` tests the gate,
baseline derivation, AIR overlay, module-local cold cleanup, `wait4` measurement
and a fake-translator record run offline.
