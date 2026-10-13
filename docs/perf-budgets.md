# Translation and proof performance budgets

Status: **recorded** (Darwin arm64 reference platform, 18 workloads). The gate has three
modes: the strict reference-platform limits, a portable mode with generous limits that CI runs
on any runner, and a normalized mode that also gates proof time on any machine (see Gate).

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

Eleven more golden examples were added with the same shape (`asm`, `atomics`, `errors`,
`floatconv`, `floats`, `iogroup`, `options`, `pointers`, `recursion`, `sync`, `threads`),
for 18 workloads in all. `lists` is not a workload: its committed golden AIR lacks the std
callees that `examples/lists/filter` adds, so it cannot be translated from the committed
files alone. `sync` has `reference_gen: null`: `Proofs/Sync/Gen.lean` carries a hand-added
function (`rwLockSnapshotPair`) that the golden AIR does not produce, so its output is
pinned only by the recorded SHA-256.

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

`--portable` checks the `portable_max_*` limits instead, on any platform, over the
phases that need no cold Lake build (`translate.*`, parse/normalize/check/emit and
`elaborate`; `--phase` narrows further). `portable_tolerance` in the budgets file sets
them from the baseline: translator phases `max(x10, +1 s)` time and `max(x3, +128 MiB)`
RSS; Lean phases `max(x6, +30 s)` and `max(x2, +512 MiB)`. They ignore platform and
absorb runner noise but still fail on a gross regression, any memory blow-up, a missing
workload/phase or any change of emitted Lean (`output-changed`). CI runs
`record --skip-proof` then `gate --portable` after building the translator (job step
"Performance budget regression gate (portable)"). The strict gate remains the
reference-platform check: record under the guard as above and run `gate`.

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

## Proof time on any machine

Wall time of a proof build differs between machines by far more than a fixed slack can absorb,
so the reference limits apply to the reference platform only. `record` therefore also times a
fixed pure-Lean workload, `tests/roadmap/perf-budgets/Calibration.lean` (no imports; `omega`,
`simp`, `decide` and `decide +kernel` goals; median of 3 `lake env lean` runs, about 5.8 s on the
reference machine), once per measurement (skipped by `--skip-proof` and `--skip-calibration`).
`baseline` stores each Lean phase (`elaborate`, `proof.cold`, `proof.warm`) as `baseline_ratio`
and `max_ratio`, its time divided by the calibration time of the same run (limit
`max(ratio x 2, ratio + 2)` units), and, for workloads recorded with `--per-module`, one limit per
proof module that takes at least 2 s (`budget.modules`: module-local cold build, `max(ratio x 2,
ratio + 1)`). The budgets file records the calibration file's SHA-256: editing the file fails
`validate` until a rebaseline.

```sh
python3 scripts/perf-budgets.py gate --normalized --measurement M.json [--workload ID] [--phase proof.cold]
```

`--normalized` is `--portable` plus those Lean phases and modules, compared as multiples of the
measurement's own calibration, so a slower or faster machine cancels. It fails closed: a missing,
zero or foreign calibration (`missing-calibration`), a phase without a calibrated budget, a
budgeted hotspot module without a timing (record with `--per-module`), or any change of emitted
Lean. Memory uses the portable limits. `--workload` gates a partial `record --workload`
measurement. CI runs it for the `threadsync` workload (the Handoff and WaitGroup hotspots) on
0.16.0. Limits: the ratio assumes the machine scales CPU-bound Lean work uniformly (it does not
model memory-bound or I/O effects), and cold builds of a runner with a warm Lake cache of
dependencies are not comparable with a cold dependency build.

## Heartbeat budgets of proofs

Lean's heartbeats count elaboration work deterministically: the same toolchain and sources give
the same count on every machine. A proof that needs more than the default `maxHeartbeats`
(200000, in Lean's units of 1000 heartbeats) raises it with `set_option maxHeartbeats N in`, and
that `N` is a recorded budget, not a free choice. `assurance/heartbeat-budgets.json` lists the
gated files, the policy and one entry per raised declaration: `measured` and
`budget = ceil(measured * tolerance / step) * step` (tolerance 1.25, step 50000). The Lean build
fails when a proof grows past its budget; `scripts/heartbeat-budgets.py check` (preflight) fails
when a raise of a gated file is not exactly its recorded budget, when an entry has no raise, or
when a budget fits the default (drop the raise). `record FILE…` elaborates a measuring copy of
each file (`Elab.async false`, every declaration counted; run it under `scripts/build-guard.py`)
and rewrites the file's entries; the `set_option` lines are then set by hand and `check` confirms
them. `show` lists the entries, worst first: the list the `fsym` engine lane works from. Gated
today: the list proofs over the open `Allocator` (`Proofs/Lists/Alloc.lean`, `Append.lean`,
`Container.lean`).

## Optimizations and preservation

A performance change must keep every workload's emitted Lean byte-identical (the
gate's `output-changed` check), or carry separate preservation evidence. For
example, `scripts/check.sh` golden/committed-translation comparison and proof
builds on the changed output. Rebaseline a changed output with
`baseline --workload ID` only in the same commit as that evidence.

## Measured hotspots and optimizations

Measured on the reference platform (`record --per-module`, one serial lane, host shared
with other jobs, so differences below about 20% are noise):

- **Translator.** A whole translation takes 20-50 ms (sync: 115-157 ms, 1.5 MB of AIR)
  at about 40 MiB. Of the four gated phases the largest is `parse` (up to 16 ms, sync).
  The `renumber` stage (`Anon.renumberAll`, reported in `--timing-json` but not budgeted)
  was larger than all four together: sync 91 ms of 146 ms wall, threadsync 14 of 44 ms.
  It re-ran the whole rename-and-compress pipeline once per marker kind (5 passes) for
  every function, although most functions contain no instance of most markers. The
  change skips functions whose identity strings hold no instance of the marker, and
  recompresses only changed texts after the first pass. renumber: layout 7.7 -> 3.1 ms,
  threadsync 13.9 -> 6.8 ms, sync 91 -> 73 ms (the rest is the strict JSON parse).
  Preservation: all 58 committed AIR directories under `tests/` and `case-studies/`,
  translated plain and with `--source-map-json` (116 runs, 156 stored results including
  exit codes and diagnostics), are byte-identical before and after; the gated workloads'
  output hashes are unchanged; `stable-generation/test_cli.py` and `timing_cli.py` pass.
- **Lean elaboration of generated modules** takes 0.3-2.3 s and 550-650 MiB, mostly
  import cost; it scales weakly with output size.
- **Proofs** dominate: 64 `Proofs.*` modules cost 116 s module-local cold. Slowest:
  `Sync.RwLock` 11 s, `Threadsync.Handoff` 17 s module-local (2.9 GB), `Threadsync.WaitGroup`
  9 s, `Sync.Handoff` 6.6 s. Warm rebuilds (trace check only) take 0.15-0.18 s per workload.
  `Sync.RwLock.live_all` proved two facts about `Ph` with `simp_all` inside a context
  holding the whole protocol invariant (2.1 s by the profiler). They are now standalone
  `Ph` lemmas; the module's standalone elaboration went from 11.3 s to 9.4 s. No theorem
  statement changed.
  **Profile serially.** Lean elaborates theorems as async tasks, and the wall time of a task
  includes the time other tasks run on the same thread: `Threadsync.Handoff.enc_box`
  (`decide +kernel` of seven array equalities) showed 8.4 s with the default settings but
  0.4 s on its own, and each conjunct 0.1-0.25 s. It was never a hotspot. Use
  `lake env lean -DElab.async=false -Dtrace.profiler=true -Dtrace.profiler.threshold=400
  Proofs/X/Y.lean`.
  The serial profile of `Threadsync.WaitGroup` put `tally_decode` first (6 s): four
  `have h' : intOfBytes ... = pure a := h` steps, each a 0.7-2 s unification that unfolds
  `ExceptT.run` over the whole term. The general lemma `Zig.Result.eq_pure_of_run`
  (`ZigLean/ResultRun.lean`) states the step once at a variable; no statement changed, and the
  module's elaboration went from 19-22 s to 15-17 s (three runs each, `-DElab.async=false`).
  Remaining in `Threadsync.Handoff` and `WaitGroup`: kernel type checking of the large
  `refine` chains (`sig_body` 4.5 s, `handoff_completes` 3.4 s, `fwait_spec`, `wus_spec`
  2.7 s each, `inv_finish` 3.5 s). Other `have _ : x = pure a := h` steps exist in
  `Proofs/Lists` and `ZigLean/Sep`; they are not hotspots.

No lookup-structure change in the translator is claimed: no translator phase other than
`renumber` exceeds 16 ms. The remaining proof candidates are the `WaitGroup`/`Handoff` `refine` chains above.

`python3 tests/roadmap/perf-budgets/test_perf_budgets.py` tests the gate,
baseline derivation, AIR overlay, module-local cold cleanup, `wait4` measurement
and a fake-translator record run offline.
