# Counterexample bundles (P08)

`scripts/counterexample.py` turns a failing schedule execution or differential case into a self-contained bundle (schema 1, `qualified: false`). It also separates a reproduced failure from an outcome that automation could not decide.

```sh
# Enumerate, select the first complete failing execution, replay it, write the bundle (+ .receipt.json).
python3 scripts/counterexample.py search --example atomics --function mpRelaxed --node-cap 64 --output cx.json
# Bundle an execution of an existing scripts/schedules.py enumeration receipt.
python3 scripts/counterexample.py from-receipt --receipt schedules.json [--execution-index 2] --replay --output cx.json
# Bundle a case from a diff-report summary (replays only a case with an observed schedule witness).
python3 scripts/counterexample.py from-case --summary tests/diff/out/report.json \
  --example atomics --function mpRelaxed --input-index 1 --replay --output cx.json
# One-command replay of a bundle: exit 0 reproduced, 1 not reproduced, 2 unsolved, 3 setup/stale.
python3 scripts/counterexample.py replay --bundle cx.json
```

All builder commands exit 0 once a bundle is written, whatever its classification, and 3 on invalid or stale evidence. Read `classification` from the bundle or the `COUNTEREXAMPLE:` line.

## Bundle contents

| Field | Content |
| --- | --- |
| `input`, `input_sha256`, `input_index` | The decoded input row and the SHA-256 of its exact bytes |
| `schedule` | Full choice `prefix`, `options`, `choice_count`, `fuel` and execution index (a witness prefix padded with the oracle's default zeros) |
| `observed` / `native` | Typed model observation (`kind`, wire `line`); for differential cases also the native one |
| `contract` | Violated contract: `no_illegal_behaviour`, `no_deadlock`, `no_safety_panic` (schedule failures, by model kind) or `native_correspondence` (differential mismatch) |
| `location` | Root function, AIR files, callees and spawned workers (`comptime_fn`, at most 64), and `candidate_sites` (at most 200) |
| `replay` | Embedded replay `request` (no `expected`; the CLI compares kind, line and options itself), `expected`, `command`, `status` |
| `sources_sha256` | Digest of the runner/runtime source fingerprints. A stale bundle is refused before the model runs |

### Localization limits

The model reports only the `Zig.Error` constructor, not the faulting instruction. The generated Lean has no per-instruction source map (`source_map: "unavailable"`), and AIR has no reliable file spans ([diagnostics.md](diagnostics.md)). `candidate_sites` therefore lists every instruction that could raise the observed failure:

- `illegal`: memory accesses (plain, atomic, `memcpy`/`memset`), `rem`/`mod`, and `free`/`destroy` calls.
- `deadlock`: calls to `join`/`wait`/`timedWait`/`lock`/`lockShared`.
- `model_panic`: noreturn panic-handler calls whose `scripts/panic-policy.tsv` constructor matches, plus the matching checked arithmetic.

A differential value mismatch is `function_only`. `zig_line` is `fn` declaration line + `dbg_stmt` line − 1 (nearest preceding statement), so it is approximate. Inside a `dbg_inline_block` the call-site line is kept and the site is marked `inlined`. Std functions have no Zig line.

## Classification

`verdict()` is the only mapping from outcome to verdict. It is kept in one function so that it can move to the V06 outcome taxonomy:

| `classification` | When |
| --- | --- |
| `counterexample` | A failure kind (`illegal`, `deadlock`, `model_panic`, differential `mismatch`/`illegal_exclusion`) that a fresh replay of the recorded prefix reproduced exactly. Only this sets `is_program_bug_evidence` |
| `candidate` | A failure was observed but not replayed: `--no-replay`, binary missing, or a sequential differential case (`replay.command` reruns `scripts/diff.sh` and needs Zig) |
| `unsolved` | `timeout`, `replay_timeout`, `replay_not_reproduced`, `search_cap`, `enumeration_truncated`, `prefix_cap` (incomplete failing trace), `bounded_no_result` (fuel), `unspecified_result`, `host_difference`, `unsupported` |
| `no_failure` | A matching differential status, or a complete, untruncated bounded tree without a failing or no-result execution. It is bounded evidence only, not a proof |
| `setup_failure` | Input or native-harness failure, or a replay process error |

A timeout or cap is never a program bug, even when the receipt recorded a failure before the limit was hit: the replay must reproduce the failure. An observed failure is still a counterexample when the surrounding tree was truncated, because coverage limits do not weaken a reproduced execution.

## Validation

```sh
python3 -I -B tests/roadmap/counterexamples/test_counterexample.py
# After `(cd tests/diff && lake build schedules)`:
python3 -I -B tests/roadmap/counterexamples/test_e2e.py [path/to/schedules]
```

The unit suite mocks the model process. Positive controls cover a replayed race with prefix, contract and Zig-line sites, panic and deadlock site selection, and replay exit statuses. Negative controls cover a search timeout, a replay timeout, an unreproduced replay, truncated and no-result trees, prefix-capped failures, a replay error, the verdict table, capped and stale differential cases, and an unreplayed sequential mismatch.

The end-to-end test runs the real atomics model. `mpRelaxed`'s relaxed message-passing data race replays as an `illegal` counterexample, with candidate sites at `atomics.zig:43` (reader) and `:20` (writer). `mpRelAcq` is `no_failure`; `--fuel 2`, `--node-cap 1` and a 1 s timeout on `stackPush` (which takes more than 2 minutes at node cap 2000) are `unsolved`, and their bundles do not replay successfully.
