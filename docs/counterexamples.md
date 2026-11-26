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

### Without Zig

```sh
# Search small inputs for a violation of a stated postcondition by evaluating the generated Lean.
python3 scripts/counterexample.py goal-search --example loops --function sumUpTo \
  --pre 'p0.toNat < 1000' --spec 'r = .ok (BitVec.ofNat 32 (p0.toNat * (p0.toNat - 1) / 2))' \
  --gen Gen.lean --output goal.json
# Replay a schedule bundle through the Lean interpreter (needs `lake build Concurrent ScheduleSearch` in tests/diff once).
python3 scripts/counterexample.py replay --bundle cx.json --interpret
```

`goal-search` appends a driver to a copy of `Gen.lean` and runs `lake env lean --run`: no native toolchain, no libm archive. `--spec` is a decidable Lean proposition over the parameter names (`p0`, `p1`, ...) and `r : Except Zig.Error T`; `--pre` filters inputs; both are elaborated with the example's namespace open, so they name its types and constructors (`{ x := p0.y, y := p0.x }`, `.red`, `Level.toBits p0`). Candidates are boundary values, a seeded cross product and a seeded sample (`--max-inputs`, `--seed`), smallest first. The first violation of a sampled domain is then minimized (below) and replayed in a fresh Lean process; only then is it a `counterexample` (contract `postcondition`).

**Value kinds.** Supported functions are sequential `Zig.Result` and `Zig.MemM` functions (the latter run from the program's start memory, `mem0 .fresh`) whose parameters and result are values. `scripts/lean-eval.py` has one class per value kind the translator emits: integers of any width and signedness, `bool`, `void`, enums (exhaustive, with signed or sparse tag values, and non-exhaustive), structs (also packed ones, which are Lean structures), tagged unions, optionals, error unions, and read-only slices (`[]const T` of a function that uses no memory, which the translator passes as `Array T`), nested in any way. A type is resolved by walking the generated Lean type and the function's AIR type table (`--air-dir`, default `tests/golden/<ex>/air`) together: the Lean declaration gives the names, the AIR gives signedness, tag values, error names and the slice item type, and a declaration that does not line up with its AIR type is rejected. Each class supplies the enumeration of its values, the row encoding and its Lean decoder, the Lean renderer, the Zig literal and the reader of a native result, so a nested type needs no code of its own. A value is written as the native harness renders it (`tests/diff/common.zig`): an integer, an enum's tag value, `{"field":…}`, `{"<active field>":…}`, `null` or the payload, `{"err":"Name"}` or the payload, a JSON array. Everything else is `unsolved: unsupported` with the reason in `source.detail`, never a guess: a pointer or a slice the function writes (`Zig.Ptr`, `Zig.Slice`: a place in memory, not a value), a slice result, floats, vectors, an extern or packed union, a tuple, an untagged union, a type whose rendering would be ambiguous (`??T`, an error union of a struct with a field `err`), a concurrent function (`Zig.ConcM`), a function with an environment instance argument, and a named type without an AIR type table. Without an AIR type table only `BitVec n` (assumed unsigned, `signedness: assumed_unsigned`) and `Bool` resolve.

**Minimal input.** Rows are ordered by the size of their values (the magnitude of a number, the items and length of a slice, the fields of a struct), then by their encoding. When the whole domain was enumerated the first violation is the smallest (`source.minimization.status = smallest_of_domain`). Otherwise the search tried a sample, and the violation is shrunk: each round evaluates the inputs one step simpler (a number moved toward zero by a power of two, an optional set to `null`, a slice without one item, one field or item shrunk) and moves to the smallest that still violates the postcondition, until none does (`locally_minimal`: no input one shrink step below the reported one violates) or a round cap or a failed evaluation stops it (`round_cap`, `stopped_*`; the input reached so far is still an observed violation). A domain fully enumerated without a violation is `no_failure`; a bounded search without one is `unsolved: search_exhausted`, as are a timeout (`timeout`), a no-result (fuel) input (`bounded_no_result`) and a precondition no input satisfies. An elaboration error of the driver or spec is `setup_failure: lean_error`. Sequential `from-case` bundles of supported functions replay the same way (`replay.kind = lean_sequential`); that confirms the model side only, and the native line stays recorded evidence. `replay --interpret` runs `tests/diff/Schedules.lean` through the interpreter with the recorded schedule prefix as the oracle.

### With the Zig side

```sh
# Also run the native program on the violating input and compare (stock zig; $AIR2LEAN_ZIG or zig by default).
python3 scripts/counterexample.py goal-search --example loops --function scale --spec 'r.toBool = true' \
  --gen Gen.lean --zig-source loops.zig --native-zig /path/to/stock/zig --output goal.json
python3 scripts/counterexample.py replay --bundle goal.json --native-zig /path/to/stock/zig
```

`--zig-source` (on `goal-search` and `from-case`) adds `replay.zig_native` to a sequential bundle: the Zig file and its SHA-256. The Zig file must define `--function` as exactly one `export fn` or `pub fn`; an `export fn` takes integers and `bool` only (it is called through its C-ABI declaration), any other value kind needs `pub fn`. The replay re-derives the value kinds from the hashed `Gen.lean` and AIR document of the Lean request, writes each argument as a Zig literal of its kind (typed by the function's own parameter types, `std.meta.ArgsTuple`), builds `tests/diff/common.zig` plus that harness with `zig build-exe -OReleaseSafe -mcpu=baseline`, runs `forkCall` in a child process (as `scripts/diff.sh` does) and compares the outcome line with the Lean one by the differential rules: equal values, or a native panic kind and its `Zig.Error` constructor from `scripts/panic-policy.tsv` (`integerOverflow` and `overflow`). Both sides must reproduce for `replay.status = verified`. A native outcome that disagrees is `not_reproduced` (`unsolved: replay_not_reproduced`: a model, translation or host difference, never program-bug evidence); a failed native build or missing `zig` is `setup_failure: replay_error`; a changed Zig file, `Gen.lean` or AIR document is stale (`error`). `replay` exits 0/1/2/3 by the combined status.

**The postcondition on the native outcome.** When the request states a postcondition, agreement of the two outcome lines is not the last check. The native line is read as a value of the result type (or, for a panic, as the `Zig.Error` constructor of its kind) and bound to `r` in a fresh Lean process that does not call the model; the postcondition is decided on it (`replay.zig_native.postcondition.status`: `violated`, `holds`, or `undecided` when the line is no value of the type). The replay is `verified` only when the native program's own outcome violates the postcondition as the model's did; otherwise it is `not_reproduced`, so the case stays unsolved. `replay` prints `native_postcondition=…`.

`from-case --spec '<Prop>' [--pre '<Prop>']` states a postcondition for a sequential differential row of a function within the value kinds above. The model decides it on the row; a violation is the failure of the case (contract `postcondition`, `source.postcondition = violated`) and replays as above, with `--zig-source` also on the native outcome. A postcondition that holds leaves the differential verdict of the row. For a function outside the value kinds (memory buffers, floats) `--spec` is refused with the reason; such rows keep the row replay below, which confirms the differential outcomes only.

### Any sequential shape: row replay

`from-case --replay` of a sequential differential case whose function the Lean goal search cannot express (pointers, slices the function writes and other memory buffers, floats, vectors, allocators) uses `replay.kind = diff_row`. It reruns the example's production runners on exactly the recorded input row: the example's own `tests/diff/<ex>/harness.zig` built with `zig build-exe -OReleaseSafe -mcpu=baseline` (stock zig, `--native-zig`) and the Lean runner `tests/diff/.lake/build/bin/difftest` (`--difftest`; `(cd tests/diff && lake build difftest)`), in a scratch directory where the row is the only input (every other function of the example gets an empty input file). `replay.status = verified` only when both fresh output lines equal the lines the differential run recorded, byte for byte; a fresh line that differs (a float bit, a libm result, a race) is `not_reproduced` and the case is `unsolved: replay_not_reproduced`, never program-bug evidence. A missing runner is `unavailable` (a `candidate`, exit 3), a failed build or a source or input row that changed since the bundle was written is `error`. Nothing is generated or re-derived, so exactly the shapes the differential test supports are covered, with its own panic-kind and value rendering; the check is that both sides reproduce the recorded outcomes, and that the model line is not a stale record. Concurrent cases keep the schedule replay (`--binary`/`--interpret`).

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

The model reports only the `Zig.Error` constructor, not the faulting instruction, so `candidate_sites` is a candidate set, not an exact fault site. Each site and function carries `source_span` and `source_span_status` in the exporter-provenance format of [diagnostics.md](diagnostics.md): `statement` (nearest preceding `dbg_stmt` in the instruction's own inline scope; `{file, module, line, column}`), `declaration` (function-level, or before any `dbg_stmt`; `column: null`) or `unavailable_in_AIR` (`source_span: null`: older exports without `src`, or an inlined body without its callee's `src`). `location.source_map` is `exact_statement` when any visited function exports `src`, else `unavailable_in_AIR`. Spans are statement-granular, not a source-correspondence claim. A site inside an inlined call is exact when the callee exports its own `src`: `source_span` and `zig_line` are the callee's statement and `zig_file` is the callee's file. Every inlined site also lists `inline_chain` (each enclosing inline block, outermost first: `call_site`, the span of the statement that holds the call, its `call_site_status`, and `callee_span`, the callee's declaration) and `call_site_span` (the innermost call site), so a site whose own span is `unavailable_in_AIR` (a nested inline block without `src`) is still placed at where it is reached from. Without `src`, the old approximation below remains. `candidate_sites` lists every instruction that could raise the observed failure:

- `illegal`: memory accesses (plain, atomic, `memcpy`/`memset`), `rem`/`mod`, and `free`/`destroy` calls.
- `deadlock`: calls to `join`/`wait`/`timedWait`/`lock`/`lockShared`.
- `model_panic`: noreturn panic-handler calls whose `scripts/panic-policy.tsv` constructor matches, plus the matching checked arithmetic.

A differential value mismatch is `function_only`. A goal-search violation is `function_only`, unless the violating run is itself an `illegal` or `model_panic` outcome: then the sites of that failure are listed (a postcondition that fails because `a * b` overflows names the `mul_safe` statement). `zig_line` is the span line for an uninlined `statement` site; otherwise it is `fn` declaration line + `dbg_stmt` line − 1 (nearest preceding statement), so it is approximate. Inside a `dbg_inline_block` the call-site line is kept and the site is marked `inlined`. Std functions have no Zig line.

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
# Goal search and Zig-free replay (the seeded-loop class needs `lake build ZigLean air2lean`; no Zig). With
# AIR2LEAN_ZIG_AIR and AIR2LEAN_ZIG_NATIVE (as below) also the value-kind fixture native/shapes.zig:
python3 -I -B tests/roadmap/counterexamples/test_goal.py
# Real export (I05 spans) and the native Zig replay. Needs a patched zig that carries the I05 exporter,
# a stock zig, and `lake build ZigLean air2lean`; skipped otherwise:
AIR2LEAN_ZIG_AIR=/path/to/zig-air/bin/zig AIR2LEAN_ZIG_NATIVE=/path/to/stock/zig \
  python3 -I -B tests/roadmap/counterexamples/test_real_export.py
# After `(cd tests/diff && lake build schedules)`:
python3 -I -B tests/roadmap/counterexamples/test_e2e.py [path/to/schedules]
```

The unit suite mocks the model process. Positive controls cover a replayed race with prefix, contract and Zig-line sites, panic and deadlock site selection, and replay exit statuses. Negative controls cover a search timeout, a replay timeout, an unreproduced replay, truncated and no-result trees, prefix-capped failures, a replay error, the verdict table, capped and stale differential cases, and an unreplayed sequential mismatch.

The end-to-end test runs the real atomics model. `mpRelaxed`'s relaxed message-passing data race replays as an `illegal` counterexample, with candidate sites at `atomics.zig:43` (reader) and `:20` (writer). `mpRelAcq` is `no_failure`; `--fuel 2`, `--node-cap 1` and a 1 s timeout on `stackPush` (which takes more than 2 minutes at node cap 2000) are `unsolved`, and their bundles do not replay successfully.

`test_real_export.py` exports `tests/roadmap/counterexamples/native/loops.zig` with the patched compiler (`native/export.sh`, a compiler without the I05 change fails it on purpose), translates it, and checks the reports against the real file: the off-by-one `sumUpTo` counterexample (`input = [1]`) carries the declaration span of `export fn sumUpTo`, and the overflowing `scale` counterexample carries the `mul_safe` statement span at the line and column of `*` in `return a * b;`, with the headline naming `loops.zig:<line>`. In both, the native program built from the same file gives the same outcome (`{"ok":1}`; `integerOverflow` against `Zig.Error.overflow`). A native source that disagrees leaves the violation unsolved. The unit class `NativeReplay` in `test_goal.py` covers the comparison and failure mapping with a fake `zig`. Sequential only: schedule bundles keep the `schedules` binary replay.

`test_goal.py` also covers the value kinds. `Kinds` checks the type model without Lean: one resolution for every kind and nesting, the reason of every rejection, the row encoding, Zig literals, native-result reading, finite and unbounded domains, and the shrinking. `Shapes` runs `native/shapes.zig` end to end (patched compiler, `air2lean`, Lean, stock zig): per kind (struct, optional result and parameter, error union, enum, enum with signed tag values, slice, tagged union, a nested struct in the memory monad) a function with a seeded bug yields a counterexample at its smallest violating input, no input one shrink step below violates, and the native program returns the same value and itself violates the postcondition; the correct twin of each reports none (`no_failure` for an exhausted domain, else `unsolved: search_exhausted`); a native source without the bug leaves the violation unsolved; a slice the function writes is rejected with the reason.

`test_row.py` (`RealPostcondition`, and `from-case --spec` with stand-ins) decides stated postconditions on rows of the committed `basic`, `variants`, `options` and `errors` examples, on the model and on the native outcome. It also covers the row replay: stand-in `zig` and `difftest` programs drive the request shapes, the scratch inputs (only the selected function has a row), every failure mapping, staleness and the `from-case` integration, and a real class runs the committed `slices` (memory buffers, a safety panic) and `basic` harnesses with the built `difftest` (skipped without them; a forged model line is `not_reproduced`).
