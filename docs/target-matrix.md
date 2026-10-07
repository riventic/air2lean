# Declared-support target matrix

[`compatibility.json`](../compatibility.json) declares the supported Zig versions, the
build hosts of each version and the target profiles. Every version × host × native
target × profile path it declares must be backed **on that platform** by CI.
[`assurance/target-matrix.json`](../assurance/target-matrix.json) maps each path to one
job of [`.github/workflows/ci.yml`](../.github/workflows/ci.yml) and, for a matrix job,
its exact `include` row, and names the steps that provide three kinds of evidence:

| Kind | Counts when the step runs |
| --- | --- |
| `native_execution` | `scripts/check.sh` with the differential test (`AIR2LEAN_DIFF` not `0`), `scripts/diff.sh`, or a roadmap gate's `check.sh --native[-only]` |
| `target_probe` | `scripts/floatprobe.sh` or `scripts/abi-probe.py observe` |
| `proof_check` | `lake build … Proofs` |

```sh
python3 scripts/target-matrix.py check            # exit 1 if a declared path is unbacked
python3 scripts/target-matrix.py check --strict   # also fail on any recorded gap
python3 -m unittest discover -s tests/roadmap/target-matrix -v
```

A step counts only when its job's runner is the path's host (`ubuntu-24.04` is
x86_64-linux, `macos-14` is aarch64-macos), its `if` holds for the selected row (the
checker evaluates the `matrix.*`/`runner.os` expressions CI uses and fails closed on any
other context), it is bound to the path's Zig version (the matrix row's `zig`, or the
step's `AIR2LEAN_ZIG_VERSION` in a job without a matrix), and it compiles no other OS's
`Gen-<os>.lean`. Proofs over a foreign golden compiled on another host, such as the
Linux 0.15.2 job's build of `tests/golden/0.15.2/threadsync/Gen-darwin.lean`, are a
translation regression, not platform support. Exit 2 means an input is unreadable. The
check is offline: it starts no Zig, Lake or Lean process.

A missing `native_execution` or `target_probe` may be recorded as an explicit gap with a
reason; `proof_check` never can, and a path with two gaps fails. Gaps keep Q05 partial;
`--strict` passing is part of its acceptance. Profiles whose `target_triples` are
`unverified` (`legacy-abi64-le`) claim no platform and must be listed as input-only. A
profile target without a declared native host fails; targets listed as `not_declared`
must stay undeclared.

## Current paths

| Zig | Host = target | Job | Native execution | Target probe | Proofs |
| --- | --- | --- | --- | --- | --- |
| 0.16.0 | x86_64-linux | `test` (full row) | check.sh + diff test | float probe | `lake build Proofs` |
| 0.15.2 | x86_64-linux | `test` (full row) | check.sh + diff test | float probe | `lake build Proofs` |
| 0.14.1 | x86_64-linux | `test` (restricted row) | dispatch `--native-only` | **gap** | `lake build Proofs` |
| 0.16.0 | aarch64-macos | `macos` | Darwin AIR export, check.sh + diff test | ABI probe (`aarch64-macos-none`) | `lake build Proofs` |
| 0.15.2 | aarch64-macos | `macos` | Darwin AIR export, check.sh + diff test | **gap** | `lake build Proofs` (with `Gen-darwin.lean`) |

The `macos` job is one job without a matrix (macOS runner concurrency is limited). It
installs the checksum-pinned stock aarch64-macos Zig releases, caches the patched
compilers it builds with them, exports fresh Darwin AIR, compares it with the goldens
and their `air-darwin`/`Gen-darwin` overrides, runs the differential test (host-listed
float differences count as `host`, [floats.md](floats.md)), and builds the proofs
against the translation of that host. On failure it uploads the dumped Darwin AIR.

Not declared: `wasm32-wasi` (needs T02 pointer-width parameterization and T05
native/WASM correspondence) and `aarch64-linux` (translation stays guarded; T04).
WASM execution joins this matrix only when `compatibility.json` declares it, and the
checker then requires its native-execution, probe and proof steps like any other path.
