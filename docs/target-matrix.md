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
| `target_probe` | `scripts/floatprobe.sh`, `scripts/abi-probe.py observe` or the T04 probe `scripts/aarch64-abi.py check` |
| `proof_check` | `lake build … Proofs` |

```sh
python3 scripts/target-matrix.py check            # exit 1 if a declared path is unbacked
python3 scripts/target-matrix.py check --strict   # also fail on any recorded gap
python3 -m unittest discover -s tests/roadmap/target-matrix -v
```

A step counts only when its job's runner is the path's host (`ubuntu-24.04` is
x86_64-linux, `ubuntu-24.04-arm` is aarch64-linux, `macos-14` is aarch64-macos), its `if`
holds for the selected row (the checker evaluates the `matrix.*`/`runner.os` expressions
CI uses and fails closed on any other context), it is bound to the path's Zig version (the matrix row's `zig`, or the
step's `AIR2LEAN_ZIG_VERSION` in a job without a matrix), and it compiles no other OS's
`Gen-<os>.lean`. Proofs over a foreign golden compiled on another host, such as the
Linux 0.15.2 job's build of `tests/golden/0.15.2/threadsync/Gen-darwin.lean`, are a
translation regression, not platform support. Exit 2 means an input is unreadable. The
check is offline: it starts no Zig, Lake or Lean process.

A missing `native_execution` or `target_probe` may be recorded as an explicit gap with a
reason; `proof_check` never can, and a path with two gaps fails. Gaps keep Q05 partial;
`--strict` passing is part of its acceptance. No path records a gap today, and CI's
`Declared target matrix is natively backed` step runs `check --strict`, so a new gap fails CI. Profiles whose `target_triples` are
`unverified` (`legacy-abi64-le`) claim no platform and must be listed as input-only. A
profile target without a declared native host fails; targets listed as `not_declared`
must stay undeclared.

## Current paths

| Zig | Host = target | Job | Native execution | Target probe | Proofs |
| --- | --- | --- | --- | --- | --- |
| 0.16.0 | x86_64-linux | `test` (full row) | check.sh + diff test | float probe | `lake build Proofs` |
| 0.15.2 | x86_64-linux | `test` (full row) | check.sh + diff test | float probe | `lake build Proofs` |
| 0.14.1 | x86_64-linux | `test` (restricted row) | dispatch `--native-only` | ABI probe (`0.14.1/x86_64-linux-gnu`) | `lake build Proofs` |
| 0.16.0 | aarch64-macos | `macos` | Darwin AIR export, check.sh + diff test | ABI probe (`aarch64-macos-none`) | `lake build Proofs` |
| 0.15.2 | aarch64-macos | `macos` | Darwin AIR export, check.sh + diff test | ABI probe (`0.15.2/aarch64-macos-none`) | `lake build Proofs` (with `Gen-darwin.lean`) |
| 0.16.0 | aarch64-linux | `aarch64-linux` | aarch64-linux AIR export, check.sh + diff test | T04 probe (`0.16.0/aarch64-linux-gnu`) | `lake build Proofs` |
| 0.15.2 | aarch64-linux | `aarch64-linux` | aarch64-linux AIR export, check.sh + diff test | T04 probe (`0.15.2/aarch64-linux-gnu`) | `lake build Proofs` |
| 0.14.1 | aarch64-linux | `aarch64-linux` | dispatch `--native-only` (check.sh without the diff test: 0.14.1 std cannot build the harness) | T04 probe (`0.14.1/aarch64-linux-gnu`) | `lake build Proofs` |

The `macos` job is one job without a matrix (macOS runner concurrency is limited). It
installs the checksum-pinned stock aarch64-macos Zig releases, caches the patched
compilers it builds with them, exports fresh Darwin AIR, compares it with the goldens
and their `air-darwin`/`Gen-darwin` overrides, runs the differential test (host-listed
float differences count as `host`, [floats.md](floats.md)), and builds the proofs
against the translation of that host. On failure it uploads the dumped Darwin AIR. Each
version's differential summary is uploaded as `diff-summary-<zig>-macOS-ARM64`, the macOS
rows of the accounting table ([host-accounting.md](host-accounting.md)).

The ABI target probes (`scripts/abi-probe.py observe`, [profiles.md](profiles.md)) run in
ReleaseSafe and ReleaseFast ([build-modes.md](build-modes.md)) against per-version contracts: 0.16.0's are
`tests/roadmap/abi-probes/<triple>-<mode>.json`, and 0.14.1's (x86_64-linux-gnu) and 0.15.2's
(aarch64-macos-none) are under `tests/roadmap/abi-probes/<zig>/`. The probe reports the Zig
version that compiled it, so a contract never matches another version's compiler. 0.14.1
needs the ABI probe because its std cannot build the float probe's `tests/diff/compat.zig`
writer. On aarch64-macos, the float probe's expected results are the x86_64-linux reference,
so it does not apply. The 0.14.1 and 0.15.2 contracts were recorded by running the probe with
stock compilers, checked against the `index.json` checksums: 0.15.2 natively on an
aarch64-macos host, and 0.14.1 in a `linux/amd64` container. That container ran ReleaseSafe
through `abi-probe.py observe`. Rosetta rejected the ReleaseFast binary (`bss_size overflow`),
so its output came from the same build run under `qemu-x86_64` and was checked against the
contract. CI runs both modes on a native `ubuntu-24.04` runner.

The `aarch64-linux` job (`ubuntu-24.04-arm`, no matrix) does the same for aarch64-linux-gnu
with Zig 0.16.0, 0.15.2 and 0.14.1, the versions with a T04 expected file (the translator rejects
other versions' aarch64-linux AIR): it builds the patched compilers, exports fresh AIR, compares it
with the goldens and their `air-linux-aarch64`/`Gen-linux-aarch64` overrides, runs the
differential test and builds the proofs against that translation. Its target probe is the T04
native probe of the same version (`scripts/aarch64-abi.py check`, below). The summaries are
uploaded as `diff-summary-aarch64-linux`.

Not declared: `wasm32-wasi` (needs T02 pointer-width parameterization and T05
native/WASM correspondence).
WASM execution joins this matrix only when `compatibility.json` declares it, and the
checker then requires its native-execution, probe and proof steps like any other path.

## ABI-only profiles (T04)

`abi_profiles` in the map lists the ABI-qualified profiles ([aarch64-abi.md](aarch64-abi.md)),
whether or not they are also declared translation paths. The checker requires each entry to have:

- its versioned expected file (`tests/roadmap/aarch64-abi/expected/<zig>/<triple>-<mode>.txt`);
- a `probe` step in a job whose runner is the profile's host. The step must run
  `scripts/aarch64-abi.py check … --target <triple>`, be bound to the entry's Zig version,
  and not ignore a failure (`|| true`, `set +e`);
- a `proof` step on any host that runs `tests/roadmap/aarch64-abi/Model.lean <triple> <expected>`.

| Zig | Profile | Probe job (host) | Proof job |
| --- | --- | --- | --- |
| 0.16.0 | aarch64-linux-gnu ReleaseSafe | `aarch64-linux` (`ubuntu-24.04-arm`) | `test` (full 0.16.0 row) |
| 0.16.0 | aarch64-macos-none ReleaseSafe | `macos` (`macos-14`) | `test` (full 0.16.0 row) |
| 0.15.2 | aarch64-linux-gnu ReleaseSafe | `aarch64-linux` (`ubuntu-24.04-arm`) | `test` (full 0.16.0 row) |
| 0.15.2 | aarch64-macos-none ReleaseSafe | `macos` (`macos-14`) | `test` (full 0.16.0 row) |
| 0.14.1 | aarch64-linux-gnu ReleaseSafe | `aarch64-linux` (`ubuntu-24.04-arm`) | `test` (full 0.16.0 row) |
| 0.14.1 | aarch64-macos-none ReleaseSafe | `macos` (`macos-14`) | `test` (full 0.16.0 row) |

The `aarch64-linux` job installs the checksum-pinned stock Zig releases and runs the probe
and compare before its translation steps. Like `macos`, it is a native-runner job that `scripts/local-ci.sh` does not
reproduce and `scripts/release-record.py` covers with GitHub evidence only.
