# Distribution, doctor and editor workflow

air2lean is distributed as source plus checksum-pinned build instructions. Nothing in a
working setup depends on undocumented local state: the elan and Zig downloads are pinned by
sha256, the Lean toolchain by its exact version in `lean-toolchain` (elan installs it), and
`scripts/clean-env.sh` reproduces the first proof in a fresh container from tracked files only.

## Compatibility metadata

[`compatibility.json`](../compatibility.json) is the committed release compatibility record:

| Field | Meaning | Source of truth it must equal |
|---|---|---|
| `lean.toolchain` | pinned Lean toolchain | `lean-toolchain`, `tests/diff/lean-toolchain` |
| `lean.lake_packages` | Lake dependencies (none) | `lake-manifest.json` |
| `lean.elan` | elan release, asset URL and sha256 | `zig-patch/versions.toml` `[ci.elan]` |
| `zig.versions[]` | supported Zig versions in order, source tarball URL/sha256, hook, LLVM major, CI host Zig URL/sha256 | `zig-patch/versions.toml` |
| `zig.versions[].hosts` | supported build hosts (`x86_64-linux`, `aarch64-macos`) | the Linux-only rule in `scripts/workflow-common.sh` |
| `zig.default` | default Zig version | `scripts/translate.sh` |
| `air2lean.air_json_schemas` | accepted AIR-JSON schemas | `Air2Lean/Air/Profile.lean` |
| `profiles` | accepted target/build profiles | `Air2Lean/Air/Profile.lean` |
| `translation` | target, CPU, optimize mode and error tracing of `translate.sh` exports | `scripts/translate.sh` |
| `air_only_lock` | wrapper/compiler names and allowed commands of the no-LLVM lock | `zig-patch/lock.sh` |
| `resources` | disk/memory guidance per workflow (doctor warnings only) | — |
| `clean_environment` | container image, platform, recipe and tutorial | `Dockerfile.clean-env` |

The supported version list must also match `scripts/workflow-common.sh`, `scripts/local-ci.sh`
and the CI matrix. Check it offline (CI runs this and the tests below):

```sh
python3 scripts/compat.py check          # human-readable; exit 1 on drift
python3 scripts/compat.py check --json   # {"consistent": ..., "errors": [...]}
python3 scripts/compat.py release --out air2lean-release.json
```

`release` (only after a successful check) adds sha256 checksums of `lean-toolchain`,
`lake-manifest.json`, `compatibility.json`, every exporter source and hook patch, the Git
revision, and `exporter_fingerprint` (the same compiler-source key as `scripts/local-ci.sh`).
Attach it to a release so users can confirm their checkout and compiler sources.
Changing a pin means changing `versions.toml` (or `lean-toolchain`) and `compatibility.json`
in the same commit.

## Doctor

```sh
scripts/doctor.sh                       # everything needed for scripts/translate.sh
scripts/doctor.sh --require proofs      # only what committed proofs need (no Zig)
scripts/doctor.sh --json                # machine-readable report
scripts/doctor.sh --zig-version 0.15.2 --zig-air /abs/zig-air-0.15.2/bin/zig
```

No downloads, builds or AIR export. Every check prints one line and, if not OK, a `hint:`
with the command to run. Checks, in order:

| id | What it checks |
|---|---|
| `metadata` | `compatibility.json` exists and agrees with its sources (`compat.py check`) |
| `host` | host is a supported build host |
| `zig-version` | selected version is supported, and supported on this host (0.14.1: Linux only) |
| `elan`, `lean-toolchain` | elan is installed; the toolchain pinned in `lean-toolchain` is installed |
| `proof-build` | `Proofs.Basic.Proofs` is built (editors need built imports) |
| `stock-zig` | stock Zig on `PATH` (or `AIR2LEAN_ZIG`) matches the selected version; only bootstrapping needs it |
| `patched-zig-<v>` | each supported version's `zig-air-<v>/bin/zig`: present, reports `<v>`, and its AIR-only lock state |
| `translator` | `.lake/build/bin/air2lean` exists (translate.sh rebuilds it anyway) |
| `bootstrap-tools` | `curl`, `tar`, `xz`, `patch` and `sha256sum`/`shasum` for `zig-patch/build.sh` |
| `docker` | Docker daemon reachable (only `local-ci.sh`/`clean-env.sh` need it; `--no-docker` skips) |
| `disk`, `memory` | free disk at the repository and physical memory against `resources` |

Statuses are `ok`, `note` (informational), `warn` (works but needs attention), `fail` and
`skip` (an optional compiler that is not built). The exit status is 0 when the required level
(`--require`, default `translate`) is ready, 1 otherwise, 2 for usage errors. The JSON report
(schema `air2lean-doctor/1`) has `ready.proofs`, `ready.translate`, `exit_code` and `checks[]`
records with `id`, `status`, `message`, optional `hint` and `details`.

Lock states of a patched compiler (`details.lock`):

| state | meaning | status |
|---|---|---|
| `locked` | `bin/zig` is exactly the wrapper `zig-patch/lock.sh` writes and `bin/zig-unlocked` exists | ok |
| `stale-lock` | wrapper differs from the current `lock.sh` | warn: rerun `zig-patch/lock.sh PREFIX` |
| `broken-lock` | `bin/zig-unlocked` exists but `bin/zig` is not the wrapper, or the wrapper lost its compiler | fail |
| `llvm-or-unlocked` | no lock: valid only for an `AIR2LEAN_LLVM=1` build | warn |

Passing `--zig-air .../zig-unlocked` is rejected, as in `translate.sh`. The doctor cannot
prove a binary contains the exporter; `translate.sh` checks that it writes fresh AIR.
The doctor needs Python 3.8+; committed proofs themselves need only elan.

## Clean environment recipe

```sh
scripts/clean-env.sh               # every tutorial, its exercise and negative control
scripts/clean-env.sh --translate   # also bootstrap Zig 0.16.0, check the lock, translate and prove
```

It builds `Dockerfile.clean-env` (Ubuntu 24.04 with only bash, ca-certificates, curl, git,
patch, python3 and xz-utils; `linux/amd64`) with no build context, copies tracked files only
(no `.lake`, compilers or caches), mounts no cache volumes and runs as an unprivileged user.
Inside it follows [getting started](getting-started.md) literally: installs the pinned elan
(sha256-verified), `elan toolchain install $(cat lean-toolchain)`, `scripts/doctor.sh --require
proofs`, `lake build Proofs.Basic.Proofs`, `lake env lean tutorials/first-proof/Main.lean`,
then builds the modules of every tutorial (`python3 scripts/tutorials.py modules`) and runs
`python3 scripts/tutorials.py check`: each `Main.lean` and solved exercise must elaborate, and
each negative control (for example the first proof's `pure 1`) must fail with its expected
error. The documentation-only cross-target tutorial is not run.
`--translate` additionally installs the pinned host Zig, runs `zig-patch/build.sh 0.16.0`
(default: no LLVM, AIR-only lock), requires the doctor to report `locked`, verifies the locked
compiler refuses `build-exe`, translates the getting-started demo and checks its separate proof.
Results (doctor JSON, logs) are written under `.lake/clean-env-results/`.

## Editor diagnostics (optional)

Editors use Lean's language server, which Lake starts as `lake serve` with the toolchain from
`lean-toolchain` (elan selects it automatically):

- VS Code: install the `leanprover.lean4` extension and open the repository root folder.
- Neovim: `lean.nvim`; Emacs: `lean4-mode`. Both start `lake serve` from the project root.

Open the repository root, not a subdirectory, so the server finds `lakefile.toml`. Build the
modules you import first (for the tutorial: `lake build Proofs.Basic.Proofs`); until then the
editor reports missing imports or rebuilds them in the background. After translating new code,
`lake build Proofs.MyProgram.Gen` before opening proofs that import it. In VS Code, the
"Lean 4: Restart File" command reloads a file after its imports were rebuilt. Generated
`Gen.lean` files are translator output: read them in the editor, but write proofs in separate
files.

The same diagnostics are available without an editor, for scripts and CI:

```sh
lake env lean tutorials/first-proof/Main.lean          # human-readable, exit 1 on errors
lake env lean --json tutorials/first-proof/Main.lean   # one JSON message per line
```

Each `--json` line has `severity` (`error`, `warning`, `information`), `pos`/`endPos`
(`line`, `column`), `fileName` and `data` (the message), which editor integrations without
an LSP client (for example a quickfix list) can consume. The doctor's `proof-build` check reports
whether the tutorial's imports are built.
