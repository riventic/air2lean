# Local CI

`scripts/local-ci.sh` runs the rows of `.github/workflows/ci.yml` on the development Mac, so
a PR is pushed green and GitHub CI only confirms it. The steps are read from `ci.yml` when the
script runs (conditions are evaluated by `scripts/local-ci-steps.py`'s `expression`), so they cannot
drift from CI.

```sh
scripts/local-ci.sh --part inputs --version 0.16.0   # one row
scripts/local-ci.sh --part golden --part lean        # every version's golden and lean rows
scripts/local-ci.sh --part ReleaseFast               # x86_64-linux native build mode (Rosetta)
scripts/local-ci.sh --part aarch64-linux             # a job by name
scripts/local-ci.sh --changed                        # the rows the diff against origin/main can affect
scripts/local-ci.sh --changed --list                 # which rows, and why, without running them
scripts/local-ci.sh --all                            # the whole CI (hours)
```

`--part` takes a part of the `test` job (`golden lean inputs native audit receipt Debug ReleaseFast
ReleaseSmall mutation`, `mutation:3` for one shard) or a job (`lake macos aarch64-linux
build-modes-aarch64-linux bitops-native-arm`). `--version` filters rows with a Zig version
(`test`, `macos`). Both repeat. Rows run one after another and a failing row does not stop the
others. At the end a table lists every row with its result and wall time; the exit status is 1 if any
row failed. The log of each row is `.lake/local-ci-results/run-*/<row>/row.log` (override the parent
with `AIR2LEAN_LOCAL_RESULTS`), next to the `steps.json` timings and the files CI would upload
(`uploads/`). `-v` prints each step as it starts.

The older modes (`targeted`, `full`, `matrix`, `mutations`; one container, release-record evidence)
still work and share the same toolchain and Lake volumes. Release evidence is still produced by those
modes.

## Where a row runs

| Row | Runs | How |
| --- | --- | --- |
| `macos` (per version) | the Mac itself (aarch64-macos) | private workspace `~/.cache/air2lean/local-ci/macos-work` |
| `aarch64-linux`, `build-modes-aarch64-linux`, `bitops-native-arm` | `linux/arm64` container | native |
| `lake`, every `test` row (x86_64-linux) | `linux/amd64` container | Rosetta on Apple silicon; `uname -m` is `x86_64` |

The image (`docker/local-ci.Dockerfile`) is Ubuntu 24.04 with the apt packages the CI steps need. Lean (elan),
the stock Zig releases and the patched compilers are not in the image: the CI install steps run as
written, once per recipe text, into persistent volumes (a changed recipe has a new text and therefore
runs again). The patched compiler is built from the tree with `zig-patch/build.sh` and cached under the key that
`ci.yml` computes (`hashFiles` of the exporter, hook, pins and build scripts).

The worktree is mounted read-only. Each row works in its own checkout of the *tracked* files as they are
on disk now (staged additions, unstaged edits and deletions included; `git add` a new file first), with
a private git history, so a test that rewrites generated files never touches your worktree and the
"checkout unchanged" step still means something. Persistent, named caches keep reruns incremental:

| Cache | Container volume (macOS: directory) |
| --- | --- |
| `.lake`, `tests/diff/.lake` | `air2lean-linux-<arch>-*-lake-*`, `-diff-*` (per toolchain and manifest) |
| elan and the Lean toolchain, stock and patched Zig, downloads, Zig global cache, harness builds | `air2lean-local-linux-toolchains` (amd64), `air2lean-local-linux-arm64-toolchains` (arm64), `~/.cache/air2lean/local-ci/tools-macos` |

## Resources and lanes

Heavy work goes through `scripts/build-guard.py`. Each row runs under it with a lock, a wall-clock
bound (the job's `timeout-minutes` times `--timeout-scale`, default 2) and a report
(`guard.json`).

* One Linux container at a time across all agents (lock `~/.cache/air2lean/local-ci-docker.lock`), one host
  row at a time (`local-ci-host.lock`). A second invocation waits (up to 8 hours) rather than overloading
  the Mac. The Docker Desktop VM has 16 CPUs and about 15 GiB; the container is capped at
  `--memory 9g --memory-swap 9g --cpus 6 --pids-limit 1024` (`AIR2LEAN_LOCAL_MEMORY`,
  `AIR2LEAN_LOCAL_CPUS`), `LEAN_NUM_THREADS=2`. The patched-compiler build peaks at about 8 GB.
* Hooks for a shared cache: `AIR2LEAN_LOCAL_PASSTHROUGH="NAME ..."` forwards those environment variables
  into the container and `AIR2LEAN_LOCAL_EXTRA_MOUNTS="SRC:DST ..."` bind-mounts host paths; host rows
  inherit the environment. The runner has no content-addressed cache of its own beyond the volumes above.
* `AIR2LEAN_LOCAL_LOCK_DIR` moves the lock files; `AIR2LEAN_LOCAL_CI_HOME` moves the host directories.
* The host needs Docker and Python 3 (a private venv with PyYAML is created on first use).

## `--changed`

The changed paths are the diff of the working tree against the merge base with `origin/main`
(`AIR2LEAN_LOCAL_BASE` replaces `origin/main`). A row is selected when:

* the path is in the pipeline for every row (`.github/`, `zig-patch/`, `docker/`, `scripts/local-ci*`,
  `compatibility.json`, Lean toolchain and manifests): all rows;
* it is translator, library, proof or corpus code (`Air2Lean/ ZigLean/ Proofs/ tools/ examples/ tests/golden/
  tests/diff/`, root `*.lean`): every row that builds Lean, except `lake` (it only warms the cache);
* it is documentation: the `inputs` row, plus `audit` for `docs/architecture-audit/`;
* otherwise a step of the row mentions the path, its directory, or a script that mentions it (followed
  transitively through `scripts/`), for example `scripts/diff.sh` selects the rows that run `check.sh`;
* if nothing refers to the path at all, the default version's test rows (no mutation shards), because
  an unreferenced file is more likely a missed reference than dead.

It errs on the side of running more. When the selection looks too small for what you changed, name
the rows yourself.

## What does not run as in CI

* `all-checks` only aggregates job results; there is nothing to run.
* Cache and upload actions are replaced by the persistent caches above and by copying the uploaded paths
  into `uploads/`; `actions/cache/save` is a no-op because the caches are updated in place.
* The `lake` job's build step is `continue-on-error` in CI (a failure only means no new cache). Locally
  a failure of that step fails the row.
* x86_64-linux runs under Rosetta, not on an Intel CPU: floating-point results are the same, timing and
  CPU-feature probes are not. Release-mode harnesses are linked with `-z norelro` (Rosetta cannot load the
  empty RELRO segment: `bss_size overflow`; `AIR2LEAN_DIFF_LINK_FLAGS`, see `docs/build-modes.md`), which
  does not change what the build-mode record compares.
* `macos` rows run on whatever macOS the Mac has, not `macos-14`; the user's own Zig, Lean and elan are
  taken off `PATH` for the steps.
