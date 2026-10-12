# Shared build cache and regeneration

Two tools take the repetitive shell work out of a worktree's life:

- `scripts/cas.py` (with `scripts/zig-air.sh`): a content-addressed cache that worktrees on one
  machine share, so each patched compiler, Lean module and AIR export is built once.
- `scripts/regen.sh`: one command that brings every generated file up to date, in dependency
  order, after merging `main`.

## The cache is opt-in: `AIR2LEAN_CAS_DIR`

The cache directory is set only by the environment variable `AIR2LEAN_CAS_DIR`. Unset or empty,
nothing is cached and nothing outside the worktree is read or written: `scripts/zig-air.sh`
builds `<worktree>/zig-air-<version>` as `zig-patch/build.sh` does by default, `cas.py run`
executes its command unchanged, and every Lake build is a plain `lake build`. CI does not set
it. On the dev Mac agents set it in their shell:

    export AIR2LEAN_CAS_DIR=$HOME/.cache/air2lean/cas

| variable | meaning |
| --- | --- |
| `AIR2LEAN_CAS_DIR` | cache root; unset or empty disables the cache |
| `AIR2LEAN_CAS_MAX_GIB` | size cap for `cas.py gc` (default 60) |
| `AIR2LEAN_HOST_ZIG_<v>` | stock Zig `<v>` (dots as `_`) that bootstraps a patched build; default `$AIR2LEAN_CACHE/host-<v>/zig`, else `zig` on `PATH` of that version |
| `AIR2LEAN_BUILD_LOCK`, `AIR2LEAN_LOCK_WAIT` | build-guard lane and lock wait (seconds) of the heavy steps |
| `AIR2LEAN_REGEN_RSS_MIB` | `scripts/regen.sh`: the RSS limit of its guarded builds (default 24576) |

## What is cached, and why a hit is always right

Every entry is stored under a key that hashes everything that determines its content. A changed
input is a different key, so an entry cannot be stale; it can only be missing.

| kind | path | key |
| --- | --- | --- |
| patched compiler | `zig/<version>-<key>/prefix` | the files `zig-patch/build.sh` reads for that version (`air-json/*.zig`, the hook patch, `build.sh`, `lock.sh`, `toml-get.sh`) and the version's `versions.toml` table (pinned tarball digest); the bootstrapping host Zig (binary SHA-256 and a digest of its `lib/`); host OS and architecture; `AIR2LEAN_OPTIMIZE`; the macOS `xcrun` shim. `AIR2LEAN_LLVM=1` builds are never cached. |
| Lean outputs | `lake/` | Lake's own artifact cache (`LAKE_ARTIFACT_CACHE`, `LAKE_CACHE_DIR`). Lake looks a module up by its input hash: the module's source, the traces of all its imports, the toolchain and the build options; outputs (`.olean`, `.ilean`, `.c`, ...) are stored by their content hash. `LAKE_RESTORE_ARTIFACTS` restores every output into `.lake/build` as a read-only hard link, so tools that read `.lake/build` see a normal build. |
| AIR export | `air/<key>` | the compiler entry's key, the export arguments and `ZIG_AIR_JSON_FILTER`, the host identity (OS, version, architecture, CPU; a native target depends on them) and every file under the root source's directory (a Zig module imports only files below its root). Only a plain `build-obj`/`build-exe`/`build-lib` of one `.zig` root with known flags into an empty output directory is cached; anything else (modules, C sources, libc, `ZIG_LIB_DIR`, a symlink under the module directory) runs uncached. |
| native build | `native/<key>` | `scripts/diff.sh`'s stock-Zig builds (`cas.py native -- ZIG build-exe\|build-lib ARGS`): the compiler binary and its `lib/` (path, size, mtime), the arguments, the target (the host identity without `-target`) and every `.zig`/`.zon` file under each source root's directory. The output (`-femit-bin`), stdout and stderr are stored and replayed. A tree that uses `@embedFile`, `ZIG_LIB_DIR` or no `-femit-bin` runs uncached. |
| pristine source | `src/zig-<version>-<sha256>` | the `versions.toml` tarball digest (checked before extraction) |

Lean is not byte-reproducible from run to run: two plain cold builds of the same tree can differ
in a few `.olean` files (elaboration order inside a module). The cache does not add or remove
such differences: a warm build restores exactly the bytes of the build that populated the entry
(verified: cold cache build and warm build of `ZigLean Air2Lean air2lean` are byte-identical in
every `.olean`, `.ilean`, `.c` and the executable).

Proof receipts (`scripts/proof-receipt.py`) refuse any `LAKE_*` environment overlay, so a
receipt never runs with the cache variables; `scripts/regen.sh` removes them for the provenance
step. The hard-linked outputs it finds in `.lake/build` are ordinary up-to-date Lake outputs.

## Use

    AIR2LEAN_ZIG_AIR=$(scripts/zig-air.sh 0.16.0)         # patched compiler for this checkout
    python3 scripts/build-guard.py ... -- python3 -B scripts/cas.py run -- lake build Proofs
    eval "$(python3 -B scripts/cas.py env)"                # or: this shell's Lake builds use it
    python3 -B scripts/cas.py air -- "$zig_air" build-obj -fno-emit-bin ... x.zig   # cached export
    python3 -B scripts/cas.py stats
    python3 -B scripts/cas.py gc [--max-gib 40]

`scripts/check.sh` exports through `cas.py air` when the cache is on; exports are cached only for
a compiler from the store, so point it there: `AIR2LEAN_ZIG_AIR=$(scripts/zig-air.sh 0.16.0)
scripts/check.sh`. (check.sh does not build a missing compiler itself: it often runs under
build-guard already, and a nested guarded build on the same lock would wait for itself.)
`scripts/preflight.sh` builds the translator through `cas.py run` and reads pristine sources
through `cas.py src`.

## Concurrency and eviction

Entries are built in `tmp/` and published by one `rename`; the marker `.cas.json` is written
before the rename, so a visible entry is complete. A per-key lock (`locks/`) makes concurrent
misses build once; the others wait and then hit. Lake writes its own entries (artifacts first,
then the input-to-output mapping; a torn or missing mapping is a miss). `cas.py gc` (run at the
end of `scripts/regen.sh`) evicts least recently used entries until the cache is below the cap:
directory entries by their last-hit stamp, Lake artifacts by the inode change time that each
restoring hard link updates; a Lake artifact still linked from a worktree frees nothing and is
skipped. Nothing used within the last hour (`--min-age`) is evicted. A deleted Lake artifact is
a miss: Lake rebuilds the module.

## `scripts/regen.sh`

Run it after every merge of `main`; do not write private regeneration scripts.

    scripts/regen.sh                  # everything; provenance last (commits PR-scoped outputs first)
    scripts/regen.sh --pr             # only PR-scoped files
    scripts/regen.sh --check [--pr]   # check only: scripts/preflight.sh
    scripts/regen.sh --list           # steps, scope, outputs
    scripts/regen.sh --only coverage,premises

Steps, in order (`scripts/regen.sh --list`): translator build; generated `Gen.lean` modules
(`gen-integrity.py write`, from committed AIR); CI matrix; trust report; op table; coverage
inventories (pristine sources); try-pointers input pins; premise index; support matrix; claims
fixture report (`tests/roadmap/claims/check.sh --write`); theorem inventory (every recorded run
whose recorded hashes no longer match is re-run with its recorded command and re-recorded); and
last provenance: when `provenance-evidence.py check --strict` or `replay --strict` fails, the
earlier (committed) outputs are committed, then `scripts/generated.py regen --group provenance-gap
--group provenance` regenerates both fixtures in place (the receipts need a clean tracked tree).

A step whose own check passes is skipped, so a second run changes nothing. Heavy steps run under
`scripts/build-guard.py` and are retried while the lock is busy (exit 75).

Scope: the `tree` steps generate the whole-tree files of `assurance/generated.json` (coverage
inventories, premise index, provenance fixtures). They are never committed: CI regenerates them
on every tested tree and publishes the merge queue's files on the `generated` branch
([ci.md](ci.md#whole-tree-generated-files)); `--pr` skips them. Every other step's output (op
table, try-pointers pins, support matrix, claims fixture, theorem inventory, translations, CI
matrix, trust report) is committed and checked in every CI run, so a PR regenerates it. Run records that need dedicated heavy runs (build-mode
records, performance budgets, mutation kills, exporter-hash fixture records) are checked by
`--check` and keep their own commands.
