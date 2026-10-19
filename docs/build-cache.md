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
| `AIR2LEAN_BUILD_LOCK`, `AIR2LEAN_LOCK_WAIT` | build-guard lock (keep the default: one per machine, see below) and lock wait (seconds) of the heavy steps |
| `AIR2LEAN_BUILD_MEM_MIB` | memory budget of all guarded workloads of the machine (default 75% of RAM) |
| `AIR2LEAN_REGEN_RSS_MIB` | `scripts/regen.sh`: the RSS limit of its guarded builds (default 11000) |

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

Lean files outside the root package's libraries that need compiled outputs are built by a Lake
package that requires the root package by path, so the same Lake artifact cache covers them:
`tests/diff` and `tests/floatmodel` (executables), and the proof fixtures (`tests/roadmap`, below).

## Proof fixtures

The Lean files of the proof fixtures (`tests/roadmap/<fixture>/check.sh`) are one Lake package,
`tests/roadmap/lakefile.toml` (name `fixtures`), with one library per fixture directory: its
`srcDir` is the directory, so a module's name is its path below it (`AllocArena.Core`,
`ArenaSpec`). The outputs go to `tests/roadmap/.lake/build`, outside the root
`.lake/build/lib/lean`, where proof receipts reject untracked compiled modules. Converted so far:
`alloc-arena`, `alloc-fba`, `alloc-translated`, `lists-fba` (and the two `interfaces` modules it
imports) and the architecture-audit claim fixtures; the other checks still elaborate with
`lake env lean`.

`scripts/fixtures.py` is the one entry point; a converted check runs nothing else on Lean files:

| command | what it does |
| --- | --- |
| `fixtures.py build [TARGET...]` | `lake build` of fixture libraries or modules (no target: every library) in the package, through `cas.py run`. Lake also builds the root-package modules they import, into the root `.lake/build`. |
| `fixtures.py audit --module M... [--theorem NAME]...` | `scripts/assumptions.py --no-build` over the built modules: the axioms come from the compiled environment, with kernel replay (`leanchecker`), not from a message log. Fails unless every theorem of the modules uses only `propext`, `Classical.choice`, `Quot.sound`, no audited declaration depends on `sorry`, and every named theorem exists. |
| `fixtures.py mutant NAME --src DIR --fails M [--expect TEXT]...` | a negative check: DIR is the fixture's sources with one mutation, built as a workspace of its own (`tests/roadmap/.lake/mutants/NAME`). `lake build M` must fail on M itself: Lake's list of failed targets is exactly M, an error is located in M's source, and each `--expect` text occurs. A failed import, a missing module or a killed process is not a kill. |
| `fixtures.py files` | the package's module files (`lean-deps.py` does not treat them as standalone files) |

**Reuse is Lake's trace, nothing else.** A module is elaborated again exactly when its trace
changes: its source, the trace of every import (fixture or root-package module, transitively), the
toolchain, the options, the module and package names. A check that runs again on an unchanged tree
elaborates nothing; an edit to a proof file, to an imported `ZigLean` module or to a retained
translation rebuilds that module and everything that imports it. Every check still runs every
step: the translator comparison, the audit, the mutants and the native runs run each time, so a
check result is never reused.

**Translations.** A retained translation (`AllocFba/Gen.lean`, `AllocArena/ArenaLinux.lean`, ...)
is a tracked module of the library. The check first translates the AIR afresh and requires the
output to be byte-identical (`cmp`), then builds: a changed translator output fails the comparison
before any proof runs, and a regenerated file has new content, so a new trace.

**Mutants** are other files: copying the fixture's modules with one changed keeps every module
name, and a workspace of their own keeps the two apart (in one workspace Lake would build only
one of two same-named modules). The mutant workspace has the package name `fixtures`, which is
part of a module's trace: an unchanged copy has the fixture module's trace (an artifact-cache
hit), the mutated module and its dependents have their own. A failing build is never cached, so
the module that must fail is elaborated on every run.

**Module names are unique by check.** Lake builds only one of two modules with the same name in
two libraries and reports success for both (seen with Lake 4.34: the second library's
ill-typed `Eval` was never elaborated). `fixtures.py` therefore refuses to build unless every
first component of a module name, and every library root, belongs to one library, and none is a
root of a root-package library (`ZigLean`, `Air2Lean`, `Proofs`, `tools`). That is why each
fixture's `Eval.lean` lives below its namespace (`AllocArena/Eval.lean`).

**Sharing across worktrees.** With `AIR2LEAN_CAS_DIR` set, `cas.py run` turns on Lake's artifact
cache. The trace does not contain the checkout's path, so a fixture module built in one worktree
is restored as a hard link in every other worktree with the same inputs, and so is an unchanged
mutant copy. Without the variable (CI) the package builds into its own `.lake` like any Lake
package.

**One mode.** Every elaboration of a converted fixture goes through Lake (proofs, `#guard` files,
obstructions, counterexamples, mutants), so the precompiled `fsym` engine of step 2
(`precompileModules`, loaded by Lake for its own builds) applies to all of them at once, and a
mutant cannot fail on a heartbeat budget that the native proof meets. The remaining `lake env
lean` in these checks is the audit driver of `assumptions.py`, which loads oleans and runs no
tactic (`maxHeartbeats 0`).

**Builds in parallel.** Lake has no build lock. `scripts/full-build.sh` builds every fixture
library once before the parallel fixture checks, so their `lake build` calls find the modules
built; `scripts/build-guard.py` keeps two guarded workloads of one checkout apart.

Lean is not byte-reproducible from run to run: two plain cold builds of the same tree can differ
in a few `.olean` files (elaboration order inside a module). The cache does not add or remove
such differences: a warm build restores exactly the bytes of the build that populated the entry
(verified: cold cache build and warm build of `ZigLean Air2Lean air2lean` are byte-identical in
every `.olean`, `.ilean`, `.c` and the executable).

Proof receipts (`scripts/proof-receipt.py`) refuse any `LAKE_*` environment overlay, so a
receipt never runs with the cache variables; `scripts/regen.sh` removes them for the provenance
step. The hard-linked outputs it finds in `.lake/build` are ordinary up-to-date Lake outputs.

## Use

A new worktree starts with one command:

    scripts/worktree-init.sh [--zig 0.16.0 ...] [--no-lean] [--no-generated]

It builds what CI's `lake` job builds (ZigLean, Air2Lean, air2lean, Proofs, AssuranceTools, every
tracked ZigLean module) and the `tests/diff` package through `cas.py run` under build-guard,
then the requested patched compilers and the whole-tree generated files. With the cache on, a
module is compiled only if no worktree has built it with the same inputs; the rest are restored
as hard links. Measured on the dev Mac (2026-10-12, main 9ea4c9b6, fresh `git worktree add`):

| start | root package | whole init |
| --- | --- | --- |
| `AIR2LEAN_CAS_DIR` unset (plain Lake build) | 399 s | 435 s |
| cache from an older `main` (some modules changed since) | 48 s | 66 s |
| cache already holding this tree's modules | 1 s | 15 s |

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

Heavy workloads (Lake builds, Lean checks, patched-compiler builds) run under
`scripts/build-guard.py`, which admits them within one memory budget for the whole machine
(`AIR2LEAN_BUILD_MEM_MIB`, default 75% of RAM, in slots of 1 GiB): a workload reserves its
`--rss-mib`, which the guard enforces as a hard limit, so several worktrees build at once while
memory allows, and the rest wait in arrival order. Two workloads in one checkout never overlap
(Lake has no build lock of its own) unless both pass `--shared-workspace`; `--exclusive` runs a
workload alone (timing measurements such as `perf-budgets.py record`): while it waits nothing new
is admitted, and it runs once the running workloads have ended
([build-budgets.md](build-budgets.md#admission)). Every agent uses the one
default lock, `~/.cache/air2lean/build.lock`: a private lock lane (another
`AIR2LEAN_BUILD_LOCK`) escapes the budget and makes the machine thrash, so do not use one. With
the old single exclusive lock, guarded runs over two days waited 12061 s in total for 8493 s
of work, one at a time on an 18-core machine (2026-10-15).

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
fixture report (`tests/roadmap/claims/check.sh --write`); the architecture-audit exposure report
(`tests/roadmap/architecture-audit/claims/build.sh`, which also builds the libraries the fixtures
import: one guarded run, so one build-lock admission); theorem inventory (every recorded run
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
