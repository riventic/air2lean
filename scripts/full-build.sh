#!/usr/bin/env bash
# The full build: every Lean module of the repository's Lake packages, through scripts/build-guard.py
# and (with AIR2LEAN_CAS_DIR) the shared Lake artifact cache (docs/build-cache.md).
#
#   scripts/full-build.sh [--lean-threads N] [--rss-mib N] [--logs DIR] [--no-fixtures]
#   scripts/full-build.sh --targets      print the root package's targets, one per line
#
# A bare `lake build` builds only the default targets (ZigLean, Air2Lean, air2lean): the ZigLean
# root imports neither the full-state logic (ZigLean.Sep.Full.*) nor Proofs, so a check run with
# `lake env lean` after it can read stale oleans. "Full build" (docs/ci.md#full-build) means this
# script:
#   - first, in every tracked Lake package, the compiled outputs of modules deleted since they
#     were built (`lean-deps.py --prune-orphans`): Lake keeps them, and a kernel replay checks them;
#   - root package (`--targets`, also what CI's `lake` job builds): `scripts/lean-deps.py --all`,
#     every library and executable of lakefile.toml and every tracked module of each library
#     without explicit roots, whether or not a library root imports it (the per-check builds,
#     `lean-deps.py --build FILES`, derive their modules the same way);
#   - tests/diff: the Outcome, ScheduleSearch and Concurrent libraries (its executables link
#     archives that scripts/diff.sh builds with Zig; diff.sh builds them on use);
#   - the standalone Lean files (`lean-deps.py --elaborate`): every tracked .lean file outside the
#     libraries that imports only Lean and this package (strength logs, proof-client fixtures,
#     tutorials) is elaborated with `lake env lean`; the negative controls in
#     assurance/lean-files.json must be rejected. Cached per input.
#   - the proof-fixture checks (`scripts/fixture-checks.sh`), after the proof-fixture package
#     (tests/roadmap/lakefile.toml, `scripts/fixtures.py build`: every fixture library, built
#     first so the parallel checks find their modules built): every CI step that runs the check.sh
#     of a fixture with Lean files (they elaborate the files that import a fixture's own generated
#     modules), derived from .github/workflows/ci.yml, with the patched and stock compilers from
#     the shared cache. Every unit runs on every invocation; no result is reused. --no-fixtures
#     skips this phase (scripts/worktree-init.sh).
#   - debug-ID canonicalization: complete native Func binding for every gen-integrity case,
#     plus one fresh independent Assurance replay of the generic CanonSem theorem module.
#     This phase always checks; it has no cached-success marker.
# Memory is charged by need (docs/build-budgets.md#elastic-workloads). The build is one elastic
# admission of --rss-mib (default 4096 MiB: Lake, the scripts, the assurance extractor's build),
# held for all phases. Every Lean elaboration of the Lake phases (root, diff, files and the
# proof-fixture package) takes a sub-admission of its own while it runs, charged 1.3 x its
# module's measured peak (scripts/lean-peaks.py) and stopped and run again at 11000 MiB if it
# outgrows that; an unmeasured or changed module is charged 11000 MiB. So does each fixture-check
# unit (its measured peak, scripts/fixture-checks.py) and the canon phase (its recent runs). Lake
# runs up to --lean-threads Lean processes at once (default min(8, cores)), each on one Lean
# thread; the slots they hold, not the thread count, bound the memory, and other workloads are
# admitted beside them. The guards wait up to AIR2LEAN_LOCK_WAIT seconds (default 3600) for the
# build lock. Prints each phase's time.
set -euo pipefail
cd "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

targets() {  # one derivation from lakefile.toml, shared with the per-check builds (lean-deps.py --build)
  python3 -B scripts/lean-deps.py --all
}

threads= rss=4096 logs= fixtures=1
while [ $# -gt 0 ]; do
  case $1 in
    --targets) targets; exit 0 ;;
    --lean-threads) threads=${2:?--lean-threads needs a number}; shift 2 ;;
    --rss-mib) rss=${2:?--rss-mib needs a number}; shift 2 ;;
    --logs) logs=${2:?--logs needs a directory}; shift 2 ;;
    --no-fixtures) fixtures=0; shift ;;
    -h|--help) sed -n '2,44p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "full-build: unknown argument $1" >&2; exit 2 ;;
  esac
done
cores=$(python3 -c 'import os; print(os.cpu_count() or 1)')
[ -n "$threads" ] || threads=$((cores < 8 ? cores : 8))
[ -n "$logs" ] || logs=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-full-build.XXXXXX")
mkdir -p "$logs"

# One elastic admission for the whole build: this script runs again inside one guard, and each
# phase's guard inherits it (build-guard.py, INHERIT) instead of queueing again. The phases keep
# their own limits and reports, each within $rss; their sub-admissions hold slots of their own.
if [ -z "${AIR2LEAN_FULL_BUILD_INNER:-}" ]; then
  inner=(--lean-threads "$threads" --rss-mib "$rss" --logs "$logs")
  [ "$fixtures" = 1 ] || inner+=(--no-fixtures)
  echo "full-build: up to $threads Lean processes, each charged its measured need; elastic base $rss MiB (logs: $logs)"
  status=0
  AIR2LEAN_FULL_BUILD_INNER=1 python3 -B scripts/build-guard.py --cwd "$PWD" --elastic --lean-threads "$threads" \
    --jobs 8 --rss-mib "$rss" --report "$logs/full-build.json" --log "$logs/full-build.log" \
    --timeout 28800 --lock-wait "${AIR2LEAN_LOCK_WAIT:-3600}" -- bash "$0" "${inner[@]}" || status=$?
  grep -E '^(full-build|fixture-checks)' "$logs/full-build.log" || true
  exit "$status"
fi
sysroot=$(lean --print-prefix)  # the toolchain's: --lean-processes runs its lean through the guard
# Each Lean process's guard report (module, charge, wait, time, exact peak), beside the phase logs.
export AIR2LEAN_LEAN_REPORTS="$logs/lean-processes"
mkdir -p "$AIR2LEAN_LEAN_REPORTS"

# guarded NAME DIR [GUARD OPTION...] -- CMD...: CMD in DIR under build-guard (an inheriting guard
# of $rss, unless the options say otherwise), through the shared Lake cache.
guarded() {
  local name=$1 dir=$2 start=$SECONDS options=()
  shift 2
  while [ "$1" != -- ]; do options+=("$1"); shift; done
  shift
  [ ${#options[@]} -gt 0 ] || options=(--rss-mib "$rss")
  if ! python3 -B scripts/cas.py run -- python3 -B scripts/build-guard.py --cwd "$dir" \
      --lean-threads "$threads" --jobs "${jobs:-1}" "${options[@]}" \
      --report "$logs/$name.json" --log "$logs/$name.log" --timeout 7200 \
      --lock-wait "${AIR2LEAN_LOCK_WAIT:-3600}" -- "$@"; then
    echo "full-build: $name failed (log: $logs/$name.log)" >&2
    # The cause in this script's own output: the log may live in a temporary directory its caller
    # removes (scripts/preflight.sh). Its error lines, else its last lines; the prefix keeps them
    # in the outer summary (above).
    { grep -m 40 'error:' "$logs/$name.log" || tail -n 20 "$logs/$name.log"; } \
      | sed "s/^/full-build: $name | /" >&2 || true
    exit 1
  fi
  echo "full-build: $name $((SECONDS - start)) s"
}

# The precompiled fsym libraries (docs/build-cache.md#precompiled-fsym): FsymDeps must be the import
# closure of Fsym and Lake must build them as listed, else an importer of Auto fails to load them.
python3 -B scripts/lean-deps.py --precompiled check || { echo 'full-build: precompiled libraries are stale' >&2; exit 1; }
# Lake never removes what it compiled from a module deleted since, and the kernel-replay receipts
# check every olean below a module's name (scripts/assumptions.py `module_needs` refuses those).
python3 -B scripts/lean-deps.py --prune-orphans
root=()
# The mandatory canon phase below includes structural case coverage (ledger #case-family-enrollment).
while IFS= read -r target; do root+=("$target"); done < <(targets)
guarded root "$PWD" --rss-mib "$rss" --lean-processes "$sysroot" -- lake build "${root[@]}"
guarded diff "$PWD/tests/diff" --rss-mib "$rss" --lean-processes "$sysroot" -- lake build Outcome ScheduleSearch Concurrent
# Lean files that only a `lake env lean` elaborates (strength logs, fixtures, tutorials): the
# libraries' modules cannot import them. Up to $threads at once, each `lean` its own sub-admission
# (the guard's --rss-mib holds only the `lake env` processes); results are remembered per input
# (lean-deps.py), so an unchanged file costs nothing.
jobs=$threads guarded files "$PWD" --rss-mib "$rss" --lean-processes "$sysroot" -- \
  python3 -B scripts/lean-deps.py --elaborate --mem-mib 256
# Retain per-case native binding evidence and the one generic kernel audit beside the logs.
canon_artifacts=$(mktemp -d "$logs/canon.XXXXXX")
# Its per-case bindings run on AIR2LEAN_JOBS threads (scripts/canon_certification.py), light on
# memory. A sub-admission charged by its recent runs (at most 11000 MiB): it holds its slots only
# while it runs, and its kernel audit sees the toolchain's own sysroot.
jobs=2 guarded canon "$PWD" --sub-admission --rss-mib 11000 --lean-threads 1 -- \
  python3 -I -B scripts/gen-integrity.py certify --work-dir "$canon_artifacts/work"
# The proof-fixture checks CI runs, in their own guard (scripts/fixture-checks.sh). It builds the
# proof-fixture package (tests/roadmap/lakefile.toml), every library, first, once: the checks run
# in parallel, and two Lake builds of one workspace must not build the same module at once.
if [ "$fixtures" = 1 ]; then
  # Within this build's elastic admission: the package's Lean processes and the units take
  # sub-admissions, each unit charged its measured peak (scripts/fixture-checks.py `schedule`).
  scripts/fixture-checks.sh --logs "$logs/fixtures" --rss-mib "$rss" --jobs 8 --lean-threads 1 \
    || { echo 'full-build: fixtures failed' >&2; exit 1; }
fi
