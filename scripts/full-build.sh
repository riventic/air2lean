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
#   - the proof-fixture package (tests/roadmap/lakefile.toml, `scripts/fixtures.py build`): every
#     fixture library, so the parallel checks below find their modules built; then the
#     proof-fixture checks (`scripts/fixture-checks.sh`): every CI step that runs the check.sh
#     of a fixture with Lean files (they elaborate the files that import a fixture's own generated
#     modules), derived from .github/workflows/ci.yml, with the patched and stock compilers from
#     the shared cache. Every unit runs on every invocation; no result is reused. --no-fixtures
#     skips this phase (scripts/worktree-init.sh).
#   - debug-ID canonicalization: complete native Func binding for every gen-integrity case,
#     plus one fresh independent Assurance replay of the generic CanonSem theorem module.
#     This phase always checks; it has no cached-success marker.
# Lake runs up to LEAN_NUM_THREADS (--lean-threads) Lean processes at once, and the guard's
# --rss-mib bounds their sum. Defaults: as many processes at 11000 MiB each (under the 12 GB
# per-process cap) as fit in what no other guarded workload holds when the build starts, at most
# half the machine's memory budget and one per core, at least one: --lean-threads
# max(1, min(cores, budget / 2 / 11000, free / 11000)), --rss-mib 11000 times that (budget and
# free slots: build-guard.py, AIR2LEAN_BUILD_MEM_MIB or 75% of physical memory; 64 GB, 18 cores,
# nothing else running: 2 processes, 22000 MiB). So the build asks for no more than is free and
# does not hold the admission queue for slots other agents' builds hold. The guard waits up to
# AIR2LEAN_LOCK_WAIT seconds (default 3600) for the build lock. All phases run in one admission
# (below). Prints each phase's time.
set -euo pipefail
cd "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

targets() {  # one derivation from lakefile.toml, shared with the per-check builds (lean-deps.py --build)
  python3 -B scripts/lean-deps.py --all
}

per_process=11000 threads= rss= logs= fixtures=1
while [ $# -gt 0 ]; do
  case $1 in
    --targets) targets; exit 0 ;;
    --lean-threads) threads=${2:?--lean-threads needs a number}; shift 2 ;;
    --rss-mib) rss=${2:?--rss-mib needs a number}; shift 2 ;;
    --logs) logs=${2:?--logs needs a directory}; shift 2 ;;
    --no-fixtures) fixtures=0; shift ;;
    -h|--help) sed -n '2,41p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "full-build: unknown argument $1" >&2; exit 2 ;;
  esac
done
if [ -z "$threads" ]; then
  threads=$(python3 -B - "$per_process" <<'PY'
import importlib.util, os, sys
spec = importlib.util.spec_from_file_location('guard', 'scripts/build-guard.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
per_process, budget = int(sys.argv[1]), guard.default_budget_mib()
print(max(1, min(os.cpu_count() or 1, budget // 2 // per_process, guard.free_mib(budget_mib=budget) // per_process)))
PY
)
fi
[ -n "$rss" ] || rss=$((threads * per_process))
[ -n "$logs" ] || logs=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-full-build.XXXXXX")
mkdir -p "$logs"

# One admission for the whole build: this script runs again inside one guard, and each phase's
# guard inherits that admission (build-guard.py, INHERIT) instead of queueing again. The phases
# keep their own limits and reports, each within $rss (the fixture checks' guard,
# scripts/fixture-checks.sh: 11000 MiB). A phase guard above it fails (inheritance_refused).
if [ -z "${AIR2LEAN_FULL_BUILD_INNER:-}" ]; then
  inner=(--lean-threads "$threads" --rss-mib "$rss" --logs "$logs")
  [ "$fixtures" = 1 ] || inner+=(--no-fixtures)
  echo "full-build: $threads Lean processes, one admission of $rss MiB (logs: $logs)"
  status=0
  AIR2LEAN_FULL_BUILD_INNER=1 python3 -B scripts/build-guard.py --cwd "$PWD" --lean-threads "$threads" \
    --jobs 8 --rss-mib "$rss" --report "$logs/full-build.json" --log "$logs/full-build.log" \
    --timeout 28800 --lock-wait "${AIR2LEAN_LOCK_WAIT:-3600}" -- bash "$0" "${inner[@]}" || status=$?
  grep -E '^(full-build|fixture-checks)' "$logs/full-build.log" || true
  exit "$status"
fi

guarded() {  # guarded NAME DIR CMD...: CMD in DIR under build-guard, through the shared Lake cache
  local name=$1 dir=$2 start=$SECONDS
  shift 2
  if ! python3 -B scripts/cas.py run -- python3 -B scripts/build-guard.py --cwd "$dir" \
      --lean-threads "$threads" --jobs "${jobs:-1}" --rss-mib "$rss" \
      --report "$logs/$name.json" --log "$logs/$name.log" --timeout 7200 \
      --lock-wait "${AIR2LEAN_LOCK_WAIT:-3600}" -- "$@"; then
    echo "full-build: $name failed (log: $logs/$name.log)" >&2
    exit 1
  fi
  echo "full-build: $name $((SECONDS - start)) s"
}

# The precompiled fsym libraries (docs/build-cache.md#precompiled-fsym): FsymDeps must be the import
# closure of Fsym and Lake must build them as listed, else an importer of Auto fails to load them.
python3 -B scripts/lean-deps.py --precompiled check || { echo 'full-build: precompiled libraries are stale' >&2; exit 1; }
root=()
# The mandatory canon phase below includes structural case coverage (ledger #case-family-enrollment).
while IFS= read -r target; do root+=("$target"); done < <(targets)
guarded root "$PWD" lake build "${root[@]}"
guarded diff "$PWD/tests/diff" lake build Outcome ScheduleSearch Concurrent
# Lean files that only a `lake env lean` elaborates (strength logs, fixtures, tutorials): the
# libraries' modules cannot import them. Up to 3 at once (the guard's memory budget); results are
# remembered per input (lean-deps.py), so an unchanged file costs nothing.
jobs=3 guarded files "$PWD" python3 -B scripts/lean-deps.py --elaborate
# Retain per-case native binding evidence and the one generic kernel audit beside the logs.
canon_artifacts=$(mktemp -d "$logs/canon.XXXXXX")
# Its per-case bindings run on AIR2LEAN_JOBS threads (scripts/canon_certification.py), light on
# memory: one per Lean process of the budget.
jobs=$threads guarded canon "$PWD" python3 -I -B scripts/gen-integrity.py certify --work-dir "$canon_artifacts/work"
# The proof-fixture package (tests/roadmap/lakefile.toml), every library, then the proof-fixture
# checks CI runs, in their own guard (scripts/fixture-checks.sh). Built first, once: the checks run
# in parallel, and two Lake builds of one workspace must not build the same module at once.
if [ "$fixtures" = 1 ]; then
  guarded fixtures-lean "$PWD" python3 -B scripts/fixtures.py build
  # Within this build's admission ($rss): the units share it, the longest first, each admitted by
  # its measured peak (scripts/fixture-checks.py `schedule`).
  scripts/fixture-checks.sh --logs "$logs/fixtures" --rss-mib "$rss" --jobs 8 \
    || { echo 'full-build: fixtures failed' >&2; exit 1; }
fi
