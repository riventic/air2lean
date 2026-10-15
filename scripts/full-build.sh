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
#   - the proof-fixture checks (`scripts/fixture-checks.sh`): every CI step that runs the check.sh
#     of a fixture with Lean files (they elaborate the files that import a fixture's own generated
#     modules), derived from .github/workflows/ci.yml, with the patched and stock compilers from
#     the shared cache. Cached per input. --no-fixtures skips this phase (scripts/worktree-init.sh).
# Defaults: --lean-threads 2, --rss-mib 11000 (one job, under the 12 GB cap); the guard waits up to
# AIR2LEAN_LOCK_WAIT seconds (default 3600) for the build lock. A phase with nothing to do (`lake
# build --no-build`, `lean-deps.py --pending`, `fixture-checks.py --pending` pass) is not run
# under the guard, so it waits for no admission. Prints each phase's time.
set -euo pipefail
cd "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

targets() {  # one derivation from lakefile.toml, shared with the per-check builds (lean-deps.py --build)
  python3 -B scripts/lean-deps.py --all
}

threads=2 rss=11000 logs= fixtures=1
while [ $# -gt 0 ]; do
  case $1 in
    --targets) targets; exit 0 ;;
    --lean-threads) threads=${2:?--lean-threads needs a number}; shift 2 ;;
    --rss-mib) rss=${2:?--rss-mib needs a number}; shift 2 ;;
    --logs) logs=${2:?--logs needs a directory}; shift 2 ;;
    --no-fixtures) fixtures=0; shift ;;
    -h|--help) sed -n '2,27p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "full-build: unknown argument $1" >&2; exit 2 ;;
  esac
done
[ -n "$logs" ] || logs=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-full-build.XXXXXX")
mkdir -p "$logs"

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

repo=$PWD
up_to_date() {  # up_to_date NAME DIR CHECK...: CHECK (it changes nothing) passes: the phase has no
  local name=$1 dir=$2  # work, so it waits for no build-guard admission
  shift 2
  if (cd "$dir" && python3 -B "$repo/scripts/cas.py" run -- "$@") > /dev/null 2>&1; then
    echo "full-build: $name up to date"
    return 0
  fi
  return 1
}

root=()
while IFS= read -r target; do root+=("$target"); done < <(targets)
up_to_date root "$PWD" lake build --no-build "${root[@]}" || guarded root "$PWD" lake build "${root[@]}"
up_to_date diff "$PWD/tests/diff" lake build --no-build Outcome ScheduleSearch Concurrent ||
  guarded diff "$PWD/tests/diff" lake build Outcome ScheduleSearch Concurrent
# Lean files that only a `lake env lean` elaborates (strength logs, fixtures, tutorials): the
# libraries' modules cannot import them. Up to 3 at once (the guard's memory budget); results are
# remembered per input (lean-deps.py), so an unchanged file costs nothing.
up_to_date files "$PWD" python3 -B scripts/lean-deps.py --pending ||
  jobs=3 guarded files "$PWD" python3 -B scripts/lean-deps.py --elaborate
# The proof-fixture checks CI runs, in their own guard (scripts/fixture-checks.sh).
if [ "$fixtures" = 1 ]; then
  scripts/fixture-checks.sh --logs "$logs/fixtures" || { echo 'full-build: fixtures failed' >&2; exit 1; }
fi
