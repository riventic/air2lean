#!/usr/bin/env bash
# The proof-fixture checks CI runs (scripts/fixture-checks.py, docs/ci.md#full-build), under
# scripts/build-guard.py and through the shared cache; scripts/full-build.sh runs it last.
#
#   scripts/fixture-checks.sh [--logs DIR] [--only TEXT]... [--jobs N] [--rss-mib M] [--lean-threads T] [--rerun]
#
# The units' compilers are resolved first, outside the guard (a patched-compiler miss builds
# under its own guard). A unit with a recorded pass of exactly its inputs does not run
# (scripts/fixture-checks.py; --rerun: every unit runs); when no unit is left, nothing waits for
# the guard. The others run up to --jobs at once (default 8) in an elastic --rss-mib
# guard (default 4096, at most an enclosing guard's admission: scripts/full-build.sh;
# docs/build-budgets.md#elastic-workloads), each unit's Lake with up to --lean-threads Lean
# processes (default 1), the longest first, each unit a sub-admission charged its measured peak
# (scripts/fixture-checks.py `schedule`), and each Lean process of the proof-fixture package's
# build one charged its module's (scripts/lean-peaks.py). Without room for that (a small budget,
# inside a plain admission) the guard is plain, at most 11000 MiB or the enclosing limit, and the
# units' requests share it. Each unit's wall time, peak RSS and time by process kind go to
# DIR/units.json; the longest are printed. The guard waits up to AIR2LEAN_LOCK_WAIT seconds
# (default 3600) for the build lock.
set -euo pipefail
cd "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

logs= args=() jobs=8 rss= threads=1
while [ $# -gt 0 ]; do
  case $1 in
    --logs) logs=${2:?--logs needs a directory}; shift 2 ;;
    --jobs) jobs=${2:?--jobs needs a number}; shift 2 ;;
    --rss-mib) rss=${2:?--rss-mib needs a number}; shift 2 ;;
    --lean-threads) threads=${2:?--lean-threads needs a number}; shift 2 ;;
    --only) args+=("$1" "${2:?$1 needs a value}"); shift 2 ;;
    --rerun) args+=("$1"); shift ;;
    -h|--help) sed -n '2,19p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "fixture-checks: unknown argument $1" >&2; exit 2 ;;
  esac
done
# The guard's mode and limit (build-guard.py `elastic_plan`).
read -r mode rss < <(python3 -B scripts/build-guard.py --elastic-plan "${rss:-4096}")
elastic=()
[ "$mode" = plain ] || elastic=(--elastic)
[ -n "$logs" ] || logs=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-fixture-checks.XXXXXX")
mkdir -p "$logs"

python3 -B scripts/fixture-checks.py --prepare ${args[@]+"${args[@]}"}
start=$SECONDS
# The same environment as the guarded run below (the shared cache's Lake variables), so the same keys.
if python3 -B scripts/cas.py run -- python3 -B scripts/fixture-checks.py --pending ${args[@]+"${args[@]}"}; then
  echo "fixture-checks: $((SECONDS - start)) s"
  exit 0
fi
if ! python3 -B scripts/cas.py run -- python3 -B scripts/build-guard.py --cwd "$PWD" ${elastic[@]+"${elastic[@]}"} \
    --lean-threads "$threads" --jobs "$jobs" --rss-mib "$rss" --report "$logs/fixtures.json" --log "$logs/fixtures.log" \
    --timeout 28800 --lock-wait "${AIR2LEAN_LOCK_WAIT:-3600}" -- \
    python3 -B scripts/fixture-checks.py --logs "$logs/units" --report "$logs/units.json" \
    ${args[@]+"${args[@]}"}; then
  grep '^fixture-checks' "$logs/fixtures.log" >&2 || true
  echo "fixture-checks: failed (log: $logs/fixtures.log)" >&2
  exit 1
fi
# The longest units (per-unit rows of every unit: $logs/units.json), the totals, the native runs.
sed -n '/^fixture-checks: longest/,/^fixture-checks: [0-9]/p;/native runs/p' "$logs/fixtures.log"
echo "fixture-checks: $((SECONDS - start)) s"
