#!/usr/bin/env bash
# The proof-fixture checks CI runs (scripts/fixture-checks.py, docs/ci.md#full-build), under
# scripts/build-guard.py and through the shared cache; scripts/full-build.sh runs it last.
#
#   scripts/fixture-checks.sh [--logs DIR] [--base REF] [--only TEXT]...
#
# The compilers of the pending units are resolved first, outside the guard (a patched-compiler
# miss builds under its own guard), then up to 2 units run at once in an 11000 MiB guard. A pass
# is remembered per input key, so an unchanged tree takes seconds. --base REF runs only the units
# whose inputs changed since REF (scripts/fixture-checks.py --base). The guard waits up to
# AIR2LEAN_LOCK_WAIT seconds (default 3600) for the build lock.
set -euo pipefail
cd "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

logs= args=()
while [ $# -gt 0 ]; do
  case $1 in
    --logs) logs=${2:?--logs needs a directory}; shift 2 ;;
    --base|--only) args+=("$1" "${2:?$1 needs a value}"); shift 2 ;;
    -h|--help) sed -n '2,11p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "fixture-checks: unknown argument $1" >&2; exit 2 ;;
  esac
done
[ -n "$logs" ] || logs=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-fixture-checks.XXXXXX")
mkdir -p "$logs"

python3 -B scripts/fixture-checks.py --prepare ${args[@]+"${args[@]}"}
start=$SECONDS
if ! python3 -B scripts/cas.py run -- python3 -B scripts/build-guard.py --cwd "$PWD" \
    --lean-threads 2 --jobs 2 --rss-mib 11000 --report "$logs/fixtures.json" --log "$logs/fixtures.log" \
    --timeout 7200 --lock-wait "${AIR2LEAN_LOCK_WAIT:-3600}" -- \
    python3 -B scripts/fixture-checks.py --logs "$logs/units" ${args[@]+"${args[@]}"}; then
  grep '^fixture-checks' "$logs/fixtures.log" >&2 || true
  echo "fixture-checks: failed (log: $logs/fixtures.log)" >&2
  exit 1
fi
grep '^fixture-checks: [0-9]\|native runs' "$logs/fixtures.log" || true
echo "fixture-checks: $((SECONDS - start)) s"
