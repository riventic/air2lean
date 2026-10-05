#!/usr/bin/env bash
# Public filename qualification; reuse built tools and never emit or execute native code.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"
[ "$#" -eq 0 ] || { echo 'usage: check-export-names.sh (AIR2LEAN_ZIG_AIR required)' >&2; exit 2; }
zig_air=${AIR2LEAN_ZIG_AIR:?set AIR2LEAN_ZIG_AIR to an existing guarded patched compiler}
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$zig_air" ] && [ -x "$translator" ] || { echo 'export names: missing built compiler or translator' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-export-names.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/air"
fixture=tests/roadmap/export-names/export_names.zig
inspector=tests/roadmap/export-names/check_dump.py
# Separate local caches force fresh function analysis on every dump. All caches
# and generated artifacts are temporary, outside tracked files and shared caches.
dump() {
  ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER=export_names. "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$fixture" \
    --cache-dir "$work/cache-$1" --global-cache-dir "$work/global-cache"
}
dump 1
python3 "$inspector" "$work/air"
"$translator" "$work/air" -o "$work/Gen.lean" --namespace ExportNames \
  --prefix export_names. --profile abi64-le-v1
# A temporary package root permits checking a generated file outside the checkout.
lake env lean -R "$work" "$work/Gen.lean"
lake env lean tests/roadmap/export-names/Order.lean
python3 tests/roadmap/export-names/test_order_cli.py "$translator"
python3 "$inspector" "$work/air" --mode seed-reexport
dump 2
python3 "$inspector" "$work/air" --mode check-reexport
python3 "$inspector" "$work/air" --mode seed-collision
dump 3 2> "$work/collision.log"
python3 "$inspector" "$work/air" --mode check-collision
grep -Fq 'OutputIdentityCollision' "$work/collision.log" || {
  echo 'export names: missing explicit collision warning' >&2
  exit 1
}
echo 'export filename qualification passed'
