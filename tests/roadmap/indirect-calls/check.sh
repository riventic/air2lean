#!/usr/bin/env bash
# Invoke only under ROOT's serialized compiler guard. No toolchain provisioning here.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
synthetic=1
native=1
case "$#:${1:-}" in
  0:) ;;
  1:--synthetic-only) native=0 ;;
  1:--native-only) synthetic=0 ;;
  *) echo 'usage: indirect-calls/check.sh [--synthetic-only|--native-only]' >&2; exit 2 ;;
esac
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-indirect-calls.XXXXXX")
case "${AIR2LEAN_INDIRECT_CALLS_KEEP_WORK:-0}" in
  0) trap 'rm -rf "$work"' EXIT ;;
  1) trap 'echo "retained fresh indirect call artifacts: $work"' EXIT ;;
  *) rm -rf "$work"; echo 'AIR2LEAN_INDIRECT_CALLS_KEEP_WORK must be 0 or 1' >&2; exit 2 ;;
esac
python3 tests/roadmap/indirect-calls/test_harness.py
lake build Air2Lean Air2Lean.Check Air2Lean.Emit ZigLean air2lean
if [ "$synthetic" = 1 ]; then
  lake env lean --run tests/roadmap/indirect-calls/Pipeline.lean "$work/generated"
  lake env lean -R "$work/generated" -o "$work/generated/Calls.olean" "$work/generated/Calls.lean"
  # Universal dispatch theorems about the fresh generated program. Compiled and audited (axioms,
  # sorry, kernel replay), not only elaborated: it is indexed (F2).
  python3 -B scripts/theorem_universe.py gate tests/roadmap/indirect-calls/Bridge.lean \
    --root tests/roadmap/indirect-calls --lean-path "$work/generated" --output-dir "$work/universe"
  python3 tests/roadmap/indirect-calls/mutations.py "$work/generated" "$work/mutants"
fi
if [ "$native" = 0 ]; then echo 'indirect call synthetic and kernel-proof regressions passed'; exit 0; fi
version=${AIR2LEAN_INDIRECT_CALLS_ZIG_VERSION:-0.16.0}
[ "$version" = 0.16.0 ] || { echo 'only Zig 0.16.0 is qualified by this slice' >&2; exit 2; }
zig_air=${AIR2LEAN_INDIRECT_CALLS_ZIG_AIR:-"$repo_root/zig-air-$version/bin/zig"}
zig_stock=${AIR2LEAN_INDIRECT_CALLS_ZIG_STOCK:-zig}
[ "$("$zig_stock" version)" = "$version" ] || { echo 'stock compiler version mismatch' >&2; exit 1; }
[ "$("$zig_air" version)" = "$version" ] || { echo 'exporter version mismatch' >&2; exit 1; }
"$zig_stock" test tests/roadmap/indirect-calls/source.zig -OReleaseSafe
mkdir -p "$work/air"
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER=source. "$zig_air" \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing tests/roadmap/indirect-calls/source.zig
python3 tests/roadmap/indirect-calls/native_checks.py "$work/air" "$version" "$work/native-checks.lean"
.lake/build/bin/air2lean "$work/air" -o "$work/native.lean" --namespace IndirectCallsNative --prefix source.
cat "$work/native-checks.lean" >> "$work/native.lean"
lake env lean -R "$work" "$work/native.lean"
echo 'indirect call native/export/generated checks passed: Zig 0.16.0'
