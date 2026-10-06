#!/usr/bin/env bash
# Invoke only under ROOT's serialized compiler guard. No toolchain provisioning here.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case "$#:${1:-}" in
  0:|1:--synthetic-only) ;;
  *) echo 'usage: local-parent/check.sh [--synthetic-only]' >&2; exit 2 ;;
esac
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-local-parent.XXXXXX")
case "${AIR2LEAN_LOCAL_PARENT_KEEP_WORK:-0}" in
  0) trap 'rm -rf "$work"' EXIT ;;
  1) trap 'echo "retained fresh local parent artifacts: $work"' EXIT ;;
  *) rm -rf "$work"; echo 'KEEP_WORK must be 0 or 1' >&2; exit 2 ;;
esac
python3 tests/roadmap/local-parent/test_harness.py
lake build Air2Lean Air2Lean.Check Air2Lean.Emit ZigLean air2lean
lake env lean tests/roadmap/local-parent/Proofs.lean
lake env lean --run tests/roadmap/local-parent/Pipeline.lean "$work/generated"
for source in "$work/generated/"*.lean; do lake env lean -R "$work/generated" "$source"; done
python3 tests/roadmap/local-parent/mutations.py "$work/generated" "$work/mutants"
if [ "${1:-}" = --synthetic-only ]; then exit 0; fi
version=${AIR2LEAN_LOCAL_PARENT_ZIG_VERSION:-0.16.0}
[ "$version" = 0.16.0 ] || { echo 'only Zig 0.16.0 is qualified by this slice' >&2; exit 2; }
zig_air=${AIR2LEAN_LOCAL_PARENT_ZIG_AIR:-"$repo_root/zig-air-$version/bin/zig"}
zig_stock=${AIR2LEAN_LOCAL_PARENT_ZIG_STOCK:-zig}
[ "$("$zig_stock" version)" = "$version" ] || { echo 'stock compiler version mismatch' >&2; exit 1; }
[ "$("$zig_air" version)" = "$version" ] || { echo 'exporter version mismatch' >&2; exit 1; }
"$zig_stock" test tests/roadmap/local-parent/source.zig -OReleaseSafe
mkdir -p "$work/air"
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER=source. "$zig_air" \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing tests/roadmap/local-parent/source.zig
python3 tests/roadmap/local-parent/native_checks.py "$work/air" "$version" "$work/native-checks.lean"
.lake/build/bin/air2lean "$work/air" -o "$work/native.lean" --namespace LocalParentNative --prefix source.
cat "$work/native-checks.lean" >> "$work/native.lean"
lake env lean -R "$work" "$work/native.lean"
echo 'local parent native/export/generated checks passed: Zig 0.16.0'
