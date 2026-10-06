#!/usr/bin/env bash
# Root-only sequential compiler qualification for one exact Zig release.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
: "${AIR2LEAN_ZIG_AIR:?set the patched Zig AIR exporter}"
zig_stock=${AIR2LEAN_ZIG:-zig}
version=${AIR2LEAN_EXPECT_ZIG_VERSION:-0.16.0}
case "$version" in 0.14.1|0.15.2|0.16.0) ;; *) echo 'unsupported qualification version' >&2; exit 1;; esac
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-permutations.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/air" "$work/generated" "$work/mutants"
python3 -B tests/roadmap/byte-permutation/test_portable.py
[ "$("$zig_stock" version)" = "$version" ] || { echo 'stock Zig version mismatch' >&2; exit 1; }
[ "$("$AIR2LEAN_ZIG_AIR" version)" = "$version" ] || { echo 'patched Zig version mismatch' >&2; exit 1; }
lake build ZigLean Air2Lean air2lean
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER='byte_permutation.' "$AIR2LEAN_ZIG_AIR" \
  build-obj -fno-emit-bin -OReleaseSafe -target x86_64-linux -mcpu=baseline -fno-error-tracing tests/roadmap/byte-permutation/byte_permutation.zig
python3 -B tests/roadmap/byte-permutation/check_exports.py "$work/air"
lake exe air2lean "$work/air" -o "$work/Gen.lean" --namespace Permutations --prefix byte_permutation.
lake env lean -R "$work" "$work/Gen.lean"
lake env lean tests/roadmap/byte-permutation/Runtime.lean
lake env lean tests/roadmap/byte-permutation/Contracts.lean > "$work/Contracts.log"
lake env lean --run tests/roadmap/byte-permutation/Cases.lean "$work/generated"
for name in swap reverse swapLoop reverseLoop narrow; do
  [ -f "$work/generated/$name.lean" ] || { echo "missing generated permutation case: $name" >&2; exit 1; }
  lake env lean -R "$work/generated" --run "$work/generated/$name.lean"
done
cat "$work/Gen.lean" tests/roadmap/byte-permutation/DiffMain.lean.inc > "$work/Diff.lean"
"$zig_stock" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$work/native" \
  --dep permutations -Mroot=tests/roadmap/byte-permutation/native.zig -Mpermutations=tests/roadmap/byte-permutation/byte_permutation.zig
"$work/native" 2> "$work/native.txt"
lake env lean -R "$work" --run "$work/Diff.lean" > "$work/lean.txt"
[ "$(wc -l < "$work/native.txt" | tr -d ' ')" = 795 ] || { echo 'incomplete permutation observation corpus' >&2; exit 1; }
cmp "$work/native.txt" "$work/lean.txt"
python3 -B tests/roadmap/byte-permutation/mutations.py "$work/mutants"
lake env lean -R "$work/mutants" "$work/mutants/control.lean"
for name in reverse_is_identity swap_is_identity swap_reverses_bits byte_index_off_by_one reverse_negates_bits lane_order_reversed; do
  lean_status=0
  lake env lean -R "$work/mutants" "$work/mutants/$name.lean" > "$work/mutants/$name.log" 2>&1 || lean_status=$?
  python3 -B tests/roadmap/bitops/classify_mutant.py "$lean_status" "$work/mutants/$name.log"
done
python3 -B tests/roadmap/byte-permutation/manifest.py "$work" "$version" "$AIR2LEAN_ZIG_AIR" "$zig_stock"
if [ -n "${AIR2LEAN_PERMUTATIONS_OUT_DIR:-}" ]; then
  mkdir -p "$AIR2LEAN_PERMUTATIONS_OUT_DIR"
  cp -R "$work/." "$AIR2LEAN_PERMUTATIONS_OUT_DIR/"
fi
echo 'permutations passed: 30 fresh compiler functions, 5 generated fixtures, 795 exact differential rows, 6 semantic mutants'
