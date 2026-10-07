#!/usr/bin/env bash
# Dedicated L02 end-to-end gate. Every compiler invocation runs sequentially.
# Required: AIR2LEAN_ZIG_AIR=patched-0.16/bin/zig. Stock compiler: AIR2LEAN_ZIG (default zig).
# Optional: AIR2LEAN_BITOPS_OUT_DIR retains fresh artifacts and observations after success.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
: "${AIR2LEAN_ZIG_AIR:?set AIR2LEAN_ZIG_AIR to the patched Zig 0.16.0 AIR exporter}"
zig_stock=${AIR2LEAN_ZIG:-zig}
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-bitops.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/air" "$work/generated" "$work/mutants"
python3 -B tests/roadmap/bitops/test_classifier.py
[ "$("$zig_stock" version)" = 0.16.0 ] || { echo 'bitops requires stock Zig 0.16.0' >&2; exit 1; }
[ "$("$AIR2LEAN_ZIG_AIR" version)" = 0.16.0 ] || { echo 'bitops requires patched Zig 0.16.0' >&2; exit 1; }
lake build ZigLean Air2Lean air2lean
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER='bitops.' "$AIR2LEAN_ZIG_AIR" \
  build-obj -fno-emit-bin -OReleaseSafe -target x86_64-linux -mcpu=baseline -fno-error-tracing tests/roadmap/bitops/bitops.zig
python3 - "$work/air" <<'PY_INVENTORY'
import json
import sys
from pathlib import Path
expected = {"counts8", "countsSigned8", "countsNarrow", "countsOne", "shiftUnsigned8", "shiftSigned8", "shiftNarrow", "shiftSignedNarrow", "leadingLanes", "trailingLanes", "populationLanes", "shiftLanes", "shiftSignedLanes", "firstSet", "clearLowest", "cardinality"}
files = list(Path(sys.argv[1]).glob("*.json"))
observed = {json.loads(p.read_text())["name"].removeprefix("bitops.") for p in files}
if observed != expected or len(files) != len(expected):
    raise SystemExit(f"bitops export inventory mismatch: observed={observed}, expected={expected}")
PY_INVENTORY
lake exe air2lean "$work/air" -o "$work/Gen.lean" --namespace Bitops --prefix bitops.
lake env lean -R "$work" -o "$work/Gen.olean" "$work/Gen.lean"
cp tests/roadmap/bitops/GeneratedBitset.lean "$work/GeneratedBitset.lean"
LEAN_PATH="$work:$(lake env printenv LEAN_PATH)" lake env lean -R "$work" "$work/GeneratedBitset.lean"
lake env lean tests/roadmap/bitops/Runtime.lean
lake env lean tests/roadmap/bitops/Bitset.lean
lake env lean --run tests/roadmap/bitops/Cases.lean "$work/generated"
for name in clz ctz popcount clzVector ctzVector popcountVector shiftUnsigned shiftSigned shiftNarrow shiftVector shiftSignedVector invalidShiftVector loopCapture clzWide ctzWide popcountWide shiftWide wideVector; do
  [ -f "$work/generated/$name.lean" ] || { echo "missing generated bitops case: $name" >&2; exit 1; }
  lake env lean -R "$work/generated" --run "$work/generated/$name.lean"
done
cat "$work/Gen.lean" tests/roadmap/bitops/DiffMain.lean.inc > "$work/Diff.lean"
"$zig_stock" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$work/native" \
  --dep bitops -Mroot=tests/roadmap/bitops/native.zig -Mbitops=tests/roadmap/bitops/bitops.zig
"$work/native" 2> "$work/native.txt"
lake env lean -R "$work" --run "$work/Diff.lean" > "$work/lean.txt"
[ "$(wc -l < "$work/native.txt" | tr -d ' ')" = 3092 ] || { echo 'incomplete bitops observation corpus' >&2; exit 1; }
cmp "$work/native.txt" "$work/lean.txt"
python3 tests/roadmap/bitops/mutations.py "$work/mutants"
lake env lean -R "$work/mutants" "$work/mutants/control.lean"
for name in clz_is_ctz ctz_is_clz population_is_zero signed_shift_is_unsigned overflow_flag_inverted oversized_shift_allowed reverse_shift_operands_swapped count_bound_operands_swapped; do
  lean_status=0
  lake env lean -R "$work/mutants" "$work/mutants/$name.lean" > "$work/mutants/$name.log" 2>&1 || lean_status=$?
  python3 tests/roadmap/bitops/classify_mutant.py "$lean_status" "$work/mutants/$name.log"
done
python3 tests/roadmap/bitops/manifest.py "$work" "$AIR2LEAN_ZIG_AIR" "$zig_stock"
if [ -n "${AIR2LEAN_BITOPS_OUT_DIR:-}" ]; then
  mkdir -p "$AIR2LEAN_BITOPS_OUT_DIR"
  # Preserve every manifest-listed artifact, including any compiler-created object files.
  cp -R "$work/." "$AIR2LEAN_BITOPS_OUT_DIR/"
fi
echo 'bitops passed: 16 exported functions, 18 generated fixtures, generated bitset proofs, 3092 exact differential observations (256 illegal narrow-shift rows excluded), 8 killed semantic mutants'
