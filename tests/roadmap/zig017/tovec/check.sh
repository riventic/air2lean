#!/usr/bin/env bash
# Zig 0.17.1 `array_to_vector` gate (the coercion `[n]T` → `@Vector(n, T)`).
#   check.sh [--check]      check the committed AIR's lock (../exports.json; scripts/fixture-exports.py
#                           verify|export zig017 re-exports it), translate it, compare with the
#                           committed ToVec/Gen.lean,
#                           run it on inputs.txt and require every line to equal the stock Zig 0.17.1
#                           build (AIR2LEAN_ZIG_NATIVE) of native.zig: every lane kind, sentinels dropped.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/zig017/tovec
case "${1:---check}" in
  --check) ;;
  *) echo 'usage: check.sh [--check]' >&2; exit 2 ;;
esac
python3 -B scripts/fixture-exports.py check zig017
: "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig 0.17.1}"
[ "$("$AIR2LEAN_ZIG_NATIVE" version)" = 0.17.1 ] || { echo 'AIR2LEAN_ZIG_NATIVE is not Zig 0.17.1' >&2; exit 1; }
python3 -B scripts/lean-deps.py --build "$dir"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-tovec.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/ToVec"
"$translator" "$dir/air/0.17.1" -o "$work/ToVec/Gen.lean" --namespace ToVec --prefix tovec.
# The committed file has no profile header (it names the exporting host).
tail -n +2 "$work/ToVec/Gen.lean" | cmp - "$dir/ToVec/Gen.lean"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -R "$work" -o "$work/ToVec/Gen.olean" "$work/ToVec/Gen.lean"
lake env lean -R "$dir" --run "$dir/ToVec/Runtime.lean" "$dir/inputs.txt" > "$work/lean.txt"
"$AIR2LEAN_ZIG_NATIVE" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} -OReleaseSafe --dep tovec -Mroot="$dir/native.zig" \
  -Mtovec="$dir/tovec.zig" -femit-bin="$work/native" --cache-dir "$work/zig-cache"
"$work/native" > "$work/native.txt"
lines=$(wc -l < "$dir/inputs.txt")
[ "$(wc -l < "$work/lean.txt")" -eq "$lines" ] || { echo 'lean output is not one line per input' >&2; exit 1; }
diff "$work/lean.txt" "$work/native.txt"
echo "array_to_vector differential: $lines vectors equal"
