#!/usr/bin/env bash
# L10 error-code widths: fixtures, translation, generated-code execution and rejections.
# Build first: lake build ZigLean ZigLean.Mem.ErrWidthLemmas Air2Lean air2lean
# Set AIR2LEAN_ERROR_WIDTH_UPDATE=1 to rewrite expected/ after a deliberate emitter change.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case_dir=tests/roadmap/error-width
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-error-width.XXXXXX")
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"

python3 "$case_dir/make-fixtures.py" check
for bits in 16 8 10 17; do
  ns="ErrorWidth$bits"
  mkdir -p "$work/$ns"
  "$translator" "$case_dir/air/bits$bits" -o "$work/$ns/Gen.lean" --namespace "$ns" --prefix error_width.
  if [ "${AIR2LEAN_ERROR_WIDTH_UPDATE:-0}" = 1 ]; then
    cp "$work/$ns/Gen.lean" "$case_dir/expected/$ns.lean"
  fi
  cmp "$work/$ns/Gen.lean" "$case_dir/expected/$ns.lean"
  "${lean_cmd[@]}" -R "$work" -o "$work/$ns/Gen.olean" "$work/$ns/Gen.lean"
done
# The default width keeps the original 2-byte operations; other widths name theirs.
if grep -q 'W 16\b' "$work/ErrorWidth16/Gen.lean"; then
  echo 'ErrorWidth16 names a width-16 operation' >&2; exit 1
fi
grep -q 'Zig.errorEnc (' "$work/ErrorWidth16/Gen.lean"
for bits in 8 10 17; do
  grep -q "Zig.errorEncW $bits " "$work/ErrorWidth$bits/Gen.lean"
  grep -q "Zig.finiteTryPayloadPtrW $bits " "$work/ErrorWidth$bits/Gen.lean"
  if grep -q 'Zig.errorEnc (' "$work/ErrorWidth$bits/Gen.lean"; then
    echo "ErrorWidth$bits uses the 2-byte error dictionary" >&2; exit 1
  fi
done
"${lean_cmd[@]}" -R "$work" --run "$case_dir/Runtime.lean"
python3 "$case_dir/negatives.py" "$translator"
echo "error widths passed: 4 widths x 7 fixtures translated, elaborated and executed; rejections checked"
