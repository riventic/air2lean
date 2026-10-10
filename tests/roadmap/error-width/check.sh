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
cp "$case_dir/RunCommon.lean" "$work/ErrorWidthRun.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/ErrorWidthRun.olean" "$work/ErrorWidthRun.lean"
"${lean_cmd[@]}" -R "$work" --run "$case_dir/Runtime.lean"
python3 "$case_dir/negatives.py" "$translator"

# Compiler exports (air-fresh): the patched 0.16.0, 0.15.2 and 0.14.1 at six widths each are
# translated, elaborated and executed with the same checks as the hand-written fixtures.
python3 "$case_dir/test_provenance.py"
export_imports=
export_runs=
for version in 0.16.0 0.15.2 0.14.1; do
  tag=V$(echo "$version" | cut -d. -f2)
  for bits in 2 8 10 16 17 32; do
    ns="EwExport${tag}B$bits"
    mkdir -p "$work/$ns"
    "$translator" "$case_dir/air-fresh/$version/bits$bits" -o "$work/$ns/Gen.lean" --namespace "$ns" --prefix error_width.
    "${lean_cmd[@]}" -R "$work" -o "$work/$ns/Gen.olean" "$work/$ns/Gen.lean"
    export_imports="${export_imports}import $ns.Gen
"
    export_runs="${export_runs}  run $bits ⟨$ns.storeError, $ns.storeOptional, $ns.loadOptional, $ns.unionTry8, $ns.unionTry64, $ns.setPayload, $ns.loadUnion⟩
"
  done
done
{
  echo 'import ErrorWidthRun'
  printf '%s' "$export_imports"
  echo 'open Zig ErrorWidthRun'
  echo 'def main : IO Unit := do'
  printf '%s' "$export_runs"
  echo '  IO.println "compiler exports: 3 versions x 6 error widths executed"'
} > "$work/RuntimeExport.lean"
"${lean_cmd[@]}" -R "$work" --run "$work/RuntimeExport.lean"

# Native observations (native.py, stock compilers) against the model; a native run of this
# host's compiler when AIR2LEAN_ZIG_NATIVE names a stock zig (then also checked).
# A deliberate, documented mismatch is listed in native/expected-mismatches-<version>.txt (none
# at present: 0.14.1's unnamed top-bit codes are a checked rejection in Model.lean).
expected_mismatches() {
  local file="$case_dir/native/expected-mismatches-$1.txt"
  if [ -f "$file" ]; then echo "$file"; fi
}
for version in 0.16.0 0.15.2 0.14.1; do
  "${lean_cmd[@]}" -R "$work" --run "$case_dir/Model.lean" "$case_dir/native/aarch64-macos-$version.txt" \
    $(expected_mismatches "$version")
done
# The comparison must notice a wrong model line, a wrong native line and a lost boundary.
mutant_check() {
  local version=$1 label=$2 pattern=$3 replacement=$4
  sed "s/$pattern/$replacement/" "$case_dir/native/aarch64-macos-$version.txt" > "$work/mutant.txt"
  if cmp -s "$work/mutant.txt" "$case_dir/native/aarch64-macos-$version.txt"; then
    echo "mutant '$label' did not change the observation" >&2; exit 1
  fi
  if "${lean_cmd[@]}" -R "$work" --run "$case_dir/Model.lean" "$work/mutant.txt" \
      $(expected_mismatches "$version") > /dev/null 2>&1; then
    echo "model comparison accepted the mutant '$label'" >&2; exit 1
  fi
}
mutant_check 0.16.0 'E!u8 payload offset' '^eu u8 1 1 4 2 0 2$' 'eu u8 1 1 4 2 2 0'
mutant_check 0.16.0 'code size' '^enc size 2 2$' 'enc size 4 4'
mutant_check 0.16.0 'errorFromInt upper bound' '^bound count 1000$' 'bound count 999'
mutant_check 0.16.0 'errorFromInt zero' '^bound zero panic$' 'bound zero ok'
mutant_check 0.16.0 'compile verdict' '^config lim255-over limit 255 total 256 compile fail$' 'config lim255-over limit 255 total 256 compile ok'
mutant_check 0.16.0 'defined code bytes' '^enc defined 3$' 'enc defined 4'
mutant_check 0.16.0 'unnamed top-bit code' '^name 512 E512$' 'name 512 '
# 0.14.1: names below the top bit are read and checked; names from it are not (out of bounds).
mutant_check 0.14.1 'unnamed code below the top bit' '^name 127 E115$' 'name 127 '
mutant_check 0.14.1 'errorFromInt rejects a top-bit code' '^bound count 65534$' 'bound count 32767'
mutant_check 0.14.1 'top-bit name read' '^names from 128 unread$' 'name 128 E116'
if [ -n "${AIR2LEAN_ZIG_NATIVE:-}" ]; then
  version=$("$AIR2LEAN_ZIG_NATIVE" version)
  python3 "$case_dir/native.py" "$AIR2LEAN_ZIG_NATIVE" "$work/native.txt"
  "${lean_cmd[@]}" -R "$work" --run "$case_dir/Model.lean" "$work/native.txt" \
    $(expected_mismatches "$version")
fi
echo "error widths passed: 4 widths x 7 fixtures translated, elaborated and executed; 3 compiler versions x 6 widths x 7 exports executed; native observations compared; rejections checked"
