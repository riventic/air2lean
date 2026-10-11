#!/usr/bin/env bash
# L07: Zig ≤0.16 representation casts and optional-pointer conversions. Needs a built translator
# and `lake build ZigLean ZigLean.ReprCast Air2Lean`; runs no compiler (`export.sh --check`
# re-exports with the recorded patched compilers). `--native` also runs
# `probe.zig` with a stock Zig (AIR2LEAN_ZIG_NATIVE, 0.14.1-0.16.0) and compares its output.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/aggregate-casts
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-aggregate-casts.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AggregateCasts"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The committed exports are the recorded compiler outputs (no compiler runs here).
python3 "$here/test_provenance.py"
# The retained translation is the fresh 0.16.0 export's, byte for byte; the 0.15.2 and 0.14.1
# exports translate to the same text except the profile header (the version).
"$translator" "$here/air/0.16.0" -o "$work/AggregateCasts/Gen.lean" \
  --namespace AggregateCasts --prefix aggregate_casts.
cmp "$work/AggregateCasts/Gen.lean" "$here/AggregateCasts/Gen.lean"
for version in 0.15.2 0.14.1; do
  "$translator" "$here/air/$version" -o "$work/Gen-$version.lean" \
    --namespace AggregateCasts --prefix aggregate_casts.
  cmp <(tail -n +2 "$work/Gen-$version.lean") <(tail -n +2 "$here/AggregateCasts/Gen.lean")
done
# The earlier hand-written AIR (no safety checks) still translates.
"$translator" "$here/air-handwritten/0.16.0" --profile legacy-abi64-le -o "$work/Gen-handwritten.lean" \
  --namespace AggregateCasts --prefix aggregate_casts.
"${lean_cmd[@]}" -R "$work" -o "$work/AggregateCasts/Gen.olean" "$work/AggregateCasts/Gen.lean"
"${lean_cmd[@]}" -R "$here" "$here/AggregateCasts/Proofs.lean"
"${lean_cmd[@]}" --run "$here/Model.lean" "$here/aarch64-macos-ReleaseSafe.txt"
"${lean_cmd[@]}" --run "$here/Checker.lean"
python3 "$here/negatives.py" "$translator"
if [ "${1:-}" = --native ]; then
  zig=${AIR2LEAN_ZIG_NATIVE:?set AIR2LEAN_ZIG_NATIVE to a stock Zig 0.14.1-0.16.0}
  "$zig" run -OReleaseSafe "$here/probe.zig" 2> "$work/observed.txt"
  "${lean_cmd[@]}" --run "$here/Model.lean" "$work/observed.txt"
fi
