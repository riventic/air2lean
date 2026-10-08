#!/usr/bin/env bash
# L07: Zig ≤0.16 representation casts and optional-pointer conversions. Needs a built translator
# and `lake build ZigLean ZigLean.ReprCast Air2Lean`; runs no compiler. `--native` also runs
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
# The retained translation is the fresh one, byte for byte.
"$translator" "$here/air/0.16.0" -o "$work/AggregateCasts/Gen.lean" \
  --namespace AggregateCasts --prefix aggregate_casts.
cmp "$work/AggregateCasts/Gen.lean" "$here/AggregateCasts/Gen.lean"
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
