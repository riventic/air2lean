#!/usr/bin/env bash
# L07: Zig ≤0.16 representation casts and optional-pointer conversions. Needs a built translator
# and `lake build ZigLean ZigLean.ReprCast Air2Lean`; runs no compiler
# (`scripts/fixture-exports.py verify aggregate-casts` re-exports with the patched compilers). `--native` also runs
# `probe.zig` with a stock Zig (AIR2LEAN_ZIG_NATIVE, 0.14.1-0.16.0) and compares its output.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 -B scripts/lean-deps.py --build tests/roadmap/aggregate-casts
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
python3 -B scripts/fixture-exports.py check aggregate-casts
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
# The earlier hand-written AIR (no safety checks) still translates, all 12 functions.
"$translator" "$here/air-handwritten/0.16.0" --profile legacy-abi64-le -o "$work/Gen-handwritten.lean" \
  --namespace AggregateCasts --prefix aggregate_casts.
[ "$(ls "$here/air-handwritten/0.16.0" | wc -l)" -eq 12 ] &&
  [ "$(grep -c '^attribute \[zig_run\]' "$work/Gen-handwritten.lean")" -eq 12 ] ||
  { echo 'air-handwritten/0.16.0: not 12 translated functions' >&2; exit 1; }
# Its two casts of `[2]u24` are rejected, each alone: the legacy profile names no backend, and
# how a load reads a `u24`'s padding byte is the backend's (the exports above keep them, on the
# LLVM profile, with their theorems in Proofs.lean).
for f in u24x2ToU56 u56ToU24x2; do
  mkdir "$work/reject-$f"
  cp "$here/air-handwritten/reject-padded/aggregate_casts.$f.json" "$work/reject-$f/"
  if out=$("$translator" "$work/reject-$f" --profile legacy-abi64-le -o "$work/reject-$f.lean" \
      --namespace Reject --prefix aggregate_casts. 2>&1); then
    echo "the hand-written $f translated on a profile without a backend" >&2; exit 1
  fi
  [ ! -e "$work/reject-$f.lean" ] || { echo "the rejected $f wrote a translation" >&2; exit 1; }
  grep -qF "aggregate_casts.$f: near line 0: a Zig ≤0.16 representation \`@bitCast\` of an integer with padding bits" <<<"$out" &&
    grep -qF "is outside the subset for backend 'unverified'" <<<"$out" || { echo "$out" >&2; exit 1; }
done
echo 'hand-written AIR: 12 functions translate, the 2 padded casts are rejected'
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
