#!/usr/bin/env bash
# T06: the differential test on inputs that are not the committed ones (docs/build-modes.md
# §Fresh inputs). In a check tree (scripts/check-tree.py create --host-goldens VERSION, never the
# checkout), tests/diff/input_seed.zig gets SEED and tests/diff/gen_inputs.zig regenerates every
# input file it writes; scripts/diff.sh then runs, in AIR2LEAN_DIFF_FRESH_INPUTS mode, the
# examples whose inputs changed (an example with only fixed inputs is not re-tested here). The
# committed per-input exclusion pins name the committed inputs, so they are not checked: a model
# `.illegal`/`.unspecified` result is an exclusion, never a match; any value, error or panic
# disagreement is a mismatch and fails the run.
#
# usage: scripts/fresh-inputs.sh SEED SUMMARY
#   SEED     a u64 (decimal or 0x-hex); CI derives it from the commit
#   SUMMARY  the differential summary (scripts/diff-report.py), with fresh_input_seed = SEED
# Env: AIR2LEAN_ZIG (stock zig, default zig), AIR2LEAN_ZIG_VERSION (default: that zig's version),
#   AIR2LEAN_FRESH_TREE (the check tree, default .lake/fresh-inputs-tree), and every scripts/diff.sh
#   variable (AIR2LEAN_DIFF_OPTIMIZE, AIR2LEAN_DIFF_BACKEND, ...).
set -euo pipefail
[ "$#" = 2 ] || { sed -n 11,17p "$0" >&2; exit 2; }
seed=$1 summary=$2
# The whole word (a case glob's `*` would accept any suffix, which lands in a Zig source file).
if ! [[ $seed =~ ^(0x[0-9a-fA-F]{1,16}|[0-9]{1,20})$ ]]; then
  echo "error: SEED must be a decimal or 0x-hex u64" >&2; exit 2
fi
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
zig=${AIR2LEAN_ZIG:-zig}
version=${AIR2LEAN_ZIG_VERSION:-$("$zig" version)}
tree=${AIR2LEAN_FRESH_TREE:-.lake/fresh-inputs-tree}
case "$summary" in /*) ;; *) summary=$repo/$summary ;; esac
python3 -B scripts/check-tree.py create "$tree" --host-goldens "$version" >/dev/null
cd "$tree"
before=$(mktemp "${TMPDIR:-/tmp}/air2lean-fresh.XXXXXX")
trap 'rm -f "$before"' EXIT
for d in tests/diff/*/inputs; do
  printf '%s %s\n' "$(cat "$d"/*.jsonl | shasum -a 256 | cut -d' ' -f1)" "$d"
done >"$before"
printf '//! scripts/fresh-inputs.sh\npub const seed: u64 = %s;\n' "$seed" >tests/diff/input_seed.zig
"$zig" run tests/diff/gen_inputs.zig >/dev/null
# The examples this host runs by default (scripts/example-selection.sh) whose inputs changed.
source scripts/example-selection.sh
eligible=" $(air2lean_default_examples "$PWD" "$version" "$(uname -m)") "
examples=''
while read -r digest dir; do
  now=$(cat "$dir"/*.jsonl | shasum -a 256 | cut -d' ' -f1)
  ex=${dir#tests/diff/}; ex=${ex%/inputs}
  case "$eligible" in *" $ex "*) ;; *) continue ;; esac
  if [ "$now" != "$digest" ]; then examples="$examples$ex "; fi
done <"$before"
[ -n "$examples" ] || { echo "error: seed $seed changed no input file" >&2; exit 1; }
echo "fresh inputs (seed $seed): $examples" >&2
AIR2LEAN_DIFF_FRESH_INPUTS=$seed AIR2LEAN_DIFF_REPORT=$summary AIR2LEAN_EXAMPLES=$examples \
  AIR2LEAN_ZIG=$zig bash scripts/diff.sh
