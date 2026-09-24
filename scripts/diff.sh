#!/usr/bin/env bash
# Differential test: build+run the Zig side (tests/diff/harness.zig) and the Lean side
# (tests/diff/Diff.lean), then compare their output line by line against the same inputs
# (tests/diff/inputs/*.jsonl, from tests/diff/gen_inputs.zig).
#
# A line counts as a match if both sides say "ok" with the same value, or both say "fail"
# (the specific Zig.Error kind is not compared). Anything else — a value mismatch, one side ok
# and the other fail, or a Lean "diverge" (none of these 8 functions should ever not terminate)
# — is a mismatch: printed immediately, and makes the whole run exit 1.
#
# Usage: diff.sh
# Env:
#   AIR2LEAN_ZIG   Stock zig to build+run the harness. Default: zig (on PATH).
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

zig_bin=${AIR2LEAN_ZIG:-zig}
functions=(scale clampAdd absDiff tardiness weightedTardiness sum totalWeightedTardiness classify)

echo "== building zig harness ==" >&2
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-diff.XXXXXX")
trap 'rm -rf "$build_dir"' EXIT
"$zig_bin" build-exe -OReleaseSafe -femit-bin="$build_dir/harness" \
  --dep basic -Mroot=tests/diff/harness.zig -Mbasic=examples/basic/basic.zig
mkdir -p tests/diff/out/zig tests/diff/out/lean
"$build_dir/harness"

echo "== building + running lean side ==" >&2
(cd tests/diff && lake build difftest)
tests/diff/.lake/build/bin/difftest

# Classifies one JSONL output line into $kind (ok|fail|diverge) and, for ok, $val (decimal
# string, quotes stripped). Both sides only ever emit these three shapes (harness.zig / Diff.lean).
classify_line() {
  local line=$1
  case "$line" in
    '{"ok":"'*'"}')
      kind=ok
      val=${line#'{"ok":"'}
      val=${val%'"}'}
      ;;
    '{"ok":'*'}')
      kind=ok
      val=${line#'{"ok":'}
      val=${val%'}'}
      ;;
    '{"fail"'*)
      kind=fail
      ;;
    '{"diverge":true}')
      kind=diverge
      ;;
    *)
      echo "error: unrecognized output line: $line" >&2
      exit 1
      ;;
  esac
}

echo "== comparing ==" >&2
total_ok=0
total_fail_match=0
total_mismatch=0
mismatch_found=0

for fn in "${functions[@]}"; do
  in_file="tests/diff/inputs/${fn}.jsonl"
  zig_file="tests/diff/out/zig/${fn}.jsonl"
  lean_file="tests/diff/out/lean/${fn}.jsonl"

  readarray -t in_lines <"$in_file"
  readarray -t zig_lines <"$zig_file"
  readarray -t lean_lines <"$lean_file"
  n=${#in_lines[@]}
  [ "${#zig_lines[@]}" -eq "$n" ] || { echo "error: $zig_file has ${#zig_lines[@]} lines, expected $n" >&2; exit 1; }
  [ "${#lean_lines[@]}" -eq "$n" ] || { echo "error: $lean_file has ${#lean_lines[@]} lines, expected $n" >&2; exit 1; }

  fn_ok=0
  fn_fail_match=0
  fn_mismatch=0
  for ((i = 0; i < n; i++)); do
    classify_line "${zig_lines[$i]}"
    zkind=$kind
    zval=${val:-}
    classify_line "${lean_lines[$i]}"
    lkind=$kind
    lval=${val:-}

    if [ "$zkind" = ok ] && [ "$lkind" = ok ] && [ "$zval" = "$lval" ]; then
      fn_ok=$((fn_ok + 1))
    elif [ "$zkind" = fail ] && [ "$lkind" = fail ]; then
      fn_fail_match=$((fn_fail_match + 1))
    else
      fn_mismatch=$((fn_mismatch + 1))
      mismatch_found=1
      echo "MISMATCH $fn input#$((i + 1)): ${in_lines[$i]}" >&2
      echo "  zig:  ${zig_lines[$i]}" >&2
      echo "  lean: ${lean_lines[$i]}" >&2
    fi
  done

  echo "$fn: ok=$fn_ok fail_match=$fn_fail_match mismatch=$fn_mismatch (of $n)"
  total_ok=$((total_ok + fn_ok))
  total_fail_match=$((total_fail_match + fn_fail_match))
  total_mismatch=$((total_mismatch + fn_mismatch))
done

echo "TOTAL: ok=$total_ok fail_match=$total_fail_match mismatch=$total_mismatch"
[ "$mismatch_found" -eq 0 ]
