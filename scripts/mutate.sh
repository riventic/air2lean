#!/usr/bin/env bash
# Mutation testing for the differential test's panic-kind comparison (docs/generated-code.md
# §Panics). Each mutation below must make scripts/diff.sh FAIL (exit 1, mismatch>0); this script
# exits 0 only if every mutation was detected. Guards against a diff test that always passes.
#
# (a) Zig-source mutation: `scale`'s checked `a * b` becomes wrapping `a *% b` in a temp copy of
#     examples/basic/basic.zig, re-translated to Lean. The Zig side keeps checked semantics (it
#     always builds from the real examples/basic/basic.zig — untouched here), so `scale`'s
#     overflow inputs now disagree: Zig fails, Lean's regenerated `scale` does not. Exercises the
#     plain ok-vs-fail comparison, unchanged by this feature — a baseline sanity check.
# (b) Lean-runtime mutation: `Zig.add` (ZigLean/Basic.lean) throws `.panic` instead of
#     `.overflow` for the same failing inputs. Both sides still fail, but with different
#     `Zig.Error` kinds — this is what exercises the new kind comparison in diff.sh/Emit.lean/
#     harness.zig; the plain ok/fail check alone would have missed it. `ZigLean.Lemmas`'s
#     `add_unsigned` states `add`'s result in terms of `.overflow`, so it stops type-checking
#     under this mutation (a real, expected proof failure, not a bug); `ZigLean.lean` imports
#     `ZigLean.Lemmas` unconditionally, and `Proofs/Basic/Gen.lean` imports `ZigLean`, so this
#     mutation also drops that one theorem for the duration of the rebuild.
#
# Usage: mutate.sh
# Env:
#   AIR2LEAN_ZIG_AIR      Patched zig for translation (same as check.sh), needed for (a).
#   AIR2LEAN_ZIG_VERSION  Zig version: golden dir suffix. Default: 0.15.2 (same as check.sh).
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

zig_version=${AIR2LEAN_ZIG_VERSION:-0.15.2}
zig_air=${AIR2LEAN_ZIG_AIR:-zig-air-$zig_version/bin/zig}
[ -x "$zig_air" ] || {
  echo "error: patched zig not found/executable at $zig_air" >&2
  echo "hint: build one with zig-patch/build.sh $zig_version (see zig-patch/README.md)" >&2
  exit 1
}

gen_file="Proofs/Basic/Gen.lean"
basic_lean="ZigLean/Basic.lean"
lemmas_lean="ZigLean/Lemmas.lean"
gen_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-gen.XXXXXX")
basic_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-basic.XXXXXX")
lemmas_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-lemmas.XXXXXX")
cp "$gen_file" "$gen_backup"
cp "$basic_lean" "$basic_backup"
cp "$lemmas_lean" "$lemmas_backup"

mutate_tmp=""
cleanup() {
  # Capture the exit status that triggered this trap first — cleanup's own commands would
  # otherwise overwrite it, and bash uses whatever $? is left when the script exits.
  local ec=$?
  cp "$gen_backup" "$gen_file"
  cp "$basic_backup" "$basic_lean"
  cp "$lemmas_backup" "$lemmas_lean"
  rm -f "$gen_backup" "$basic_backup" "$lemmas_backup"
  [ -n "$mutate_tmp" ] && rm -rf "$mutate_tmp"
  exit "$ec"
}
trap cleanup EXIT

# Runs scripts/diff.sh, prints "$1: detected/NOT detected (mismatch=N)" and sets $detected
# (1/0). A diff.sh crash with no TOTAL line at all (not even a mismatch report) is a broken test
# setup, not an undetected mutation, so that case aborts the whole script instead.
run_and_report() {
  local label=$1
  local out
  out=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-diff.XXXXXX")
  local status=0
  bash scripts/diff.sh >"$out" 2>&1 || status=$?
  local total_line
  total_line=$(grep '^TOTAL:' "$out" || true)
  if [ -z "$total_line" ]; then
    echo "error: $label: diff.sh produced no TOTAL line (setup broke, not just undetected)" >&2
    cat "$out" >&2
    rm -f "$out"
    exit 1
  fi
  local mismatch
  mismatch=$(echo "$total_line" | sed -n 's/.*mismatch=\([0-9]*\).*/\1/p')
  rm -f "$out"
  if [ "$status" -ne 0 ] && [ "${mismatch:-0}" -gt 0 ]; then
    echo "$label: detected (exit=$status mismatch=$mismatch)"
    detected=1
  else
    echo "$label: NOT detected (exit=$status mismatch=$mismatch)"
    detected=0
  fi
}

all_detected=1

echo "== mutation (a): scale a*b -> a*%b (Zig source) ==" >&2
mutate_tmp=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-mutate-src.XXXXXX")
cp examples/basic/basic.zig "$mutate_tmp/basic.zig"
sed -i.bak 's/return a \* b;/return a *% b;/' "$mutate_tmp/basic.zig"
rm -f "$mutate_tmp/basic.zig.bak"
grep -q 'a \*% b' "$mutate_tmp/basic.zig" || {
  echo "error: mutation (a): sed did not change scale's body" >&2
  exit 1
}

air_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-mutate-air.XXXXXX")
ZIG_AIR_JSON_DIR="$air_dir" ZIG_AIR_JSON_FILTER=basic. "$zig_air" \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$mutate_tmp/basic.zig"
lake exe air2lean "$air_dir" -o "$gen_file" --namespace Basic --prefix basic.
rm -rf "$air_dir" "$mutate_tmp"
mutate_tmp=""

# No top-level `lake build` here: scripts/diff.sh's own `(cd tests/diff && lake build difftest)`
# already rebuilds Proofs.Basic.Gen as a dependency of Diff.lean.
run_and_report "mutation (a)"
[ "$detected" -eq 1 ] || all_detected=0

# Restore Gen.lean before mutation (b) so the two mutations don't compound.
cp "$gen_backup" "$gen_file"

echo "== mutation (b): Zig.add throws .panic instead of .overflow (Lean runtime) ==" >&2
sed -i.bak 's/a\.uaddOverflow b) then throw \.overflow/a.uaddOverflow b) then throw .panic/' "$basic_lean"
rm -f "$basic_lean.bak"
grep -q 'a.uaddOverflow b) then throw .panic' "$basic_lean" || {
  echo "error: mutation (b): sed did not change Zig.add" >&2
  exit 1
}

# `Proofs/Basic/Gen.lean` imports `ZigLean`, and `ZigLean.lean` imports `ZigLean.Lemmas`
# unconditionally, so building `difftest` always builds `ZigLean.Lemmas` too. Its `add_unsigned`
# states `add`'s result in terms of `.overflow`, which no longer holds once `add` throws `.panic`
# instead — a genuine, expected proof failure. Drop just that theorem for this mutation's window.
awk '/@\[simp\] theorem add_unsigned/,/simp \[add, BitVec\.uaddOverflow\]/{next} {print}' \
  "$lemmas_lean" >"$lemmas_lean.tmp" && mv "$lemmas_lean.tmp" "$lemmas_lean"
grep -q 'theorem add_unsigned' "$lemmas_lean" && {
  echo "error: mutation (b): failed to remove add_unsigned from $lemmas_lean" >&2
  exit 1
}

run_and_report "mutation (b)"
[ "$detected" -eq 1 ] || all_detected=0

[ "$all_detected" -eq 1 ]
