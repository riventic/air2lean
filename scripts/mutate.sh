#!/usr/bin/env bash
# Mutation testing for the differential test's panic-kind comparison (docs/generated-code.md
# §Panics). Each mutation below must make scripts/diff.sh FAIL (exit 1, mismatch>0); this script
# exits 0 only if every mutation was detected. Guards against a diff test that always passes.
# Each mutation runs diff.sh over its own example only, so a mismatch elsewhere cannot count as
# a detection.
#
# (a) Zig-source mutation: `scale`'s checked `a * b` becomes wrapping `a *% b` in a temp copy of
#     examples/basic/basic.zig, re-translated to Lean. The Zig side keeps checked semantics (it
#     always builds from the real examples/basic/basic.zig — untouched here), so `scale`'s
#     overflow inputs now disagree: Zig fails, Lean's regenerated `scale` does not. Exercises the
#     plain ok-vs-fail comparison — a baseline sanity check.
# (b) Lean-runtime mutation: `Zig.add` (ZigLean/Basic.lean) throws `.panic` instead of
#     `.overflow` for the same failing inputs. Both sides still fail, but with different
#     `Zig.Error` kinds — this exercises the kind comparison in diff.sh/Emit.lean/harness.zig;
#     the plain ok/fail check alone would miss it. `ZigLean.Lemmas`'s `add_unsigned` states
#     `add`'s result in terms of `.overflow`, so it stops type-checking under this mutation (a
#     real, expected proof failure, not a bug); `ZigLean.lean` imports `ZigLean.Lemmas`
#     unconditionally, and `Proofs/Basic/Gen.lean` imports `ZigLean`, so this mutation also drops
#     that one theorem for the duration of the rebuild.
# (c) Zig-source mutation, options: `findOr`'s `orelse xs.len` becomes `orelse 0` in a temp copy
#     of examples/options/options.zig, re-translated to Lean — same shape as (a), but for the
#     optional-result protocol (a not-found search now returns 0 instead of xs.len).
# (d) Lean-runtime mutation: `roundQuot` (ZigLean/Float/Round.lean) rounds ties away from zero
#     instead of to even. `Float.roundRat`'s domain is nonnegative, so "away from zero" is
#     "always round up": the tie branch `else if m % 2 = 0 then (m : Int) else (m : Int) + 1`
#     becomes `else (m : Int) + 1`. Every float op that rounds (`+ - * /`, `@sqrt`,
#     `@floatFromInt`, …) goes through it, so `scripts/diff.sh` must catch it via mismatches,
#     not a build failure: the one lemma that unfolds `roundQuot` (`roundQuot_le`) is written to
#     hold for both forms.
# (e) Emitter-output mutation, variants: the generated `Light.ofInt?` (Proofs/Variants/Gen.lean) also
#     accepts the unnamed value 3. `lightOf(3)` then returns `.red`, where Zig panics
#     (`invalidEnumValue`): the conversion an enum's generated defs do must match Zig's.
# (f) Lean-runtime mutation, pointers: `Zig.store` (ZigLean/Mem/Basic.lean) writes one byte too
#     few (the last byte of the value stays as it was). `swap`, `delay` and `copyJob` then leave
#     other bytes in the buffers than Zig: the diff test compares the buffers after each call.
# (g) Lean-runtime mutation, slices: `Zig.memmove` (ZigLean/Mem/Basic.lean) writes one byte too
#     few (the last byte of the destination stays as it was). `copy` and `copyWithin` then leave
#     other bytes in the buffers than Zig.
# (h) Lean-runtime mutation, lists: `Zig.rawAlloc` (ZigLean/Mem/Alloc.lean) never fails at
#     `Mem.failAt`. Every lists function then returns a value where Zig returns
#     `error.OutOfMemory`.
# (i) Diff-test-archive mutation, asm: `tests/diff/asm/asm.zig`'s `air2lean_asm_bswap32` returns
#     `x` unchanged instead of `@byteSwap(x)`. This archive (docs/generated-code.md §Inline asm)
#     is the diff test's own stand-in for `Asm.airAsm_*`'s opaque behaviour (M21: no defining
#     equation exists to mutate on the Lean side, unlike (b)/(d)/(f)/(g)/(h) above) -- mutating
#     it and comparing against `examples/asm/asm.zig`'s real inline asm checks that the
#     comparison is live, not vacuous. x86_64 only, same as `asm` itself.
# (j) Lean-runtime mutation, vectors: `Vec.reduce` (ZigLean/Vec.lean) folds only lanes
#     `1..n-1`, dropping the last lane. `maxLane`'s `@reduce(.Max)` then ignores the vector's
#     last lane, so an input whose max is in that lane disagrees with Zig.
#
# Usage: mutate.sh
# Env:
#   AIR2LEAN_ZIG_AIR      Patched zig for translation (same as check.sh), needed for (a)/(c).
#   AIR2LEAN_ZIG_VERSION  Zig version: selects the default patched zig. Default: 0.16.0 (same as check.sh).
#   AIR2LEAN_EXAMPLES     Space-separated example dirs. A mutation runs only if its example
#                         (basic for (a)/(b), options for (c), floatops for (d), variants for (e),
#                         pointers (f), slices (g), lists (h), asm for (i), vectors (j))
#                         is in the list.
#                         Default: every dir in examples/.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

zig_version=${AIR2LEAN_ZIG_VERSION:-0.16.0}
zig_air=${AIR2LEAN_ZIG_AIR:-zig-air-$zig_version/bin/zig}
[ -x "$zig_air" ] || {
  echo "error: patched zig not found/executable at $zig_air" >&2
  echo "hint: build one with zig-patch/build.sh $zig_version (see zig-patch/README.md)" >&2
  exit 1
}

examples=${AIR2LEAN_EXAMPLES:-$(cd examples && for d in */; do printf '%s ' "${d%/}"; done)}
has_example() {
  local needle=$1 e
  for e in $examples; do
    [ "$e" = "$needle" ] && return 0
  done
  return 1
}

gen_file="Proofs/Basic/Gen.lean"
options_gen="Proofs/Options/Gen.lean"
variants_gen="Proofs/Variants/Gen.lean"
basic_lean="ZigLean/Basic.lean"
lemmas_lean="ZigLean/Lemmas.lean"
round_lean="ZigLean/Float/Round.lean"
mem_lean="ZigLean/Mem/Basic.lean"
alloc_lean="ZigLean/Mem/Alloc.lean"
asm_zig="tests/diff/asm/asm.zig"
vec_lean="ZigLean/Vec.lean"
gen_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-gen.XXXXXX")
options_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-options-gen.XXXXXX")
variants_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-variants-gen.XXXXXX")
basic_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-basic.XXXXXX")
lemmas_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-lemmas.XXXXXX")
round_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-round.XXXXXX")
mem_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-mem.XXXXXX")
alloc_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-alloc.XXXXXX")
asm_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-asm.XXXXXX")
vec_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-vec.XXXXXX")
cp "$gen_file" "$gen_backup"
cp "$options_gen" "$options_backup"
cp "$variants_gen" "$variants_backup"
cp "$basic_lean" "$basic_backup"
cp "$lemmas_lean" "$lemmas_backup"
cp "$round_lean" "$round_backup"
cp "$mem_lean" "$mem_backup"
cp "$alloc_lean" "$alloc_backup"
cp "$asm_zig" "$asm_backup"
cp "$vec_lean" "$vec_backup"

mutate_tmp=""
air_dir=""
cleanup() {
  # Capture the exit status that triggered this trap first — cleanup's own commands would
  # otherwise overwrite it, and bash uses whatever $? is left when the script exits.
  local ec=$?
  cp "$gen_backup" "$gen_file"
  cp "$options_backup" "$options_gen"
  cp "$variants_backup" "$variants_gen"
  cp "$basic_backup" "$basic_lean"
  cp "$lemmas_backup" "$lemmas_lean"
  cp "$round_backup" "$round_lean"
  cp "$mem_backup" "$mem_lean"
  cp "$alloc_backup" "$alloc_lean"
  cp "$asm_backup" "$asm_zig"
  cp "$vec_backup" "$vec_lean"
  rm -f "$gen_backup" "$options_backup" "$variants_backup" "$basic_backup" "$lemmas_backup" "$round_backup" \
    "$mem_backup" "$alloc_backup" "$asm_backup" "$vec_backup"
  [ -n "$mutate_tmp" ] && rm -rf "$mutate_tmp"
  [ -n "$air_dir" ] && rm -rf "$air_dir"
  exit "$ec"
}
trap cleanup EXIT

# translate_mutated <ex> <sed-expr> <grep-pattern>: apply <sed-expr> to a temp copy of
# examples/<ex>/<ex>.zig, check with <grep-pattern> that it changed, and translate the copy to
# Proofs/<Ex>/Gen.lean (the same steps as check.sh). The Zig harness keeps the real source.
translate_mutated() {
  local ex=$1 expr=$2 pattern=$3
  local Ex
  Ex="$(printf '%s' "${ex:0:1}" | tr '[:lower:]' '[:upper:]')${ex:1}"
  mutate_tmp=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-mutate-src.XXXXXX")
  cp "examples/$ex/$ex.zig" "$mutate_tmp/$ex.zig"
  sed -i.bak "$expr" "$mutate_tmp/$ex.zig"
  grep -q "$pattern" "$mutate_tmp/$ex.zig" || {
    echo "error: sed '$expr' did not change examples/$ex/$ex.zig" >&2
    exit 1
  }
  air_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-mutate-air.XXXXXX")
  ZIG_AIR_JSON_DIR="$air_dir" ZIG_AIR_JSON_FILTER="$ex." "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$mutate_tmp/$ex.zig"
  lake exe air2lean "$air_dir" -o "Proofs/$Ex/Gen.lean" --namespace "$Ex" --prefix "$ex."
  rm -rf "$air_dir" "$mutate_tmp"
  air_dir=""
  mutate_tmp=""
}

# run_and_report <label> <ex>: runs scripts/diff.sh over <ex>, prints "<label>: detected/NOT
# detected (mismatch=N)" and sets $detected (1/0). A diff.sh crash with no TOTAL line at all (not
# even a mismatch report) is a broken test setup, not an undetected mutation, so that case
# aborts the whole script instead.
run_and_report() {
  local label=$1 ex=$2
  local out
  out=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-diff.XXXXXX")
  local status=0
  AIR2LEAN_EXAMPLES=$ex bash scripts/diff.sh >"$out" 2>&1 || status=$?
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
if ! has_example basic; then
  echo "mutation (a): skipped (AIR2LEAN_EXAMPLES excludes basic)"
else
  translate_mutated basic 's/return a \* b;/return a *% b;/' 'a \*% b'
  # No top-level `lake build` here: scripts/diff.sh's own `(cd tests/diff && lake build
  # difftest)` already rebuilds Proofs.Basic.Gen as a dependency of Diff.lean.
  run_and_report "mutation (a)" basic
  [ "$detected" -eq 1 ] || all_detected=0
  # Restore Gen.lean before mutation (b) so the two mutations don't compound.
  cp "$gen_backup" "$gen_file"
fi

echo "== mutation (b): Zig.add throws .panic instead of .overflow (Lean runtime) ==" >&2
if ! has_example basic; then
  echo "mutation (b): skipped (AIR2LEAN_EXAMPLES excludes basic)"
else
  sed -i.bak 's/a\.uaddOverflow b) then throw \.overflow/a.uaddOverflow b) then throw .panic/' "$basic_lean"
  rm -f "$basic_lean.bak"
  grep -q 'a.uaddOverflow b) then throw .panic' "$basic_lean" || {
    echo "error: mutation (b): sed did not change Zig.add" >&2
    exit 1
  }

  # `Proofs/Basic/Gen.lean` imports `ZigLean`, and `ZigLean.lean` imports `ZigLean.Lemmas`
  # unconditionally, so building `difftest` always builds `ZigLean.Lemmas` too. Its
  # `add_unsigned` states `add`'s result in terms of `.overflow`, which no longer holds once
  # `add` throws `.panic` instead — a genuine, expected proof failure. Drop just that theorem
  # for this mutation's window.
  awk '/@\[simp\] theorem add_unsigned/,/simp \[add, BitVec\.uaddOverflow\]/{next} {print}' \
    "$lemmas_lean" >"$lemmas_lean.tmp" && mv "$lemmas_lean.tmp" "$lemmas_lean"
  grep -q 'theorem add_unsigned' "$lemmas_lean" && {
    echo "error: mutation (b): failed to remove add_unsigned from $lemmas_lean" >&2
    exit 1
  }

  run_and_report "mutation (b)" basic
  [ "$detected" -eq 1 ] || all_detected=0
  # Restore ZigLean before mutation (c) so the mutations don't compound.
  cp "$basic_backup" "$basic_lean"
  cp "$lemmas_backup" "$lemmas_lean"
fi

echo "== mutation (c): findOr orelse xs.len -> orelse 0 (Zig source) ==" >&2
if ! has_example options; then
  echo "mutation (c): skipped (AIR2LEAN_EXAMPLES excludes options)"
else
  translate_mutated options 's/orelse xs\.len/orelse 0/' 'orelse 0'
  run_and_report "mutation (c)" options
  [ "$detected" -eq 1 ] || all_detected=0
fi

echo "== mutation (d): roundQuot ties away from zero (Lean runtime) ==" >&2
if ! has_example floatops; then
  echo "mutation (d): skipped (AIR2LEAN_EXAMPLES excludes floatops)"
else
  sed -i.bak 's/else if m % 2 = 0 then (m : Int) else (m : Int) + 1/else (m : Int) + 1/' "$round_lean"
  rm -f "$round_lean.bak"
  ! grep -q 'if m % 2 = 0 then' "$round_lean" || {
    echo "error: mutation (d): sed did not change roundQuot" >&2
    exit 1
  }

  run_and_report "mutation (d)" floatops
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$round_backup" "$round_lean"
fi

echo "== mutation (e): Light.ofInt? accepts the unnamed value 3 (emitter output) ==" >&2
if ! has_example variants; then
  echo "mutation (e): skipped (AIR2LEAN_EXAMPLES excludes variants)"
else
  sed -i.bak 's/else if v = 2 then some .green else none/else if v = 2 then some .green else if v = 3 then some .red else none/' "$variants_gen"
  rm -f "$variants_gen.bak"
  grep -q 'if v = 3 then some .red' "$variants_gen" || {
    echo "error: mutation (e): sed did not change Light.ofInt?" >&2
    exit 1
  }

  run_and_report "mutation (e)" variants
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$variants_backup" "$variants_gen"
fi

echo "== mutation (f): Zig.store writes one byte too few (Lean runtime) ==" >&2
if ! has_example pointers; then
  echo "mutation (f): skipped (AIR2LEAN_EXAMPLES excludes pointers)"
else
  sed -i.bak 's/storeBytes p align (Enc.encode v)$/storeBytes p align (Enc.encode v).pop/' "$mem_lean"
  rm -f "$mem_lean.bak"
  grep -q 'storeBytes p align (Enc.encode v).pop' "$mem_lean" || {
    echo "error: mutation (f): sed did not change Zig.store" >&2
    exit 1
  }

  run_and_report "mutation (f)" pointers
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$mem_backup" "$mem_lean"
fi

echo "== mutation (g): Zig.memmove writes one byte too few (Lean runtime) ==" >&2
if ! has_example slices; then
  echo "mutation (g): skipped (AIR2LEAN_EXAMPLES excludes slices)"
else
  sed -i.bak 's/^  storeBytes dst dstAlign bs$/  storeBytes dst dstAlign bs.pop/' "$mem_lean"
  rm -f "$mem_lean.bak"
  grep -q 'storeBytes dst dstAlign bs.pop' "$mem_lean" || {
    echo "error: mutation (g): sed did not change Zig.memmove" >&2
    exit 1
  }

  run_and_report "mutation (g)" slices
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$mem_backup" "$mem_lean"
fi

echo "== mutation (h): Zig.rawAlloc never fails at Mem.failAt (Lean runtime) ==" >&2
if ! has_example lists; then
  echo "mutation (h): skipped (AIR2LEAN_EXAMPLES excludes lists)"
else
  sed -i.bak 's/  if m.failAt = some m.allocs ∨ maxAllocBytes < n then return none/  if maxAllocBytes < n then return none/' "$alloc_lean"
  rm -f "$alloc_lean.bak"
  grep -q '  if maxAllocBytes < n then return none' "$alloc_lean" || {
    echo "error: mutation (h): sed did not change Zig.rawAlloc" >&2
    exit 1
  }

  run_and_report "mutation (h)" lists
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$alloc_backup" "$alloc_lean"
fi

echo "== mutation (i): air2lean_asm_bswap32 returns x unchanged (diff-test archive) ==" >&2
if ! has_example asm; then
  echo "mutation (i): skipped (AIR2LEAN_EXAMPLES excludes asm)"
else
  sed -i.bak 's/return @byteSwap(x);/return x;/' "$asm_zig"
  rm -f "$asm_zig.bak"
  grep -q 'return x;' "$asm_zig" || {
    echo "error: mutation (i): sed did not change air2lean_asm_bswap32" >&2
    exit 1
  }

  run_and_report "mutation (i)" asm
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$asm_backup" "$asm_zig"
fi

echo "== mutation (j): Vec.reduce drops the last lane (Lean runtime) ==" >&2
if ! has_example vectors; then
  echo "mutation (j): skipped (AIR2LEAN_EXAMPLES excludes vectors)"
else
  sed -i.bak 's/(v\.lanes\.toArray\.extract 1 n)\.foldl f v\.lanes\.toArray\[0\]!/(v.lanes.toArray.extract 1 (n - 1)).foldl f v.lanes.toArray[0]!/' "$vec_lean"
  rm -f "$vec_lean.bak"
  grep -q 'extract 1 (n - 1)).foldl f' "$vec_lean" || {
    echo "error: mutation (j): sed did not change Vec.reduce" >&2
    exit 1
  }

  run_and_report "mutation (j)" vectors
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$vec_backup" "$vec_lean"
fi

[ "$all_detected" -eq 1 ]
