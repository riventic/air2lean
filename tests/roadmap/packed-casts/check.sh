#!/usr/bin/env bash
# L07/L08 packed representations and logical casts (README.md). Sources and their versions:
#   packed_casts.zig   0.14.1 0.15.2 0.16.0 0.17.1   (PackedCasts/<version>/PackedCasts.lean, Model.lean)
#   logical017.zig     0.17.1                        (PackedCasts/<version>/Logical017.lean, ModelLogical.lean)
#   vector_fields.zig  0.14.1 0.15.2                 (PackedCasts/<version>/VectorFields.lean, ModelVector.lean)
#   auto_items.zig     0.14.1 0.15.2                 (PackedCasts/<version>/AutoItems.lean, ModelAuto.lean)
#   opt_items.zig      0.14.1 0.15.2                 (PackedCasts/<version>/OptItems.lean, ModelOpt.lean;
#                                                    air/<version>/opt_items_x64, the self-hosted
#                                                    x86_64 backend: OptItemsX64.lean, ModelOptX64.lean)
#   sentinel_arrays.zig 0.14.1 0.15.2 0.16.0         (PackedCasts/<version>/SentinelArrays.lean, ModelSentinel.lean)
#   void_casts.zig     0.14.1 0.15.2 0.16.0 0.17.1   (PackedCasts/<version>/VoidCasts.lean, ModelVoid.lean)
#   void017.zig        0.17.1                        (PackedCasts/<version>/Void017.lean, ModelVoid017.lean)
#   air-handwritten/<version>/void_cast  0.16.0 0.17.1  (PackedCasts/<version>/VoidCast.lean,
#                                                    ModelVoidCast.lean: the `bitcast` of a zero-bit
#                                                    type, which Sema folds and no compiler emits)
#   reject_lanes.zig   0.14.1 0.15.2                 (rejected: docs/upstream/packed-vector-lane-ptr.md)
#   reject_sentinel.zig 0.17.1                       (rejected: docs/upstream/bitcast-sentinel-array.md)
#   reject_items.zig   0.14.1 0.15.2                 (rejected: arrays of tuples, errors, optionals)
#   reject_ptrfield.zig 0.14.1 0.15.2                (rejected: a pointer field in a packed struct)
# (<version> as a name: V0_17_1). Each model is written for the newest version of its source; the
# other versions' models are that one with the version renamed (scripts/fixtures.py instance).
# reject/expected.txt lists every rejected function with its diagnostic; expected/wrong.txt lists
# results of wrong models, which the comparison with the model and with the native output must
# reject.
#
#   check.sh [--check]            translate every retained export, compare with the retained
#                                 translation, check the model instances, build the library
#                                 PackedCasts (tests/roadmap/lakefile.toml: the translations and
#                                 the kernel proofs of the models), audit the models' axioms,
#                                 compare the lines the models' `main`s print with
#                                 expected/<version>.txt, and check the rejections
#   check.sh --native VERSION     build native.zig with a stock Zig VERSION (AIR2LEAN_ZIG_NATIVE)
#                                 for x86_64-linux-musl (ReleaseSafe and Debug), run it (Docker
#                                 linux/amd64 unless AIR2LEAN_X86_64_RUN is set; empty: the host),
#                                 and compare with expected/<version>.txt
#   check.sh --compile-errors VERSION   the casts in compile-errors/ fail to compile with a stock
#                                 Zig VERSION (AIR2LEAN_ZIG_NATIVE) as compile-errors/expected.txt says
#
# The exports are declared in exports.json and pinned by exports.lock.json
# (scripts/fixture-exports.py check|verify|export packed-casts; the default run checks the lock).
# A model line `unspecified` matches any native value (a NaN's bits, padding bytes). Needs a built
# translator; Lake builds the library with what it imports (scripts/fixtures.py; run it under
# scripts/build-guard.py).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/packed-casts
versions=(0.14.1 0.15.2 0.16.0 0.17.1)
# source:translation:model:versions (the newest first: its model is the written one)
sources=(
  "packed_casts:PackedCasts:Model:0.17.1 0.16.0 0.15.2 0.14.1"
  "logical017:Logical017:ModelLogical:0.17.1"
  "vector_fields:VectorFields:ModelVector:0.15.2 0.14.1"
  "auto_items:AutoItems:ModelAuto:0.15.2 0.14.1"
  "opt_items:OptItems:ModelOpt:0.15.2 0.14.1"
  "sentinel_arrays:SentinelArrays:ModelSentinel:0.16.0 0.15.2 0.14.1"
  "void_casts:VoidCasts:ModelVoid:0.17.1 0.16.0 0.15.2 0.14.1"
  "void017:Void017:ModelVoid017:0.17.1"
)
has_version() { [[ " $1 " == *" $2 "* ]]; }

# `model` against `native`: equal lines, except that `unspecified` matches any value.
compare() {
  python3 - "$1" "$2" <<'PY'
import sys
model, native = (open(p).read().splitlines() for p in sys.argv[1:3])
ok = len(model) == len(native)
for m, n in zip(model, native):
    mn, _, mv = m.partition(": ")
    nn, _, nv = n.partition(": ")
    if mn != nn or (mv != "unspecified" and mv != nv):
        print(f"model {m!r} != native {n!r}", file=sys.stderr); ok = False
if not ok:
    sys.exit(f"{sys.argv[1]} does not match {sys.argv[2]}")
PY
}

# Negative control (`wrong_models_rejected MODEL NATIVE`, MODEL a scratch file): every wrong
# result of expected/wrong.txt (`name: value`, `#` comments) that has a line in MODEL, put in
# place of that line, must make `compare` fail against NATIVE.
wrong_models_rejected() {
  local wrong name count=0
  while IFS= read -r wrong; do
    wrong=${wrong%%#*}
    wrong=${wrong%"${wrong##*[![:space:]]}"}
    name=${wrong%%: *}
    [ -n "$wrong" ] && grep -q "^$name: " "$1" || continue
    awk -v n="$name: " -v w="$wrong" 'index($0, n) == 1 { print w; next } { print }' "$1" > "$1.wrong"
    if compare "$1.wrong" "$2" 2>/dev/null; then
      echo "the wrong model '$wrong' matches $2" >&2; return 1
    fi
    count=$((count + 1))
  done < "$dir/expected/wrong.txt"
  [ "$count" -gt 0 ] || { echo "no wrong model of expected/wrong.txt applies to $2" >&2; return 1; }
  echo "$count wrong models rejected by the comparison with $(basename "$2")"
}

case "${1:---check}" in
  --native)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --native VERSION' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig of that version}"
    work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-packed-casts.XXXXXX")
    trap 'rm -rf "$work"' EXIT
    for mode in ReleaseSafe Debug; do
      "$AIR2LEAN_ZIG_NATIVE" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} "-O$mode" -target x86_64-linux-musl \
        -femit-bin="$work/native-$mode" "$dir/native.zig"
      if [ -n "${AIR2LEAN_X86_64_RUN+set}" ]; then
        # shellcheck disable=SC2086
        ${AIR2LEAN_X86_64_RUN} "$work/native-$mode" 2> "$work/native-$mode.txt"
      else
        docker run --rm --platform linux/amd64 -v "$work:/w:ro" alpine:3 \
          sh -c "/w/native-$mode 2>&1" > "$work/native-$mode.txt"
      fi
      compare "$dir/expected/$2.txt" "$work/native-$mode.txt"
      echo "native x86_64-linux-musl $mode ($2) matches the model ($(wc -l < "$work/native-$mode.txt" | tr -d ' ') lines)"
      cp "$dir/expected/$2.txt" "$work/model.txt"
      wrong_models_rejected "$work/model.txt" "$work/native-$mode.txt"
    done
    exit ;;
  --compile-errors)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --compile-errors VERSION' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig of that version}"
    grep "^$2 " "$dir/compile-errors/expected.txt" | while read -r _ file outcome; do
      if msg=$("$AIR2LEAN_ZIG_NATIVE" build-obj -fno-emit-bin "$dir/compile-errors/$file" 2>&1); then
        [ "$outcome" = compiles ] || { echo "$2 $file compiles, expected a compile error" >&2; exit 1; }
      else
        [ "$outcome" = error ] || { echo "$2 $file: unexpected compile error: $msg" >&2; exit 1; }
        grep -q 'cannot @bitCast' <<<"$msg" || { echo "$2 $file: $msg" >&2; exit 1; }
      fi
      echo "$2 $file: $outcome"
    done
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check|--native VERSION|--compile-errors VERSION]' >&2; exit 2 ;;
esac
python3 -B scripts/fixture-exports.py check packed-casts
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-packed-casts.XXXXXX")
trap 'rm -rf "$work"' EXIT
models=() mains=() theorems=()
for entry in "${sources[@]}"; do
  IFS=: read -r src ns model vs <<<"$entry"
  read -r newest _ <<<"$vs"
  newest="V${newest//./_}"
  for v in $vs; do
    t="V${v//./_}"
    # The retained translation is the fresh one, byte for byte (Lake builds the retained file).
    "$translator" "$dir/air/$v/$src" -o "$work/$t-$ns.lean" --namespace "PackedCasts.$t.$ns" --prefix "$src."
    cmp "$work/$t-$ns.lean" "$dir/PackedCasts/$t/$ns.lean"
    # Every version's model states the same theorems: the newest version's, the version renamed.
    [ "$t" = "$newest" ] ||
      python3 -B scripts/fixtures.py instance "$dir/PackedCasts/$newest/$model.lean" --subst "$newest=$t"
    models+=("PackedCasts.$t.$model")
    mains+=("PackedCasts.$t.$model:PackedCasts.$t.$model.main")
  done
done
# The hand-written `bitcast` of zero-bit types: one translation and one written model per version.
for v in 0.16.0 0.17.1; do
  t="V${v//./_}"
  "$translator" "$dir/air-handwritten/$v/void_cast" -o "$work/$t-VoidCast.lean" \
    --namespace "PackedCasts.$t.VoidCast" --prefix void_cast.
  cmp "$work/$t-VoidCast.lean" "$dir/PackedCasts/$t/VoidCast.lean"
  models+=("PackedCasts.$t.ModelVoidCast")
  theorems+=(--declaration "PackedCasts.$t.ModelVoidCast.voidsToInt_ok")
done
# `opt_items.zig` for the self-hosted x86_64 backend (an opt-in build mode): the profile's
# storage encoding of a padded payload. The 0.15.2 model is written, the 0.14.1 one renamed.
for v in 0.15.2 0.14.1; do
  t="V${v//./_}"
  "$translator" "$dir/air/$v/opt_items_x64" -o "$work/$t-OptItemsX64.lean" \
    --namespace "PackedCasts.$t.OptItemsX64" --prefix opt_items. --allow-unqualified-build-mode
  cmp "$work/$t-OptItemsX64.lean" "$dir/PackedCasts/$t/OptItemsX64.lean"
  [ "$t" = V0_15_2 ] ||
    python3 -B scripts/fixtures.py instance "$dir/PackedCasts/V0_15_2/ModelOptX64.lean" --subst "V0_15_2=$t"
  models+=("PackedCasts.$t.ModelOptX64")
  theorems+=(--declaration "PackedCasts.$t.ModelOptX64.intToU24s_padding")
done
for t in V0_14_1 V0_15_2 V0_16_0 V0_17_1; do
  theorems+=(--declaration "PackedCasts.$t.Model.setUnion_ok" --declaration "PackedCasts.$t.Model.floatField_nan")
done
for t in V0_14_1 V0_15_2; do
  theorems+=(--declaration "PackedCasts.$t.ModelVector.laneSum_ok" --declaration "PackedCasts.$t.ModelAuto.unionsToInt_padding"
    --declaration "PackedCasts.$t.ModelOpt.intToU24s_padding" --declaration "PackedCasts.$t.ModelOpt.intToU8s_badFlag")
done
theorems+=(--declaration PackedCasts.V0_17_1.ModelLogical.intToModes_unnamed)
for t in V0_14_1 V0_15_2 V0_16_0; do
  theorems+=(--declaration "PackedCasts.$t.ModelSentinel.sentToInt_ok" --declaration "PackedCasts.$t.ModelSentinel.intToSentAt_last")
done
python3 -B scripts/fixtures.py build PackedCasts
# Compiled and audited (axioms, sorry, kernel replay), not only run: they are indexed (F2).
python3 -B scripts/fixtures.py audit "${models[@]}" "${theorems[@]}"
python3 -B scripts/fixtures.py run "$work/out" "${mains[@]}"
for v in "${versions[@]}"; do
  : > "$work/$v.txt"
  for entry in "${sources[@]}"; do
    IFS=: read -r _ _ model vs <<<"$entry"
    has_version "$vs" "$v" || continue
    cat "$work/out/PackedCasts.V${v//./_}.$model.main.txt" >> "$work/$v.txt"
  done
  # The models' lines are the retained native observations of this version.
  compare "$work/$v.txt" "$dir/expected/$v.txt"
  echo "$v: translations, kernel proofs and $(wc -l < "$work/$v.txt" | tr -d ' ') model lines match"
  # A wrong model's result is not the observation.
  wrong_models_rejected "$work/$v.txt" "$dir/expected/$v.txt"
done
# Every function of the rejected sources, translated alone, fails with its diagnostic
# (reject/expected.txt: version, source, function, then the text the diagnostic must contain).
rejected=0
while read -r v src fn text; do
  case $v in ''|'#'*) continue ;; esac
  mkdir "$work/reject-air"
  cp "$dir/air/$v/$src/$src.$fn.json" "$work/reject-air/"
  if out=$("$translator" "$work/reject-air" -o "$work/reject.lean" --namespace Reject --prefix "$src." 2>&1); then
    echo "$src.$fn ($v) translated, expected a rejection" >&2; exit 1
  fi
  grep -qF -- "$text" <<<"$out" || { echo "$src.$fn ($v): expected '$text' in: $out" >&2; exit 1; }
  [ ! -e "$work/reject.lean" ] || { echo "$src.$fn ($v): a rejected cast wrote a translation" >&2; exit 1; }
  rm -r "$work/reject-air"
  rejected=$((rejected + 1))
done < "$dir/reject/expected.txt"
# Every exported function of those sources has a line there.
for v in "${versions[@]}"; do
  for src in reject_sentinel reject_items reject_ptrfield; do
    [ -d "$dir/air/$v/$src" ] || continue
    for f in "$dir/air/$v/$src"/*.json; do
      fn=$(basename "$f" .json)
      grep -q "^$v $src ${fn#"$src".} " "$dir/reject/expected.txt" ||
        { echo "reject/expected.txt has no line for $v $fn" >&2; exit 1; }
    done
  done
done
# `void` itself has no bit representation before Zig 0.17 (hand-written: Sema rejects the source).
if out=$("$translator" "$dir/air-handwritten/0.16.0/reject_void" -o "$work/reject.lean" --namespace Reject --prefix void_cast. 2>&1); then
  echo 'a Zig 0.16.0 `bitcast` of `void` translated' >&2; exit 1
fi
grep -qF 'a `@bitCast` to or from `void` is outside the subset' <<<"$out" || { echo "$out" >&2; exit 1; }
# A padded payload (`[2]?u24`) on a profile that names no backend (opt_items.intToU24s without
# its profile): which bytes a load reads is the backend's.
if out=$("$translator" "$dir/air-handwritten/0.15.2/reject_padded" -o "$work/reject.lean" --namespace Reject --prefix opt_items. 2>&1); then
  echo 'a representation cast of a padded integer translated on a legacy profile' >&2; exit 1
fi
grep -qF 'representation `@bitCast` of an integer with padding bits' <<<"$out" || { echo "$out" >&2; exit 1; }
echo "$((rejected + 2)) rejected casts fail with their diagnostics"
# Lane pointers into a vector field of a packed struct are rejected (0.14.1, 0.15.2).
for v in 0.14.1 0.15.2; do
  if out=$("$translator" "$dir/air/$v/reject_lanes" -o "$work/reject.lean" --namespace Reject 2>&1); then
    echo "reject_lanes ($v) translated" >&2; exit 1
  fi
  grep -q 'lane pointer into a vector field of a packed struct' <<<"$out" || { echo "$out" >&2; exit 1; }
done
echo 'packed-casts translation, proof, model and rejection gates passed'
