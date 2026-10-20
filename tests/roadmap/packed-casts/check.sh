#!/usr/bin/env bash
# L07/L08 packed representations and logical casts (README.md). Sources and their versions:
#   packed_casts.zig   0.14.1 0.15.2 0.16.0 0.17.0   (PackedCasts/<version>/PackedCasts.lean, Model.lean)
#   logical017.zig     0.17.0                        (PackedCasts/<version>/Logical017.lean, ModelLogical.lean)
#   vector_fields.zig  0.14.1 0.15.2                 (PackedCasts/<version>/VectorFields.lean, ModelVector.lean)
#   auto_items.zig     0.14.1 0.15.2                 (PackedCasts/<version>/AutoItems.lean, ModelAuto.lean)
#   reject_lanes.zig   0.14.1 0.15.2                 (rejected: docs/upstream/packed-vector-lane-ptr.md)
# (<version> as a name: V0_17_0). Each model is written for the newest version of its source; the
# other versions' models are that one with the version renamed (scripts/fixtures.py instance).
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
#   check.sh --export VERSION DIR write fresh AIR with a patched Zig VERSION (AIR2LEAN_ZIG_AIR)
#
# A model line `unspecified` matches any native value (a NaN's bits, padding bytes). Needs a built
# translator; Lake builds the library with what it imports (scripts/fixtures.py; run it under
# scripts/build-guard.py).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/packed-casts
versions=(0.14.1 0.15.2 0.16.0 0.17.0)
# source:translation:model:versions (the newest first: its model is the written one)
sources=(
  "packed_casts:PackedCasts:Model:0.17.0 0.16.0 0.15.2 0.14.1"
  "logical017:Logical017:ModelLogical:0.17.0"
  "vector_fields:VectorFields:ModelVector:0.15.2 0.14.1"
  "auto_items:AutoItems:ModelAuto:0.15.2 0.14.1"
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

case "${1:---check}" in
  --export)
    [ "$#" -eq 3 ] || { echo 'usage: check.sh --export VERSION DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a patched Zig with the repository exporter}"
    for entry in "${sources[@]}" "reject_lanes:::0.14.1 0.15.2"; do
      IFS=: read -r src _ _ vs <<<"$entry"
      has_version "$vs" "$2" || continue
      out="$3/$src"
      mkdir -p "$out"
      [ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo "$out must be empty" >&2; exit 1; }
      ZIG_AIR_JSON_DIR="$(cd -- "$out" && pwd)" ZIG_AIR_JSON_FILTER="$src." \
        "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
        -target x86_64-linux -mcpu=baseline "$dir/$src.zig"
    done
    exit ;;
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
  *) echo 'usage: check.sh [--check|--native VERSION|--compile-errors VERSION|--export VERSION DIR]' >&2; exit 2 ;;
esac
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
for t in V0_14_1 V0_15_2 V0_16_0 V0_17_0; do
  theorems+=(--declaration "PackedCasts.$t.Model.setUnion_ok" --declaration "PackedCasts.$t.Model.floatField_nan")
done
for t in V0_14_1 V0_15_2; do
  theorems+=(--declaration "PackedCasts.$t.ModelVector.laneSum_ok" --declaration "PackedCasts.$t.ModelAuto.unionsToInt_padding")
done
theorems+=(--declaration PackedCasts.V0_17_0.ModelLogical.intToModes_unnamed)
python3 -B scripts/fixtures.py build PackedCasts
# Compiled and audited (axioms, sorry, kernel replay), not only run: they are indexed (F2).
python3 -B scripts/fixtures.py audit "${models[@]}" "${theorems[@]}"
python3 -B scripts/fixtures.py run "$work/out" "${mains[@]}"
for v in "${versions[@]}"; do
  : > "$work/$v.txt"
  for entry in "${sources[@]}"; do
    IFS=: read -r _ _ model vs <<<"$entry"
    has_version "$vs" "$v" || continue
    cat "$work/out/PackedCasts.V${v//./_}.$model.txt" >> "$work/$v.txt"
  done
  # The models' lines are the retained native observations of this version.
  compare "$work/$v.txt" "$dir/expected/$v.txt"
  echo "$v: translations, kernel proofs and $(wc -l < "$work/$v.txt" | tr -d ' ') model lines match"
done
# Lane pointers into a vector field of a packed struct are rejected (0.14.1, 0.15.2).
for v in 0.14.1 0.15.2; do
  if out=$("$translator" "$dir/air/$v/reject_lanes" -o "$work/reject.lean" --namespace Reject 2>&1); then
    echo "reject_lanes ($v) translated" >&2; exit 1
  fi
  grep -q 'lane pointer into a vector field of a packed struct' <<<"$out" || { echo "$out" >&2; exit 1; }
done
echo 'packed-casts translation, proof, model and rejection gates passed'
