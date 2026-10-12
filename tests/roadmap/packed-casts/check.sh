#!/usr/bin/env bash
# L07/L08 packed representations and logical casts (README.md). Sources and their versions:
#   packed_casts.zig   0.14.1 0.15.2 0.16.0 0.17.0   (namespace PackedCasts,  Model.lean)
#   logical017.zig     0.17.0                        (namespace Logical017,   ModelLogical.lean)
#   vector_fields.zig  0.14.1 0.15.2                 (namespace VectorFields, ModelVector.lean)
#   auto_items.zig     0.14.1 0.15.2                 (namespace AutoItems,    ModelAuto.lean)
#   reject_lanes.zig   0.14.1 0.15.2                 (rejected: docs/upstream/packed-vector-lane-ptr.md)
#
#   check.sh [--check]            translate every retained export, compare with gen/<version>/,
#                                 build the translations, check the kernel proofs of the Model*.lean
#                                 files, compare their lines with expected/<version>.txt, and check
#                                 the rejections
#   check.sh --native VERSION     build native.zig with a stock Zig VERSION (AIR2LEAN_ZIG_NATIVE)
#                                 for x86_64-linux-musl (ReleaseSafe and Debug), run it (Docker
#                                 linux/amd64 unless AIR2LEAN_X86_64_RUN is set; empty: the host),
#                                 and compare with expected/<version>.txt
#   check.sh --compile-errors VERSION   the casts in compile-errors/ fail to compile with a stock
#                                 Zig VERSION (AIR2LEAN_ZIG_NATIVE) as compile-errors/expected.txt says
#   check.sh --export VERSION DIR write fresh AIR with a patched Zig VERSION (AIR2LEAN_ZIG_AIR)
#
# A model line `unspecified` matches any native value (a NaN's bits, padding bytes). Needs
# `lake build ZigLean Air2Lean air2lean`; run in the serialized build queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/packed-casts
versions=(0.14.1 0.15.2 0.16.0 0.17.0)
# source:namespace:model:versions
sources=(
  "packed_casts:PackedCasts:Model:0.14.1 0.15.2 0.16.0 0.17.0"
  "logical017:Logical017:ModelLogical:0.17.0"
  "vector_fields:VectorFields:ModelVector:0.14.1 0.15.2"
  "auto_items:AutoItems:ModelAuto:0.14.1 0.15.2"
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
      "$AIR2LEAN_ZIG_NATIVE" build-exe "-O$mode" -target x86_64-linux-musl \
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
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-packed-casts.XXXXXX")
trap 'rm -rf "$work"' EXIT
for v in "${versions[@]}"; do
  w="$work/$v"
  mkdir -p "$w"
  cp "$dir/Show.lean" "$w/"
  "${lean_cmd[@]}" -R "$w" -o "$w/Show.olean" "$w/Show.lean"
  : > "$w/lines.txt"
  for entry in "${sources[@]}"; do
    IFS=: read -r src ns model vs <<<"$entry"
    has_version "$vs" "$v" || continue
    mkdir -p "$w/$ns"
    "$translator" "$dir/air/$v/$src" -o "$w/$ns/Gen.lean" --namespace "$ns" --prefix "$src."
    cmp "$w/$ns/Gen.lean" "$dir/gen/$v/$ns.lean"
    LEAN_PATH="$w:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}" \
      "${lean_cmd[@]}" -R "$w" -o "$w/$ns/Gen.olean" "$w/$ns/Gen.lean"
    cp "$dir/$model.lean" "$w/"
    LEAN_PATH="$w:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}" \
      "${lean_cmd[@]}" -R "$w" --run "$w/$model.lean" > "$w/$model.txt" \
      || { cat "$w/$model.txt" >&2; exit 1; }
    cat "$w/$model.txt" >> "$w/lines.txt"
    # Compiled and audited (axioms, sorry, kernel replay), not only run: it is indexed (F2).
    python3 -B scripts/theorem_universe.py gate "$w/$model.lean" --root "$w" --lean-path "$w" \
      --output-dir "$w/universe-$model" > /dev/null
  done
  # The model's lines are the retained native observations of this version.
  compare "$w/lines.txt" "$dir/expected/$v.txt"
  echo "$v: translations, kernel proofs and $(wc -l < "$w/lines.txt" | tr -d ' ') model lines match"
done
# Lane pointers into a vector field of a packed struct are rejected (0.14.1, 0.15.2).
for v in 0.14.1 0.15.2; do
  if out=$("$translator" "$dir/air/$v/reject_lanes" -o "$work/reject.lean" --namespace Reject 2>&1); then
    echo "reject_lanes ($v) translated" >&2; exit 1
  fi
  grep -q 'lane pointer into a vector field of a packed struct' <<<"$out" || { echo "$out" >&2; exit 1; }
done
echo 'packed-casts translation, proof, model and rejection gates passed'
