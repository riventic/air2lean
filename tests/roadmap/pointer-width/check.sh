#!/usr/bin/env bash
# T02 pointer-width fixtures. `--export DIR` writes fresh AIR of pointer_width.zig and
# reject.zig (Zig 0.16.0) for every profile with a patched compiler; names.zig and c_ints.zig
# (0.17.1, 0.16.0) and the 0.17.1 exports of pointer_width.zig and reject.zig are declared in
# exports.json and pinned by exports.lock.json (scripts/fixture-exports.py verify|export pointer-width).
# `--native` runs the sources' layout/boundary/name tests on the host and under wasm32-wasi
# (Node WASI). The default re-translates the retained AIR, compares
# it with the retained Gen.lean files byte for byte and checks the proofs and rejections.
# Needs `lake build ZigLean Air2Lean air2lean ZigLean.Mem.WidthLemmas`. All tool invocations
# must run in the root's serialized build queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case_dir=tests/roadmap/pointer-width
src=$case_dir/pointer_width.zig
targets=(wasm32-freestanding wasm32-wasi x86_64-linux)
case "${1:---check}" in
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a patched Zig 0.16.0 with the repository exporter}"
    for t in "${targets[@]}"; do
      out="$2/$t"
      mkdir -p "$out"
      [ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo "$out must be empty" >&2; exit 1; }
      cpu=()
      [ "$t" = x86_64-linux ] && cpu=(-mcpu=baseline)
      ZIG_AIR_JSON_DIR="$(cd -- "$out" && pwd)" ZIG_AIR_JSON_FILTER=pointer_width. \
        "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
        -target "$t" "${cpu[@]}" "$src"
    done
    out="$2/wasm32-reject"
    mkdir -p "$out"
    [ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo "$out must be empty" >&2; exit 1; }
    ZIG_AIR_JSON_DIR="$(cd -- "$out" && pwd)" ZIG_AIR_JSON_FILTER=reject. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target wasm32-freestanding "$case_dir/reject.zig"
    exit ;;
  --native)
    [ "$#" -eq 1 ] || { echo 'usage: check.sh --native' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig (0.16.0 or 0.17.1)}"
    wasm_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-pointer-width-wasi.XXXXXX")
    trap 'rm -rf "$wasm_dir"' EXIT
    for s in "$src" "$case_dir/names.zig" "$case_dir/c_ints.zig"; do
      "$AIR2LEAN_ZIG_NATIVE" test -OReleaseSafe "$s"
      # Compiled for wasm32-freestanding: pointer_width.zig's comptime layout asserts are
      # evaluated for that target's ABI.
      "$AIR2LEAN_ZIG_NATIVE" build-obj -OReleaseSafe -target wasm32-freestanding -fno-emit-bin "$s"
      # The wasm32-wasi test binary runs under Node's WASI (32-bit usize boundaries).
      "$AIR2LEAN_ZIG_NATIVE" test -OReleaseSafe -target wasm32-wasi --test-no-exec \
        -femit-bin="$wasm_dir/test.wasm" "$s"
      node --no-warnings "$case_dir/run-wasi.mjs" "$wasm_dir/test.wasm"
    done
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check|--native|--export OUTPUT_DIR]' >&2; exit 2 ;;
esac
python3 -B scripts/lean-deps.py --build "$case_dir"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-pointer-width.XXXXXX")
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
for pair in Wasm32:wasm32-freestanding Wasi:wasm32-wasi X64:x86_64-linux; do
  ns=${pair%%:*}
  t=${pair#*:}
  mkdir -p "$work/PointerWidth/$ns"
  "$translator" "$case_dir/air/0.16.0/$t" -o "$work/PointerWidth/$ns/Gen.lean" \
    --namespace "PointerWidth.$ns" --prefix pointer_width.
  cmp "$work/PointerWidth/$ns/Gen.lean" "$case_dir/PointerWidth/$ns/Gen.lean"
  "${lean_cmd[@]}" -R "$work" -o "$work/PointerWidth/$ns/Gen.olean" "$work/PointerWidth/$ns/Gen.lean"
done
"${lean_cmd[@]}" -R "$case_dir" "$case_dir/PointerWidth/Proofs.lean"
# pointer_width.zig exported by Zig 0.17.1 (exports.json): the same proofs, instantiated from the
# 0.16.0 file (which the T05 wasm-correspondence claims name) one namespace deeper.
python3 -B scripts/fixture-exports.py check pointer-width
for pair in Wasm32:wasm32-freestanding Wasi:wasm32-wasi X64:x86_64-linux; do
  ns=${pair%%:*}
  t=${pair#*:}
  gen="PointerWidth/V0_17_1/$ns/Gen.lean"
  mkdir -p "$(dirname "$work/$gen")"
  "$translator" "$case_dir/air/0.17.1/pointer_width/$t" -o "$work/$gen" \
    --namespace "PointerWidth.V0_17_1.$ns" --prefix pointer_width.
  cmp "$work/$gen" "$case_dir/$gen"
  "${lean_cmd[@]}" -R "$work" -o "$work/${gen%.lean}.olean" "$work/$gen"
done
python3 -B scripts/fixtures.py instance "$case_dir/PointerWidth/Proofs.lean" \
  --subst PointerWidth=PointerWidth.V0_17_1
"${lean_cmd[@]}" -R "$case_dir" "$case_dir/PointerWidth/V0_17_1/Proofs.lean"
# names.zig (`@tagName`, `@errorName`) and c_ints.zig (the C integer types, `isize`, extern
# struct layouts) per Zig version of exports.json and target. The proofs are stated once (0.17.1)
# and instantiated for 0.16.0 (scripts/fixtures.py instance).
for source in names:Names c_ints:CInts; do
  stem=${source%%:*}
  dir=${source#*:}
  for v in 0.17.1 0.16.0; do
    V="V${v//./_}"
    for pair in Wasm32:wasm32-freestanding Wasi:wasm32-wasi X64:x86_64-linux; do
      ns=${pair%%:*}
      t=${pair#*:}
      gen="PointerWidth/$dir/$V/$ns/Gen.lean"
      mkdir -p "$(dirname "$work/$gen")"
      "$translator" "$case_dir/air/$v/$stem/$t" -o "$work/$gen" \
        --namespace "PointerWidth.$dir.$V.$ns" --prefix "$stem."
      cmp "$work/$gen" "$case_dir/$gen"
      "${lean_cmd[@]}" -R "$work" -o "$work/${gen%.lean}.olean" "$work/$gen"
    done
    [ "$V" = V0_17_1 ] || python3 -B scripts/fixtures.py instance \
      "$case_dir/PointerWidth/$dir/V0_17_1/Proofs.lean" --subst "V0_17_1=$V"
    "${lean_cmd[@]}" -R "$case_dir" "$case_dir/PointerWidth/$dir/$V/Proofs.lean"
  done
done
# Layout, overflow and bounds mutants of the retained translations (mutations.py): each builds,
# and its proofs (PointerWidth.Proofs or PointerWidth.CInts.V0_17_1.Proofs) fail in the theorems
# of the changed fact.
python3 -B "$case_dir/mutations.py" --self-test
python3 -B "$case_dir/mutations.py" run "$work"
python3 "$case_dir/test_cli.py" "$translator"
echo 'pointer-width translation, layout, proof and rejection gates passed'
