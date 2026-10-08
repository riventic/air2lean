#!/usr/bin/env bash
# T02 pointer-width fixtures. `--export DIR` writes fresh AIR for every profile with a
# patched compiler; `--native` runs the source's layout/boundary tests on the host and
# type-checks them for wasm32. The default re-translates the retained AIR, compares it
# with the retained Gen.lean files byte for byte and checks the proofs and rejections.
# All tool invocations must run in the root's serialized build queue.
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
    exit ;;
  --native)
    [ "$#" -eq 1 ] || { echo 'usage: check.sh --native' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig 0.16.0}"
    "$AIR2LEAN_ZIG_NATIVE" test -OReleaseSafe "$src"
    # The comptime layout asserts are evaluated by the compiler for each target's ABI.
    "$AIR2LEAN_ZIG_NATIVE" build-obj -OReleaseSafe -target wasm32-freestanding -fno-emit-bin "$src"
    # The wasm32-wasi test binary runs under Node's WASI (32-bit usize boundaries).
    wasm_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-pointer-width-wasi.XXXXXX")
    trap 'rm -rf "$wasm_dir"' EXIT
    "$AIR2LEAN_ZIG_NATIVE" test -OReleaseSafe -target wasm32-wasi --test-no-exec \
      -femit-bin="$wasm_dir/test.wasm" "$src"
    node --no-warnings "$case_dir/run-wasi.mjs" "$wasm_dir/test.wasm"
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check|--native|--export OUTPUT_DIR]' >&2; exit 2 ;;
esac
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
python3 "$case_dir/test_cli.py" "$translator"
echo 'pointer-width translation, layout, proof and rejection gates passed'
