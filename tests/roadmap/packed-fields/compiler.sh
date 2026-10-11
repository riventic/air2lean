#!/usr/bin/env bash
# L08 compiler export and native run of packed_fields.zig. Run under scripts/build-guard.py.
#   compiler.sh --export OUTPUT_DIR   fresh patched-compiler export: OUTPUT_DIR/llvm (LLVM
#                                     bit-pointer host widths) and OUTPUT_DIR/x86_64 (the
#                                     self-hosted backend, `hostAbi` only: ABI host widths)
#   compiler.sh --native              stock host Zig runs the source's tests
#   compiler.sh --check               retained export -> translation -> proofs (no compiler)
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/packed-fields
case "${1:---check}" in
  --native)
    [ "$#" -eq 1 ] || { echo 'usage: compiler.sh --native' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig}"
    "$AIR2LEAN_ZIG_NATIVE" test "$here/packed_fields.zig" -OReleaseSafe
    exit ;;
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: compiler.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a patched AIR-only compiler}"
    mkdir -p "$2"
    [ -z "$(find "$2" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo 'AIR output must be empty' >&2; exit 1; }
    out=$(cd -- "$2" && pwd)
    mkdir "$out/llvm" "$out/x86_64"
    ZIG_AIR_JSON_DIR="$out/llvm" ZIG_AIR_JSON_FILTER=packed_fields. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline "$here/packed_fields.zig"
    ZIG_AIR_JSON_DIR="$out/x86_64" ZIG_AIR_JSON_FILTER=packed_fields.hostAbi \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -fno-llvm -fno-lld -target x86_64-linux -mcpu=baseline "$here/packed_fields.zig"
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: compiler.sh [--check]' >&2; exit 2; } ;;
  *) echo 'usage: compiler.sh [--check|--native|--export OUTPUT_DIR]' >&2; exit 2 ;;
esac
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-packed-compiler.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/PackedFieldsFresh" "$work/PackedFieldsX86"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/compiler-check.py"
"$translator" "$here/air-fresh/0.16.0/llvm" -o "$work/PackedFieldsFresh/Gen.lean" \
  --namespace PackedFieldsFresh --prefix packed_fields.
cmp "$work/PackedFieldsFresh/Gen.lean" "$here/PackedFieldsFresh/Gen.lean"
"$translator" "$here/air-fresh/0.16.0/x86_64" -o "$work/PackedFieldsX86/Gen.lean" \
  --namespace PackedFieldsX86 --prefix packed_fields. --allow-unqualified-build-mode
cmp "$work/PackedFieldsX86/Gen.lean" "$here/PackedFieldsX86/Gen.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/PackedFieldsFresh/Gen.olean" "$work/PackedFieldsFresh/Gen.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/PackedFieldsX86/Gen.olean" "$work/PackedFieldsX86/Gen.lean"
"${lean_cmd[@]}" -R "$here" "$here/PackedFieldsFresh/Proofs.lean"
echo 'packed-field compiler export: inventory, profile, translation and proofs passed'
