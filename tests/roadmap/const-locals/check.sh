#!/usr/bin/env bash
# Comptime-resolved locals (Q01 fuzz seeds 18, 19, 39). Default: retained translations, Lean
# checks and CLI rejections; needs a built translator and `lake build ZigLean`, runs no compiler.
#   --native        zig test both sources with a stock Zig (AIR2LEAN_ZIG_NATIVE)
#   --export        re-export both sources with the patched Zig (AIR2LEAN_ZIG_AIR) and compare
#                   with the committed AIR
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/const-locals
sources=(const_locals:ConstLocals:air fuzz_s19:FuzzS19:air-fuzz_s19)
case "${1:-}" in
  --native)
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig 0.16.0}"
    for s in "${sources[@]}"; do
      "$AIR2LEAN_ZIG_NATIVE" test "$here/${s%%:*}.zig" -OReleaseSafe
    done
    exit 0 ;;
  --export)
    : "${AIR2LEAN_ZIG_AIR:?set the patched Zig 0.16.0}"
    work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-const-locals.XXXXXX")
    trap 'rm -rf "$work"' EXIT
    for s in "${sources[@]}"; do
      IFS=: read -r name _ air <<<"$s"
      mkdir "$work/$name"
      ZIG_AIR_JSON_DIR="$work/$name" ZIG_AIR_JSON_FILTER="$name." "$AIR2LEAN_ZIG_AIR" build-obj \
        -fno-emit-bin -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline "$here/$name.zig"
      diff -r "$work/$name" "$here/$air/0.16.0"
    done
    exit 0 ;;
  '') ;;
  *) echo 'usage: check.sh [--native|--export]' >&2; exit 2 ;;
esac
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-const-locals.XXXXXX")
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The retained translations are the fresh ones, byte for byte.
for s in "${sources[@]}"; do
  IFS=: read -r name ns air <<<"$s"
  mkdir "$work/$ns"
  "$translator" "$here/$air/0.16.0" -o "$work/$ns/Gen.lean" --namespace "$ns" --prefix "$name."
  cmp "$work/$ns/Gen.lean" "$here/$ns/Gen.lean"
  "${lean_cmd[@]}" -R "$work" -o "$work/$ns/Gen.olean" "$work/$ns/Gen.lean"
done
"${lean_cmd[@]}" -R "$here" "$here/ConstLocals/Proofs.lean"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
