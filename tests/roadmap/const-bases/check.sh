#!/usr/bin/env bash
# Nested constant pointer bases (L06): retained translation, generated-client proofs and CLI
# rejections. Needs a built translator and `lake build ZigLean ZigLean.Mem.ConstPtr`; runs no
# compiler. `--native` additionally runs the source fixture with a stock stage2_x86_64 Zig on
# x86_64 Linux (AIR2LEAN_ZIG_NATIVE).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/const-bases
if [ "${1:-}" = --native ]; then
  : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig}"
  "$AIR2LEAN_ZIG_NATIVE" test "$here/const_bases.zig" -OReleaseSafe -fno-llvm -fno-lld \
    -target x86_64-linux-musl -mcpu=baseline
  exit 0
fi
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-const-bases.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/ConstBases"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The retained translation is the fresh one, byte for byte.
"$translator" "$here/air/0.16.0" -o "$work/ConstBases/Gen.lean" \
  --namespace ConstBases --prefix const_bases.
cmp "$work/ConstBases/Gen.lean" "$here/ConstBases/Gen.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/ConstBases/Gen.olean" "$work/ConstBases/Gen.lean"
"${lean_cmd[@]}" -R "$here" "$here/ConstBases/Proofs.lean"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
