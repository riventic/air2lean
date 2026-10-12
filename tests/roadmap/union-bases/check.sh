#!/usr/bin/env bash
# Union-member constant pointer bases (L06): retained translation, generated-client proofs,
# per-version exports and CLI rejections. Needs a built translator and
# `lake build ZigLean ZigLean.Mem.ConstPtr Air2Lean`; runs no compiler. `--native` additionally runs the
# source's test with a stock Zig on x86_64 Linux (AIR2LEAN_ZIG_NATIVE), on stage2_x86_64 and LLVM.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/union-bases
if [ "${1:-}" = --native ]; then
  : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig}"
  for backend in -fno-llvm -fllvm; do
    "$AIR2LEAN_ZIG_NATIVE" test "$here/union_bases.zig" -OReleaseSafe "$backend" \
      -target x86_64-linux-musl -mcpu=baseline
  done
  exit 0
fi
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-union-bases.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/UnionBases"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The retained translation is the fresh 0.16.0 one, byte for byte.
"$translator" "$here/air/0.16.0" -o "$work/UnionBases/Gen.lean" \
  --namespace UnionBases --prefix union_bases. --allow-unqualified-build-mode
cmp "$work/UnionBases/Gen.lean" "$here/UnionBases/Gen.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/UnionBases/Gen.olean" "$work/UnionBases/Gen.lean"
"${lean_cmd[@]}" -R "$here" "$here/UnionBases/Proofs.lean"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
