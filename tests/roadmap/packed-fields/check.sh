#!/usr/bin/env bash
# L08 packed fields and bit-pointers: retained translation, client proofs and CLI rejections.
# Needs a built translator and `lake build ZigLean ZigLean.PackedLemmas`; runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-packed-fields.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/PackedFields"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/packed-fields/test_cli.py --self-test
# The retained translation is the fresh one, byte for byte.
"$translator" tests/roadmap/packed-fields/air/0.16.0 -o "$work/PackedFields/Gen.lean" \
  --namespace PackedFields --prefix packed_fields.
cmp "$work/PackedFields/Gen.lean" tests/roadmap/packed-fields/PackedFields/Gen.lean
"${lean_cmd[@]}" -R "$work" -o "$work/PackedFields/Gen.olean" "$work/PackedFields/Gen.lean"
"${lean_cmd[@]}" -R tests/roadmap/packed-fields tests/roadmap/packed-fields/PackedFields/Proofs.lean
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/packed-fields/test_cli.py "$translator"
