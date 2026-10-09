#!/usr/bin/env bash
# Inline asm effect contract (A01): retained translation, effect proofs, CLI rejections and the
# test-only interpreter run of the generated wrappers with mutants. Needs a built translator and
# `lake build ZigLean Proofs.Asm.Effects`; runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-asm-effects.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AsmEffects"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The retained translation is the fresh one, byte for byte.
"$translator" tests/roadmap/asm-effects/air/0.16.0 -o "$work/AsmEffects/Gen.lean" \
  --namespace AsmEffects --prefix asm_effects.
cmp "$work/AsmEffects/Gen.lean" tests/roadmap/asm-effects/AsmEffects/Gen.lean
"${lean_cmd[@]}" -R "$work" -o "$work/AsmEffects/Gen.olean" "$work/AsmEffects/Gen.lean"
"${lean_cmd[@]}" -R tests/roadmap/asm-effects tests/roadmap/asm-effects/AsmEffects/Proofs.lean
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/asm-effects/test_cli.py "$translator"
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/asm-effects/harness.py
