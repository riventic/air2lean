#!/usr/bin/env bash
# Inline asm effect contract (A01): retained translation, effect proofs, CLI rejections and the
# test-only interpreter run of the generated wrappers with mutants. Needs a built translator and
# `lake build ZigLean Proofs.Asm.Effects`; runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 -B scripts/lean-deps.py --build tests/roadmap/asm-effects
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-asm-effects.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AsmEffects"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The retained translation is the fresh one, byte for byte.
"$translator" tests/roadmap/asm-effects/air/0.16.0 --profile legacy-abi64-le -o "$work/AsmEffects/Gen.lean" \
  --namespace AsmEffects --prefix asm_effects.
cmp "$work/AsmEffects/Gen.lean" tests/roadmap/asm-effects/AsmEffects/Gen.lean
"${lean_cmd[@]}" -R "$work" -o "$work/AsmEffects/Gen.olean" "$work/AsmEffects/Gen.lean"
"${lean_cmd[@]}" -R tests/roadmap/asm-effects tests/roadmap/asm-effects/AsmEffects/Proofs.lean
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/asm-effects/test_cli.py "$translator"
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/asm-effects/harness.py
# A01 environment reads, memory inputs and memory-region contracts on fresh 0.17.0/0.16.0/0.15.2
# exports of asm_env.zig (provenance-env.json): retained translation, proofs, CLI rejections.
python3 - <<'PY'
import hashlib, json, pathlib
here = pathlib.Path('tests/roadmap/asm-effects')
record = json.loads((here / 'provenance-env.json').read_text())
for name, digest in record['source_sha256'].items():
    assert hashlib.sha256((here / name).read_bytes()).hexdigest() == digest, name
files = {str(p.relative_to(here)): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in sorted((here / 'air-env').rglob('*.json'))}
assert files == record['air_sha256'], 'AIR fixtures differ from provenance-env.json'
PY
mkdir -p "$work/AsmEnv"
"$translator" tests/roadmap/asm-effects/air-env/0.17.0 --profile abi64-le-v1 -o "$work/AsmEnv/Gen.lean" \
  --namespace AsmEnv --prefix asm_env.
cmp "$work/AsmEnv/Gen.lean" tests/roadmap/asm-effects/AsmEnv/Gen.lean
"${lean_cmd[@]}" -R "$work" -o "$work/AsmEnv/Gen.olean" "$work/AsmEnv/Gen.lean"
"${lean_cmd[@]}" -R tests/roadmap/asm-effects tests/roadmap/asm-effects/AsmEnv/Proofs.lean
python3 -B tests/roadmap/callbacks/mutants.py generate asm-env "$work/mutants" | while IFS=: read -r name module proofs; do
  mroot="$work/mutants/$name"
  "${lean_cmd[@]}" -R "$mroot" -o "$mroot/${module%.lean}.olean" "$mroot/$module"
  cp "tests/roadmap/asm-effects/$proofs" "$mroot/$proofs"
  status=0
  LEAN_PATH="$mroot:$LEAN_PATH" "${lean_cmd[@]}" -R "$mroot" "$mroot/$proofs" > "$mroot/log" 2>&1 || status=$?
  python3 -B tests/roadmap/callbacks/mutants.py classify "$name" "$status" "$mroot/log" "$mroot/$proofs"
done
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/asm-effects/test_env_cli.py "$translator"
