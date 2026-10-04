#!/usr/bin/env bash
# Complete typed external-model gate. Retain all evidence in the caller-selected directory.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"
model_evidence=${AIR2LEAN_MODEL_EVIDENCE:-${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-model-contracts}
mkdir -p "$model_evidence/tests/roadmap/models"
model_evidence=$(cd "$model_evidence" && pwd)
export AIR2LEAN_MODEL_EVIDENCE="$model_evidence"

# Generated source imports the ZigLean umbrella, so its .olean is a required prerequisite.
lake build ZigLean ZigLean.External Air2Lean.ModelRegistry Air2Lean.Check Air2Lean.Emit air2lean   2>&1 | tee "$model_evidence/build.log"
lake env bash -euo pipefail -c '
  export LEAN_PATH="$AIR2LEAN_MODEL_EVIDENCE:${LEAN_PATH:-}"
  lean -o "$AIR2LEAN_MODEL_EVIDENCE/tests/roadmap/models/Model.olean"     tests/roadmap/models/Model.lean 2>&1 | tee "$AIR2LEAN_MODEL_EVIDENCE/model.log"
  test -s "$AIR2LEAN_MODEL_EVIDENCE/tests/roadmap/models/Model.olean"
  lean --run tests/roadmap/models/Registry.lean "$AIR2LEAN_MODEL_EVIDENCE"     2>&1 | tee "$AIR2LEAN_MODEL_EVIDENCE/registry.log"
  test -s "$AIR2LEAN_MODEL_EVIDENCE/registry.json"
  test -s "$AIR2LEAN_MODEL_EVIDENCE/Generated.lean"
  test -s "$AIR2LEAN_MODEL_EVIDENCE/TupleGenerated.lean"
  test -s "$AIR2LEAN_MODEL_EVIDENCE/CollisionGenerated.lean"
  lean "$AIR2LEAN_MODEL_EVIDENCE/Generated.lean"     2>&1 | tee "$AIR2LEAN_MODEL_EVIDENCE/client.log"
  lean "$AIR2LEAN_MODEL_EVIDENCE/TupleGenerated.lean" 2>&1 | tee "$AIR2LEAN_MODEL_EVIDENCE/tuple-client.log"
  lean "$AIR2LEAN_MODEL_EVIDENCE/CollisionGenerated.lean" 2>&1 | tee "$AIR2LEAN_MODEL_EVIDENCE/collision-client.log"
'
python3 tests/roadmap/models/test_cli.py .lake/build/bin/air2lean   2>&1 | tee "$model_evidence/cli.log"
printf 'External model contract evidence: %s\n' "$model_evidence"
