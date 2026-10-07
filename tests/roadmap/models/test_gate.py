#!/usr/bin/env python3
"""Verify orchestration and failure propagation using fake tools only."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

source = Path(__file__).resolve().parents[3] / "scripts/model-contracts.sh"
with tempfile.TemporaryDirectory(prefix="air2lean-model-gate-mock-") as tmp:
    root = Path(tmp)
    repo = root / "repo"
    (repo / "scripts").mkdir(parents=True)
    shutil.copyfile(source, repo / "scripts/model-contracts.sh")
    tools = root / "fake-tools"
    tools.mkdir()
    programs = {
        "lake": r'''#!/usr/bin/env bash
set -euo pipefail
if [ "$1" = build ]; then
  echo "mock build: $*"
  [ "${MOCK_FAILURE:-}" != build ] || exit 7
elif [ "$1" = env ]; then
  shift
  exec "$@"
else
  exit 90
fi
''',
        "lean": r'''#!/usr/bin/env bash
set -euo pipefail
if [ "$1" = -o ]; then
  echo "mock model"
  [ "${MOCK_FAILURE:-}" != model ] || exit 8
  printf model > "$2"
elif [ "$1" = --run ] && [ "$2" = tests/roadmap/models/StdModels.lean ]; then
  echo "mock std-models"
  [ "${MOCK_FAILURE:-}" != std-models ] || exit 12
elif [ "$1" = tests/roadmap/models/StdDependencies.lean ]; then
  echo "mock std-dependencies"
  [ "${MOCK_FAILURE:-}" != std-dependencies ] || exit 13
elif [ "$1" = --run ]; then
  echo "mock registry"
  [ "${MOCK_FAILURE:-}" != registry ] || exit 9
  evidence=${@: -1}
  printf registry > "$evidence/registry.json"
  printf generated > "$evidence/Generated.lean"
  printf generated > "$evidence/TupleGenerated.lean"
  printf generated > "$evidence/CollisionGenerated.lean"
  printf generated > "$evidence/FillGenerated.lean"
  printf generated > "$evidence/FillAssumedGenerated.lean"
else
  echo "mock client"
  [ "${MOCK_FAILURE:-}" != client ] || exit 10
fi
''',
        "python3": r'''#!/usr/bin/env bash
set -euo pipefail
case "$*" in *external-contracts.py*) printf '{"mock": "contracts"}\n'; exit 0;; esac
printf 'mock cli\n'
[ "${MOCK_FAILURE:-}" != cli ] || exit 11
''',
    }
    for name, text in programs.items():
        executable = tools / name
        executable.write_text(text)
        executable.chmod(0o755)
    for stage in ["", "build", "model", "registry", "std-models", "std-dependencies", "client", "cli"]:
        evidence = root / (stage or "success")
        env = dict(os.environ, PATH=f"{tools}{os.pathsep}{os.environ['PATH']}",
                   AIR2LEAN_MODEL_EVIDENCE=str(evidence), MOCK_FAILURE=stage)
        result = subprocess.run(["bash", str(repo / "scripts/model-contracts.sh")],
                                env=env, text=True, capture_output=True)
        assert (result.returncode == 0) == (stage == ""), (stage, result.stdout, result.stderr)
        assert (evidence / "build.log").is_file()
        if stage:
            assert (evidence / f"{stage}.log").is_file()
            assert f"mock {stage}" in (evidence / f"{stage}.log").read_text()
        else:
            for artifact in ["tests/roadmap/models/Model.olean", "registry.json", "Generated.lean",
                             "model.log", "registry.log", "std-models.log", "std-dependencies.log", "client.log", "tuple-client.log", "collision-client.log", "cli.log",
                             "tests/roadmap/models/Fill.olean", "fill-model.log", "fill-client.log",
                             "fill-contracts.json", "fill-assumed-contracts.json"]:
                assert (evidence / artifact).is_file(), artifact
            assert "ZigLean ZigLean.External Air2Lean.StdModels Air2Lean.ModelRegistry Air2Lean.Check Air2Lean.Emit air2lean" in (evidence / "build.log").read_text()
        assert not (repo / "tests").exists(), "gate wrote generated evidence into checkout"
print("model contract gate mocks passed (no compiler executed)")
