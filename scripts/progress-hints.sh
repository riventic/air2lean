#!/usr/bin/env bash
# Default: artifact-only Lean/runtime/pipeline/mutation qualification; no patched Zig needed.
# Full: AIR2LEAN_ZIG_AIR=<patched Zig> AIR2LEAN_ZIG=<stock Zig> scripts/progress-hints.sh full
# Full export is x86_64-linux baseline, ReleaseSafe, no error tracing. Native smoke tests use
# the host target separately and execute only finite calls. Local artifacts remain in .lake/;
# AIR2LEAN_PROGRESS_ARTIFACT_DIR can retain them elsewhere (CI uses uncached RUNNER_TEMP).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
exec python3 "$repo_root/tests/roadmap/progress/qualify.py" "$@"
