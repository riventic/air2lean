#!/usr/bin/env bash
# artifact-only: Lean model, pipeline and mutation checks; full: explicit patched+stock 0.16.
# Retain locally by default; CI uses uncached AIR2LEAN_WEAK_CAS_ARTIFACT_DIR under RUNNER_TEMP.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
exec python3 "$repo_root/tests/roadmap/weak-cas/qualify.py" "$@"
