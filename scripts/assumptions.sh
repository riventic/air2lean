#!/usr/bin/env bash
# Build and audit all shipped ZigLean/Proofs theorems. See docs/assumptions-audit.md.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
exec python3 "$repo_root/scripts/assumptions.py" "$@"
