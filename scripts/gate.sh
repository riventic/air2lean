#!/usr/bin/env bash
# The pre-merge gate: run it before every push and merge (docs/ci.md#pre-merge-gate).
#
#   scripts/gate.sh [--base REF] [--check] [--only UNIT,...] [--jobs N] [--logs DIR]
#   scripts/gate.sh --list            the units, in dependency order
#
# Set AIR2LEAN_CAS_DIR so that the worktrees share their builds (docs/build-cache.md).
# Details: scripts/gate.py --help.
set -euo pipefail
exec python3 -B "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/gate.py" "$@"
