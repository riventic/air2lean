#!/usr/bin/env bash
# Bring every generated file up to date in dependency order; run it after merging main.
#
#   scripts/regen.sh                 regenerate everything (commits, provenance last)
#   scripts/regen.sh --pr            only the PR-scoped files (whole-tree files are made at merge)
#   scripts/regen.sh --check [--pr]  check only: scripts/preflight.sh
#   scripts/regen.sh --list          steps, scope and outputs
#
# Set AIR2LEAN_CAS_DIR to share Lake builds and patched compilers between worktrees
# (docs/build-cache.md). Details: scripts/regen.py --help.
set -euo pipefail
exec python3 -B "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/regen.py" "$@"
