#!/usr/bin/env bash
# M01 allocator identity: executable regressions of the std-mode model (ZigLean/Mem/Owned.lean).
# The M01 theorems are stated over the translated arena (tests/roadmap/alloc-arena: `free_in_node`,
# `reset_free_all_frame`, `foreign_free_panics`).
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
python3 -B scripts/lean-deps.py --build tests/roadmap/allocator-identity
lake env lean --run tests/roadmap/allocator-identity/Check.lean
