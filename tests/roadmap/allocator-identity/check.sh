#!/usr/bin/env bash
# M01 allocator identity: kernel theorems (no sorry) and executable model regressions.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
lake build ZigLean.Sep.ArenaClient
kernel=$(lake env lean tests/roadmap/allocator-identity/Kernel.lean)
printf '%s\n' "$kernel"
if grep -q sorryAx <<<"$kernel"; then
  echo "allocator identity: a theorem depends on sorryAx" >&2
  exit 1
fi
lake env lean --run tests/roadmap/allocator-identity/Check.lean
