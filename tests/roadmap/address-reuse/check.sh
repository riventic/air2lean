#!/usr/bin/env bash
# M05 address reuse: kernel theorems (no sorry) and executable model regressions.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
lake build ZigLean.Sep.AddrReuse
kernel=$(lake env lean tests/roadmap/address-reuse/Kernel.lean)
printf '%s\n' "$kernel"
if grep -q sorryAx <<<"$kernel"; then
  echo "address reuse: a theorem depends on sorryAx" >&2
  exit 1
fi
lake env lean --run tests/roadmap/address-reuse/Check.lean
