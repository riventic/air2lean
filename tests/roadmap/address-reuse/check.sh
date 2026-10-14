#!/usr/bin/env bash
# M05 address reuse: kernel theorems (no sorry) and executable model regressions.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
python3 -B scripts/lean-deps.py --build tests/roadmap/address-reuse
lake build ZigLean.Mem.Reuse ZigLean.Sep.Full.AutoAll ZigLean.Sep.Full.Strength
kernel=$(lake env lean tests/roadmap/address-reuse/Kernel.lean)
printf '%s\n' "$kernel"
if grep -q sorryAx <<<"$kernel"; then
  echo "address reuse: a theorem depends on sorryAx" >&2
  exit 1
fi
# The strength log of the migrated statement (tests/roadmap/strength-log).
lake env lean tests/roadmap/strength-log/AddressReuse.lean
lake env lean --run tests/roadmap/address-reuse/Check.lean
