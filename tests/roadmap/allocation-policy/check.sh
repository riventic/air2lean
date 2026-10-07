#!/usr/bin/env bash
# Compiler execution must be scheduled by the coordinator's global resource guard.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-allocation-policy.XXXXXX")
trap 'rm -rf "$work"' EXIT
zig_bin=${AIR2LEAN_ZIG:-zig}
lake build ZigLean ZigLean.Sep.Alloc
lake env lean --run tests/roadmap/allocation-policy/Check.lean > "$work/lean.jsonl"
# Lean-only general-policy checks (oracle, budget, embedding, uncapped default, large fixture).
lake build Proofs.Lists.Policy
lake env lean --run tests/roadmap/allocation-policy/Oracle.lean
"$zig_bin" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$work/fixture" \
  --dep common -Mroot=tests/roadmap/allocation-policy/fixture.zig -Mcommon=tests/diff/common.zig
"$work/fixture" 2> "$work/zig.jsonl"
# Preserve raw comparison evidence only when explicitly requested, outside compiler caches.
if [ -n "${AIR2LEAN_ALLOCATION_REPORT_DIR:-}" ]; then
  mkdir -p "$AIR2LEAN_ALLOCATION_REPORT_DIR"
  cp "$work/lean.jsonl" "$AIR2LEAN_ALLOCATION_REPORT_DIR/lean.jsonl"
  cp "$work/zig.jsonl" "$AIR2LEAN_ALLOCATION_REPORT_DIR/zig.jsonl"
fi
python3 tests/roadmap/allocation-policy/compare.py "$work/lean.jsonl" "$work/zig.jsonl"
