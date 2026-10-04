#!/usr/bin/env bash
# Compiler execution must be scheduled by the coordinator's global resource guard.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-allocation-policy.XXXXXX")
trap 'rm -rf "$work"' EXIT
zig_bin=${AIR2LEAN_ZIG:-zig}
lake build ZigLean
lake env lean tests/roadmap/allocation-policy/Check.lean
lake env lean --run tests/roadmap/allocation-policy/Check.lean > "$work/lean.jsonl"
"$zig_bin" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$work/fixture" \
  --dep common -Mroot=tests/roadmap/allocation-policy/fixture.zig -Mcommon=tests/diff/common.zig
"$work/fixture" 2> "$work/zig.jsonl"
python3 tests/roadmap/allocation-policy/compare.py "$work/lean.jsonl" "$work/zig.jsonl"
