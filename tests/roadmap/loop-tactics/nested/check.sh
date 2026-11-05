#!/usr/bin/env bash
# P03 nested loops: retranslate the retained nested.pairs AIR, regenerate the inner loop's
# invariant and measure (P09, air2lean-invgen), kernel-check the full-state nested-loop proof
# (nested/Proof.lean) and its seeded mutants (mutants.json: a wrong cell relation, a dropped bound,
# a measure that does not decrease must each fail the inner loop's theorems), all through
# ../invgen-fixture.sh; then the proof's strength log. Needs a built translator (lake build
# air2lean); no Zig compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
source tests/roadmap/loop-tactics/invgen-fixture.sh
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-nested-loops.XXXXXX")
trap 'rm -rf "$work"' EXIT
invgen_fixture tests/roadmap/loop-tactics/nested Nested nested. "$work"
# The strength log of the proof (tests/roadmap/strength-log).
lake env lean tests/roadmap/strength-log/LoopTactics.lean
echo 'nested-loop translation, generated invariants and full-state proof checks passed'
