#!/usr/bin/env bash
# P03 nested loops: retranslate the retained nested.pairs AIR, regenerate both loops' invariants,
# measures and exit posts (P09, air2lean-invgen, `@[fsym_inv]`; the outer one from the inner
# loop's exit post), kernel-check the full-state nested-loop proof (nested/Proof.lean, whose
# `pairs_total` walk applies them) and its seeded mutants (mutants.json: of the inner loop a wrong
# cell relation, a dropped bound, a measure that does not decrease; of the outer loop a wrong sum
# and a dropped no-overflow fact; each must fail `pairs_total`), all through
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
