#!/usr/bin/env bash
# P09 counted loops: retranslate the retained AIR of counted.zig (Zig 0.17.0), regenerate the
# loops' invariants and measures (air2lean-invgen), kernel-check counted/Proof.lean, which walks
# each loop with its generated invariant, and its seeded mutants (mutants.json: a wrong cell
# relation, a dropped bound, a dropped no-overflow fact of the counter, a measure that does not
# decrease, a dropped read-only cell, a candidate Houdini pruned put back and one it kept dropped
# must each fail their loop's theorems), all through
# ../invgen-fixture.sh. Needs a built translator (lake build air2lean); no Zig compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
source tests/roadmap/loop-tactics/invgen-fixture.sh
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-counted-loops.XXXXXX")
trap 'rm -rf "$work"' EXIT
invgen_fixture tests/roadmap/loop-tactics/counted Counted counted. "$work"
echo 'counted-loop translation, generated invariants and full-state proof checks passed'
