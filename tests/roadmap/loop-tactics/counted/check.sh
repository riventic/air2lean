#!/usr/bin/env bash
# P09 counted loops: retranslate the retained AIR of counted.zig (Zig 0.17.0), regenerate the
# loops' invariants, measures and exit posts (air2lean-invgen, `@[fsym_inv]`), kernel-check
# counted/Proof.lean, whose bare `fsym` walks apply each loop's generated invariant, and its seeded
# mutants (mutants.json: a wrong cell relation, a dropped bound under `!=`, a dropped `x ≤ b + 1`
# of a `<=` counter, a measure that does not decrease, a dropped read-only cell, a too strong exit
# post, a candidate Houdini pruned put back and one it kept dropped must each fail their
# function's theorem), all through
# ../invgen-fixture.sh. Needs a built translator (lake build air2lean); no Zig compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
source tests/roadmap/loop-tactics/invgen-fixture.sh
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-counted-loops.XXXXXX")
trap 'rm -rf "$work"' EXIT
invgen_fixture tests/roadmap/loop-tactics/counted Counted counted. "$work"
echo 'counted-loop translation, generated invariants and full-state proof checks passed'
