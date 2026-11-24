#!/usr/bin/env bash
# The translator's CPU-feature table of inline-asm instructions (Air2Lean/AsmFeatures.lean, A02
# decision D1, premise ASM-09) against the Zig 0.17.1 compiler's own tables (feature_table.py).
# Needs a built translator and the pinned compiler source (scripts/cas.py src; cached with
# AIR2LEAN_CAS_DIR). Runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-asm-features.XXXXXX")
trap 'rm -rf "$work"' EXIT
source=$(python3 -B "$repo_root/scripts/cas.py" src 0.17.1 --scratch "$work/src")
"$translator" --print-asm-feature-table > "$work/table.json"
python3 -B "$repo_root/tests/roadmap/asm-semantics/feature_table.py" "$work/table.json" "$source"
