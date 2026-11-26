#!/usr/bin/env bash
# C10 evidence (docs/research/C10.md): Sc.lean's `#guard`s (the model against the sequentially
# consistent outcomes), the committed native observations checked against both, and the wrong
# observations and mutants of mutations.py. Runs no compiler; builds what Sc.lean imports.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/sc-order
python3 -B scripts/lean-deps.py --build "$dir"
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-sc-order.XXXXXX")
trap 'rm -rf "$work"' EXIT
"${lean_cmd[@]}" --run "$dir/Sc.lean" "$dir"/observed/*.txt
python3 -B "$dir/mutations.py" "$work"
echo 'sc-order model, observation and mutant gates passed'
