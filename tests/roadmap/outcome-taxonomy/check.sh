#!/usr/bin/env bash
# The kernel conclusion, then the claim/receipt gates: no sampled-evidence substitute.
set -euo pipefail
cd "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)"
python3 -B scripts/lean-deps.py --build tests/roadmap/outcome-taxonomy
python3 -B -m unittest discover -s tests/roadmap/outcome-taxonomy -p 'test_*.py'
out=.lake/assurance/outcome-taxonomy
fixtures=.lake/assurance/fixtures/lean
mkdir -p "$out" "$fixtures"
export LEAN_PATH="$PWD/$fixtures${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -R tests/roadmap/outcome-taxonomy -o "$fixtures/Contracts.olean" tests/roadmap/outcome-taxonomy/Contracts.lean
scripts/assumptions.sh --no-build --module Contracts --output "$out/audit.json"
python3 -B tests/roadmap/outcome-taxonomy/extracted.py "$out/audit.json"
lake env lean -R tests/roadmap/outcome-taxonomy -o "$out/Taxonomy.olean" tests/roadmap/outcome-taxonomy/Taxonomy.lean
LEAN_PATH="$PWD/$out${LEAN_PATH:+:$LEAN_PATH}" lake env lean tests/roadmap/strength-log/OutcomeTaxonomy.lean
