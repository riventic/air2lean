#!/usr/bin/env bash
# The kernel conclusion, then the claim/receipt gates: no sampled-evidence substitute.
# Outcomes/Contracts.lean and Outcomes/Taxonomy.lean are the fixture library Outcomes, and the
# strength log of Taxonomy (tests/roadmap/strength-log/OutcomeTaxonomy.lean) a module of the
# library StrengthLog (tests/roadmap/lakefile.toml): Lake builds them with what they import
# (scripts/fixtures.py; run this under scripts/build-guard.py).
set -euo pipefail
cd "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)"
python3 -B -m unittest discover -s tests/roadmap/outcome-taxonomy -p 'test_*.py'
out=.lake/assurance/outcome-taxonomy
mkdir -p "$out"
python3 -B scripts/fixtures.py build Outcomes StrengthLog
python3 -B scripts/fixtures.py audit Outcomes.Contracts --output "$out/audit.json"
python3 -B tests/roadmap/outcome-taxonomy/extracted.py "$out/audit.json"
