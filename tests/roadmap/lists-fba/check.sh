#!/usr/bin/env bash
# The list theorems over an open std.mem.Allocator (Proofs/Lists/Append.lean, Alloc.lean) are not
# vacuous: ListsFba/Witness.lean meets their premises with the translated FixedBufferAllocator of
# tests/roadmap/alloc-fba (its proved FAllocSpec, through ZigLean/Sep/Full/AllocBridge.lean) in the
# memory at program start (ZigLean/Sep/Full/WitnessStart.lean). The witnesses use only the standard
# axioms, and the claims extractor (scripts/assumptions.py, docs/claim-strength.md) reports the
# companions Lists.Append.append_spec.nonvacuous, Lists.Alloc.push_spec.nonvacuous,
# Lists.Alloc.freeAll_spec.nonvacuous and Lists.Alloc.freeAll_freed.nonvacuous as verified
# against the statements. ListsFba/Sentinel.lean does the same for M04's sentinel theorems
# (tests/roadmap/interfaces/Interfaces/SentinelSpec.lean): the allocator premise is met
# (ListsFba.Sentinel.fba_spec) and Interfaces.SentinelSpec.make_spec.nonvacuous is verified.
# The modules are the fixture's library ListsFba (tests/roadmap/lakefile.toml) and what it imports:
# the FixedBufferAllocator of the library AllocFba (alloc-fba/check.sh checks that its translation
# is the translator's output) and M04's sentinel program and proofs of the library Interfaces (the
# retained 0.17.0 open translation; interfaces/check.sh checks it is the translator's output).
# Lake builds them (scripts/fixtures.py; run it under scripts/build-guard.py); runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-lists-fba.XXXXXX")
trap 'rm -rf "$work"' EXIT
# Witness, NotDead (regression: an FBA free does not end the grant's block, so no resource knows
# it dead) and Sentinel; Proofs.Lists.Alloc for the claims extractor.
python3 -B scripts/fixtures.py build ListsFba Proofs.Lists.Alloc
# Axioms from the built environment (only the standard ones), and the claims extractor sees the
# companions next to the claims and checks their statements.
theorems=()
for name in ListsFba.env_runs ListsFba.start_admissible ListsFba.fba_spec Lists.Append.append_spec.nonvacuous \
    Lists.Alloc.push_spec.nonvacuous Lists.Alloc.freeAll_spec.nonvacuous \
    Lists.Alloc.freeAll_freed.nonvacuous ListsFba.NotDead.free_not_dead \
    ListsFba.Sentinel.env_runs ListsFba.Sentinel.fba_spec Interfaces.SentinelSpec.make_spec.nonvacuous; do
  theorems+=(--declaration "$name")
done
python3 -B scripts/fixtures.py audit Proofs.Lists.Append Proofs.Lists.Alloc ListsFba.Witness \
  ListsFba.NotDead Interfaces.SentinelSpec ListsFba.Sentinel "${theorems[@]}" --output "$work/assurance.json"
python3 - "$work/assurance.json" <<'PY'
import json, sys
report = json.load(open(sys.argv[1]))
theorems = {t["name"]: t for t in report["theorems"]}
for name in ("Lists.Append.append_spec", "Lists.Alloc.push_spec", "Lists.Alloc.freeAll_spec",
             "Lists.Alloc.freeAll_freed", "Interfaces.SentinelSpec.make_spec"):
    witness = theorems[name]["statement"]["witnesses"]["nonvacuity"]
    assert witness["status"] == "verified", (name, witness)
    print(f"lists-fba: {name}: non-vacuity {witness['status']} ({witness['theorem']})")
PY
echo "lists-fba: ok"
