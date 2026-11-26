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
# (ListsFba.Sentinel.fba_spec) and the witnesses of make_spec, append_grant, resize_grant and
# release_spec are verified; ListsFba/Wide.lean for the wider item types (Interfaces/WideSpec.lean:
# ListsFba.Wide.fba_spec and the same four witnesses per item type, one alignment each). The
# witnesses of append, resize and release hold a grant that the allocator's own alloc made from
# program start (ListsFba.granted_admissible over AllocFba.FBA.fthread_alloc_room).
# The modules are the fixture's library ListsFba (tests/roadmap/lakefile.toml) and what it imports:
# the FixedBufferAllocator of the library AllocFba (alloc-fba/check.sh checks that its translation
# is the translator's output) and M04's sentinel program and proofs of the library Interfaces (the
# retained 0.17.1 open translation; interfaces/check.sh checks it is the translator's output).
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
# The sentinel clients' claims with a witness: `make` at program start, and `append`, `resize`,
# `release` of a buffer that the allocator's own `alloc` granted (ListsFba.granted_admissible).
sentinel=(Interfaces.SentinelSpec.make_spec Interfaces.SentinelSpec.append_grant
  Interfaces.SentinelSpec.resize_grant Interfaces.SentinelSpec.release_spec)
for w in 16 32 64; do
  sentinel+=("Interfaces.WideSpec.make${w}_spec" "Interfaces.WideSpec.append${w}_grant"
    "Interfaces.WideSpec.resize${w}_grant" "Interfaces.WideSpec.release${w}_spec")
done
theorems=()
for name in ListsFba.env_runs ListsFba.start_admissible_at ListsFba.start_admissible ListsFba.fba_spec \
    ListsFba.make_admissible ListsFba.granted_admissible "ListsFba.granted_admissible'" \
    Lists.Append.append_spec.nonvacuous \
    Lists.Alloc.push_spec.nonvacuous Lists.Alloc.freeAll_spec.nonvacuous \
    Lists.Alloc.freeAll_freed.nonvacuous ListsFba.NotDead.free_not_dead \
    ListsFba.Sentinel.env_runs ListsFba.Sentinel.fba_spec \
    ListsFba.Wide.env_runs ListsFba.Wide.fba_spec "${sentinel[@]/%/.nonvacuous}"; do
  theorems+=(--declaration "$name")
done
python3 -B scripts/fixtures.py audit Proofs.Lists.Append Proofs.Lists.Alloc ListsFba.Witness \
  ListsFba.NotDead Interfaces.SentinelSpec ListsFba.Sentinel Interfaces.WideSpec ListsFba.Wide \
  "${theorems[@]}" --output "$work/assurance.json"
python3 - "$work/assurance.json" "${sentinel[@]}" <<'PY'
import json, sys
report = json.load(open(sys.argv[1]))
theorems = {t["name"]: t for t in report["theorems"]}
for name in ("Lists.Append.append_spec", "Lists.Alloc.push_spec", "Lists.Alloc.freeAll_spec",
             "Lists.Alloc.freeAll_freed", *sys.argv[2:]):
    witness = theorems[name]["statement"]["witnesses"]["nonvacuity"]
    assert witness["status"] == "verified", (name, witness)
    print(f"lists-fba: {name}: non-vacuity {witness['status']} ({witness['theorem']})")
PY
echo "lists-fba: ok"
