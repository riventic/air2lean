#!/usr/bin/env bash
# The list theorems over an open std.mem.Allocator (Proofs/Lists/Append.lean, Alloc.lean) are not
# vacuous: ListsFba/Witness.lean meets their premises with the translated FixedBufferAllocator of
# tests/roadmap/alloc-fba (its proved FAllocSpec, through ZigLean/Sep/Full/AllocBridge.lean) in the
# memory at program start (ZigLean/Sep/Full/WitnessStart.lean). The witnesses use only the standard
# axioms, and the claims extractor (scripts/assumptions.py, docs/claim-strength.md) reports the
# companions Lists.Append.append_spec.nonvacuous, Lists.Alloc.push_spec.nonvacuous and
# Lists.Alloc.freeAll_spec.nonvacuous as verified
# against the statements. Builds the Lean modules it needs (run it under scripts/build-guard.py);
# runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/lists-fba
fba=tests/roadmap/alloc-fba
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-lists-fba.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocFba" "$work/ListsFba"
lake build Proofs.Lists.Append Proofs.Lists.Alloc ZigLean.Sep.Full.AllocBridge ZigLean.Sep.Full.WitnessStart ZigLean.Sep.Full.ResetLedger \
  ZigLean.Witness ZigLean.Sep.Full.AllocSpec ZigLean.Sep.Full.Auto ZigLean.Sep.Full.AutoClaims \
  ZigLean.Sep.Full.AutoThread
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The FixedBufferAllocator's translation and its FAllocSpec (alloc-fba/check.sh checks that the
# translation is the translator's output).
for m in Gen Impl Full; do
  cp "$fba/AllocFba/$m.lean" "$work/AllocFba/$m.lean"
  "${lean_cmd[@]}" -R "$work" -o "$work/AllocFba/$m.olean" "$work/AllocFba/$m.lean"
done
cp "$here/ListsFba/Witness.lean" "$work/ListsFba/Witness.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/ListsFba/Witness.olean" "$work/ListsFba/Witness.lean"
# Regression: an FBA free does not end the grant's block, so no resource knows it dead.
cp "$here/ListsFba/NotDead.lean" "$work/ListsFba/NotDead.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/ListsFba/NotDead.olean" "$work/ListsFba/NotDead.lean"
names=(ListsFba.env_runs ListsFba.start_admissible ListsFba.fba_spec Lists.Append.append_spec.nonvacuous
  Lists.Alloc.push_spec.nonvacuous Lists.Alloc.freeAll_spec.nonvacuous ListsFba.NotDead.free_not_dead)
{ echo "import ListsFba.NotDead"; for n in "${names[@]}"; do echo "#print axioms $n"; done; } > "$work/Axioms.lean"
"${lean_cmd[@]}" "$work/Axioms.lean" > "$work/axioms.txt"
python3 - "$work/axioms.txt" "${#names[@]}" <<'PY'
import re, sys
text, n = open(sys.argv[1]).read(), int(sys.argv[2])
groups = re.findall(r"depends on axioms: \[([^\]]*)\]|(does not depend on any axioms)", text)
used = {a.strip() for g, _ in groups for a in g.split(",") if a.strip()}
assert len(groups) == n and used <= {"propext", "Classical.choice", "Quot.sound"}, text
PY
# The claims extractor sees the companions next to the claims and checks their statements.
python3 scripts/assumptions.py --no-build --module Proofs.Lists.Append --module Proofs.Lists.Alloc \
  --module ListsFba.Witness --output "$work/assurance.json" > "$work/assurance.log" 2>&1 || true
python3 - "$work/assurance.json" "$work/assurance.log" <<'PY'
import json, sys
report = json.load(open(sys.argv[1]))
assert report.get("status") != "error", open(sys.argv[2]).read()
theorems = {t["name"]: t for t in report["theorems"]}
for name in ("Lists.Append.append_spec", "Lists.Alloc.push_spec", "Lists.Alloc.freeAll_spec"):
    witness = theorems[name]["statement"]["witnesses"]["nonvacuity"]
    assert witness["status"] == "verified", (name, witness)
    print(f"lists-fba: {name}: non-vacuity {witness['status']} ({witness['theorem']})")
PY
echo "lists-fba: ok"
