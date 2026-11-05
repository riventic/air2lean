#!/usr/bin/env bash
# P03 nested loops: retranslate the retained nested.pairs AIR, compare it with the committed
# Nested/Gen.lean, regenerate the inner loop's invariant and measure (P09, air2lean-invgen) and
# compare them with the committed Nested/Inv.lean, and kernel-check the full-state nested-loop
# proof (nested/Proof.lean). Seeded mutants of the generated invariant and measure must make the
# proof fail: the generator is untrusted, and only the check accepts its output.
# Needs a built translator and the full-state library (lake build air2lean
# ZigLean.Sep.Full.Loop ZigLean.Sep.Full.Auto ZigLean.Sep.Full.Strength); no Zig compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
python3 -B scripts/lean-deps.py --build tests/roadmap/loop-tactics/nested
lake build air2lean-invgen
dir=tests/roadmap/loop-tactics/nested
python3 - "$dir" <<'PY'
import hashlib, json, pathlib, sys
d = pathlib.Path(sys.argv[1])
prov = json.loads((d / "provenance.json").read_text())
for rel, want in prov["artifacts"].items():
    got = hashlib.sha256((d / rel).read_bytes()).hexdigest()
    if got != want:
        sys.exit(f"{rel}: sha256 {got} != provenance {want}")
src = pathlib.Path(prov["source"])
if hashlib.sha256(src.read_bytes()).hexdigest() != prov["source_sha256"]:
    sys.exit(f"{src} changed since the retained export; re-export and update provenance.json")
PY
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first: lake build air2lean' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-nested-loops.XXXXXX")
trap 'rm -rf "$work"' EXIT
"$translator" "$dir/air" -o "$work/Gen.lean" --namespace Nested --prefix nested.
cmp "$work/Gen.lean" "$dir/Nested/Gen.lean"
mkdir -p "$work/olean/Nested"
export LEAN_PATH="$work/olean:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -R "$dir" -o "$work/olean/Nested/Gen.olean" "$dir/Nested/Gen.lean"
# The generated invariants, reproduced byte for byte from the committed translation.
lake env "$repo_root/.lake/build/bin/air2lean-invgen" Nested.Gen Nested -o "$work/Inv.lean"
cmp "$work/Inv.lean" "$dir/Nested/Inv.lean" ||
  { echo "$dir/Nested/Inv.lean is stale: regenerate it with air2lean-invgen" >&2; exit 1; }
lake env lean -R "$dir" -o "$work/olean/Nested/Inv.olean" "$dir/Nested/Inv.lean"
lake env lean -R "$dir" -o "$work/olean/Proof.olean" "$dir/Proof.lean"
# Negative controls: each seeded mutant of the generated file still elaborates, and the proof
# then fails: a wrong cell relation, a dropped bound, a measure that does not decrease.
for mutant in relation bound measure; do
  mdir="$work/mutant-$mutant"
  mkdir -p "$mdir/olean/Nested" "$mdir/src/Nested"
  cp "$work/olean/Nested/Gen.olean" "$mdir/olean/Nested/"
  python3 - "$dir/Nested/Inv.lean" "$mdir/src/Nested/Inv.lean" "$mutant" <<'PY'
import pathlib, sys
src, dst, mutant = sys.argv[1:]
text = pathlib.Path(src).read_text()
old, new = {
    "relation": ("⟪v.toNat = v0.toNat + ", "⟪v.toNat = 1 + v0.toNat + "),
    "bound": ("s.j.toNat ≤ s.i.toNat ∧", "True ∧"),
    "measure": ("Nat :=\n  s.i.toNat - s.j.toNat\n", "Nat :=\n  s.i.toNat\n"),
}[mutant]
if text.count(old) != 1:
    sys.exit(f"mutant {mutant}: {old!r} does not occur exactly once in the generated file")
pathlib.Path(dst).write_text(text.replace(old, new))
PY
  LEAN_PATH="$mdir/olean:$LEAN_PATH" lake env lean -R "$mdir/src" -o "$mdir/olean/Nested/Inv.olean" \
    "$mdir/src/Nested/Inv.lean"
  if LEAN_PATH="$mdir/olean:$LEAN_PATH" lake env lean -R "$dir" "$dir/Proof.lean" > "$mdir/log" 2>&1; then
    echo "mutant $mutant of the generated invariant was accepted" >&2; exit 1
  fi
  grep -q "Proof.lean:[0-9]*:[0-9]*: error" "$mdir/log" ||
    { echo "mutant $mutant: the proof failed without an elaboration error:" >&2; tail -n 5 "$mdir/log" >&2; exit 1; }
  echo "mutant $mutant of the generated invariant rejected"
done
# The strength log of the proof (tests/roadmap/strength-log).
lake env lean tests/roadmap/strength-log/LoopTactics.lean
echo 'nested-loop translation, generated invariants and full-state proof checks passed'
