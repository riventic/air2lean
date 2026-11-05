# Sourced by the check.sh of a fixture with generated loop invariants (P09,
# docs/invariant-synthesis.md), from the repository root:
#
#   invgen_fixture DIR NAMESPACE PREFIX WORK
#
# checks the retained AIR in DIR/air against DIR/provenance.json, retranslates it and compares the
# result with the committed DIR/NAMESPACE/Gen.lean, regenerates the loop invariants and measures
# (air2lean-invgen, the fixture's target of scripts/invgen.py) and compares them with the committed
# DIR/NAMESPACE/Inv.lean, kernel-checks DIR/Proof.lean, and runs the seeded mutants of
# DIR/mutants.json (invgen_mutants.py): the generator is untrusted, and only the check accepts its
# output. The oleans go to WORK/olean, which leads LEAN_PATH afterwards.
# Needs a built translator (lake build air2lean); builds the generator (lake exe air2lean-invgen)
# and the full-state library modules the proof imports itself; no Zig compiler.
invgen_fixture() {
  local dir=$1 ns=$2 prefix=$3 work=$4
  python3 -B scripts/lean-deps.py --build "$dir"
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
  local translator=${AIR2LEAN_TRANSLATOR:-"$PWD/.lake/build/bin/air2lean"}
  [ -x "$translator" ] || { echo 'build the translator first: lake build air2lean' >&2; return 1; }
  "$translator" "$dir/air" -o "$work/Gen.lean" --namespace "$ns" --prefix "$prefix"
  cmp "$work/Gen.lean" "$dir/$ns/Gen.lean"
  mkdir -p "$work/olean/$ns"
  export LEAN_PATH="$work/olean:$PWD/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
  lake env lean -R "$dir" -o "$work/olean/$ns/Gen.olean" "$dir/$ns/Gen.lean"
  # The generated invariants, reproduced byte for byte from the committed translation (the
  # generator's pruning walks import the library, scripts/invgen.py's LIBRARY).
  lake build -q ZigLean.Sep.Full.AutoAll
  lake exe air2lean-invgen "$ns.Gen" "$ns" --source "$dir/$ns/Gen.lean" -o "$work/Inv.lean"
  cmp "$work/Inv.lean" "$dir/$ns/Inv.lean"
  lake env lean -R "$dir" -o "$work/olean/$ns/Inv.olean" "$dir/$ns/Inv.lean"
  lake env lean -R "$dir" -o "$work/olean/Proof.olean" "$dir/Proof.lean"
  python3 -B tests/roadmap/loop-tactics/invgen_mutants.py "$dir" "$ns" "$work"
}
