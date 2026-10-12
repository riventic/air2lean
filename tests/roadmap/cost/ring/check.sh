#!/usr/bin/env bash
# P06 queue-operation bound: retranslate the retained ring.drain/ring.push AIR (Zig 0.17.0),
# compare it with the committed Ring/Gen.lean, and kernel-check Proof.lean (drain bound under the
# capacity premises, failing and diverging runs). Needs a built translator and
# ZigLean.Sep.CostRuns ZigLean.Range (lake build air2lean ZigLean.Sep.CostRuns ZigLean.Range); no
# Zig compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/cost/ring
python3 - "$dir" <<'PY'
import hashlib, json, pathlib, sys
d = pathlib.Path(sys.argv[1])
prov = json.loads((d / "provenance.json").read_text())
for rel, want in prov["artifacts"].items():
    got = hashlib.sha256((d / rel).read_bytes()).hexdigest()
    if got != want:
        sys.exit(f"{rel}: sha256 {got} != provenance {want}")
if sorted(p.name for p in (d / "air").iterdir()) != sorted(pathlib.Path(r).name for r in prov["artifacts"]):
    sys.exit("air/ holds files that provenance.json does not list")
src = pathlib.Path(prov["source"])
if hashlib.sha256(src.read_bytes()).hexdigest() != prov["source_sha256"]:
    sys.exit(f"{src} changed since the retained export; re-export and update provenance.json")
PY
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first: lake build air2lean' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-ring.XXXXXX")
trap 'rm -rf "$work"' EXIT
"$translator" "$dir/air" -o "$work/Gen.lean" --namespace Ring --prefix ring.
cmp "$work/Gen.lean" "$dir/Ring/Gen.lean"
mkdir -p "$work/olean/Ring"
export LEAN_PATH="$work/olean:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -R "$dir" -o "$work/olean/Ring/Gen.olean" "$dir/Ring/Gen.lean"
lake env lean "$dir/Proof.lean"
echo 'ring-buffer translation, queue bound, failing and diverging run checks passed'
