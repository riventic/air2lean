#!/usr/bin/env bash
# P03 nested loops: retranslate the retained nested.pairs AIR, compare it with the committed
# Nested/Gen.lean, and kernel-check the nested-loop proof and inference reports
# (tests/roadmap/loop-tactics/Nested.lean). Needs a built translator and
# ZigLean.Sep.LoopTemplate ZigLean.Range (lake build air2lean ZigLean.Sep.LoopTemplate
# ZigLean.Range); no Zig compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
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
lake env lean tests/roadmap/loop-tactics/Nested.lean
echo 'nested-loop translation, template proof and inference checks passed'
