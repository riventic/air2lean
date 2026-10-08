#!/usr/bin/env bash
# C03 worker idle loop: retranslate the retained progress.idle AIR, compare it with the
# committed IdleLoop/Gen.lean, and kernel-check the safety, progress and starvation proofs.
# Needs a built translator and ZigLean (lake build ZigLean air2lean); no Zig compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/idle-loops
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
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-idle-loops.XXXXXX")
trap 'rm -rf "$work"' EXIT
"$translator" "$dir/air" -o "$work/Gen.lean" --namespace IdleLoop --prefix progress.
cmp "$work/Gen.lean" "$dir/IdleLoop/Gen.lean"
mkdir -p "$work/olean/IdleLoop"
export LEAN_PATH="$work/olean:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
for mod in Gen Basic Total Mem Shape Turns Steps Theorems; do
  lake env lean -R "$dir" -o "$work/olean/IdleLoop/$mod.olean" "$dir/IdleLoop/$mod.lean"
done
lake env lean "$dir/Check.lean"
# Semantic mutants of the client (bounded runtime witnesses): a skipped idle loop and a
# relaxed publication must make the read of data race.
lake env lean --run "$dir/Mutants.lean"
echo 'idle-loop translation, safety, progress-under-premise, starvation and mutant checks passed'
