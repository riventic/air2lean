#!/usr/bin/env bash
# C03 worker idle loop: retranslate the retained progress.idle AIR, compare it with the
# committed IdleLoop/Gen.lean, and kernel-check the safety, progress and starvation proofs.
# Needs a built translator and ZigLean (lake build ZigLean air2lean); no Zig compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 -B scripts/lean-deps.py --build tests/roadmap/idle-loops
dir=tests/roadmap/idle-loops
# air: progress.idle's call closure in tests/roadmap/progress/progress.zig (exports.json), pinned
# by exports.lock.json.
python3 -B scripts/fixture-exports.py check idle-loops
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
