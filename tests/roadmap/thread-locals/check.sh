#!/usr/bin/env bash
# C02 thread-local storage: retranslate the retained 0.16.0 and 0.15.2 exports, compare with
# ThreadLocals/Gen.lean, kernel-check the proofs, run sampled schedules and mutants, and run
# the CLI rejection regressions. Needs `lake build air2lean ZigLean.Sep.Full.ThreadTls
# ZigLean.Sep.Full.ThreadFacts`; no Zig.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 -B scripts/lean-deps.py --build tests/roadmap/thread-locals
dir=tests/roadmap/thread-locals
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first: lake build air2lean' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-thread-locals.XXXXXX")
trap 'rm -rf "$work"' EXIT
"$translator" "$dir/air/0.16.0" -o "$work/Gen.lean" --namespace ThreadLocals --prefix thread_locals.
cmp "$work/Gen.lean" "$dir/ThreadLocals/Gen.lean"
"$translator" "$dir/air/0.15.2" -o "$work/Gen15.lean" --namespace ThreadLocals --prefix thread_locals.
cmp <(tail -n +2 "$work/Gen15.lean") <(tail -n +2 "$dir/ThreadLocals/Gen.lean")
mkdir -p "$work/olean/ThreadLocals"
export LEAN_PATH="$work/olean:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
for mod in Gen Counters Leak; do
  # With Lake's native fsym where the module reaches it (scripts/lean-deps.py --lean).
  python3 -B scripts/lean-deps.py --lean -R "$dir" -o "$work/olean/ThreadLocals/$mod.olean" "$dir/ThreadLocals/$mod.lean"
done
lake env lean "$dir/Check.lean"
# The strength log of the migrated proof (tests/roadmap/strength-log).
lake env lean tests/roadmap/strength-log/ThreadLocals.lean
lake env lean --run "$dir/ThreadLocals/Runtime.lean"
python3 -B scripts/mutation_kill_log.py --check tests/roadmap/thread-locals/check.sh \
  tests/roadmap/thread-locals/ThreadLocals/Runtime.lean shared-instance immortal-instance
PYTHONDONTWRITEBYTECODE=1 python3 "$dir/test_cli.py" "$translator"
echo 'thread-local translation, proofs, schedules, mutants and CLI checks passed'
