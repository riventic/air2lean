#!/usr/bin/env bash
# C02 thread-local storage: retranslate the retained 0.16.0 and 0.15.2 exports, compare with
# ThreadLocals/Gen.lean, kernel-check the proofs, run sampled schedules and mutants, and run
# the CLI rejection regressions. Needs `lake build air2lean ZigLean.Conc.TlsLemmas`; no Zig.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
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
  lake env lean -R "$dir" -o "$work/olean/ThreadLocals/$mod.olean" "$dir/ThreadLocals/$mod.lean"
done
lake env lean "$dir/Check.lean"
lake env lean --run "$dir/ThreadLocals/Runtime.lean"
PYTHONDONTWRITEBYTECODE=1 python3 "$dir/test_cli.py" "$translator"
echo 'thread-local translation, proofs, schedules, mutants and CLI checks passed'
