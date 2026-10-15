#!/usr/bin/env bash
# Soundness audit 2026-10-14 (docs/architecture-audit/soundness-2026-10-14.md): reproduce the
# kernel-checked counterexamples and the claim-layer probe. Every case prints `vulnerable` while
# its finding is open. A fix flips its case: a kernel file then fails to elaborate (the false
# statement is no longer provable) and the probe prints `fixed`.
#
#   tests/roadmap/architecture-audit/soundness-1014/check.sh [--require-fixed]
#
# Needs a full build (scripts/full-build.sh); run it through scripts/build-guard.py.
set -uo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$here/../../../.." && pwd)
cd "$repo_root"
require_fixed=0
[ "${1:-}" = --require-fixed ] && require_fixed=1
open=0

lean_case() {
  local name=$1 file=$2
  if lake env lean "$here/$file" >/dev/null 2>&1; then
    echo "$name: vulnerable -- $file elaborates"
    open=1
  else
    echo "$name: fixed -- $file no longer elaborates"
  fi
}

lean_case S4-nonstrict-unspecified nonstrict-unspecified/NonStrict.lean
# Evidence for S1 (stays true after the fix): the two fixture theorems are vacuous, the root panics.
lake env lean "$here/vacuous-safety/Vacuity.lean" >/dev/null 2>&1 \
  && echo "S1 evidence: Vacuity.lean elaborates" || { echo "S1 evidence: Vacuity.lean FAILED"; open=1; }
lean_case F2-contract-fee-false contract-vacuity/FeeFalse.lean
python3 -B "$here/vacuous-safety/probe.py" --require-fixed || open=1
for extra in "$here"/translator/check.sh; do
  [ -x "$extra" ] && { "$extra" || open=1; }
done

[ "$require_fixed" = 1 ] && [ "$open" = 1 ] && exit 1
exit 0
