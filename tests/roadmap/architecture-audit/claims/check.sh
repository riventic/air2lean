#!/usr/bin/env bash
# Architecture audit area 4: compile the counterexample fixtures, re-extract their kernel
# conclusions, require them to match exposure-report.json, then pin the claim-tooling verdicts.
# Needs `lake build ZigLean ZigLean.Sep.Total AssuranceTools` (run heavy builds via build-guard).
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
bash "$here/build.sh"
python3 -B "$here/snapshot.py" check
python3 -B "$here/test_exposure.py" "$@"
# S1 structural-fix probe: the toolchain's leanchecker re-checks honest fixtures and rejects the
# kernel-unchecked one that assumptions.py and claims.py accept.
bash "$here/kernel-replay.sh" AuditClaims.Vacuous AuditClaims.Shadow AuditClaims.AsmTotal
if bash "$here/kernel-replay.sh" AuditClaims.Unchecked; then
  echo "error: leanchecker accepted AuditClaims.Unchecked" >&2
  exit 1
fi
echo "architecture-audit claims fixtures: verdicts pinned"
