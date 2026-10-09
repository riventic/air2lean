#!/usr/bin/env bash
# Architecture audit area 4: compile the counterexample fixtures, re-extract their kernel
# statements, require them to match exposure-report.json, then pin the claim-tooling verdicts.
# Needs `lake build ZigLean AssuranceTools Proofs.Asm.Gen` (run heavy builds via build-guard).
# Arguments go to test_exposure.py (`--require-fixed[=S2,S3,...]`).
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
bash "$here/build.sh"
python3 -B "$here/snapshot.py" check
python3 -B "$here/test_exposure.py" "$@"
# S1 structural-fix probe: the toolchain's leanchecker re-checks honest fixtures and rejects the
# kernel-unchecked ones that assumptions.py and claims.py accept.
bash "$here/kernel-replay.sh" AuditClaims.Vacuous AuditClaims.Shadow AuditClaims.AsmTotal AuditClaims.ShadowWithin
for module in AuditClaims.Unchecked AuditClaims.Universal; do
  if bash "$here/kernel-replay.sh" "$module"; then
    echo "error: leanchecker accepted $module" >&2
    exit 1
  fi
done
echo "architecture-audit claims fixtures: verdicts pinned"
