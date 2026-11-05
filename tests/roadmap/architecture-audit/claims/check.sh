#!/usr/bin/env bash
# Architecture audit area 4: compile the counterexample fixtures, re-extract their kernel
# statements, require them to match exposure-report.json, then pin the claim-tooling verdicts.
# build.sh builds the fixtures (the library AuditClaims of tests/roadmap/lakefile.toml) and what
# they import: run this through scripts/build-guard.py.
# Arguments go to test_exposure.py (`--require-fixed[=S2,S3,...]`).
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
bash "$here/build.sh"
python3 -B "$here/snapshot.py" check
python3 -B "$here/test_exposure.py" "$@"
# S1 structural-fix probe: the toolchain's leanchecker re-checks honest fixtures and rejects the
# kernel-unchecked ones that assumptions.py and claims.py accept.
bash "$here/kernel-replay.sh" AuditClaims.Vacuous AuditClaims.Shadow AuditClaims.AsmTotal AuditClaims.ShadowWithin
# The rejection must be the forged theorem's, not a missing olean or a load error.
for fixture in Unchecked:unchecked_total Universal:unchecked_universal; do
  module=AuditClaims.${fixture%%:*}
  if replay=$(bash "$here/kernel-replay.sh" "$module" 2>&1); then
    echo "error: leanchecker accepted $module" >&2
    exit 1
  fi
  if ! grep -qF "while replaying declaration 'AuditClaims.${fixture#*:}'" <<<"$replay"; then
    echo "error: leanchecker rejected $module, but not at AuditClaims.${fixture#*:}:" >&2
    echo "$replay" >&2
    exit 1
  fi
done
echo "architecture-audit claims fixtures: verdicts pinned"
