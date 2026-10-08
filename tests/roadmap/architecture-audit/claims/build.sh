#!/usr/bin/env bash
# Compile the architecture-audit claim fixtures (module root AuditClaims) into a private olean
# directory outside .lake/build/lib/lean (proof receipts reject untracked compiled modules there),
# then extract their assurance report. Requires a built ZigLean and AssuranceTools.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
src=tests/roadmap/architecture-audit/claims
out=.lake/architecture-audit/claims
mkdir -p "$out/lib/AuditClaims"
export LEAN_PATH="$repo_root/$out/lib"
for module in Gen Vacuous Shadow Unchecked AsmTotal; do
  lake env lean -R "$src" -o "$out/lib/AuditClaims/$module.olean" "$src/AuditClaims/$module.lean"
done
# Separate audits: Shadow declares its own Zig.TotalTriple and cannot share an environment with
# ZigLean.Sep.Total, exactly as a project contract audited alone with --module.
for group in "Vacuous Unchecked AsmTotal" "Shadow"; do
  name=${group%% *}
  args=()
  for module in $group; do args+=(--module "AuditClaims.$module"); done
  status=0
  python3 -B scripts/assumptions.py --no-build --output "$out/assurance-$name.json" "${args[@]}" || status=$?
  echo "assumptions.py [$group] exit $status"
done
