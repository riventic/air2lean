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
for module in Gen Vacuous Shadow Unchecked AsmTotal ShadowWithin Universal Escapes; do
  lake env lean -R "$src" -o "$out/lib/AuditClaims/$module.olean" "$src/AuditClaims/$module.lean"
done
# Separate audits: Shadow declares its own Zig.TotalTriple, exactly as a project contract audited
# alone with --module, and ShadowWithin its own Zig.TotalTripleWithin. The audit environment
# imports the registered claim heads (tools/Assurance.lean), so both audits must fail with a
# name clash; their stderr is kept.
# Unchecked and Universal are audited apart because kernel replay (S1) rejects them and so
# fails their whole report. Escapes (H4) is audited apart because its policy violations fail its
# report.
for group in "Vacuous AsmTotal" "Shadow" "ShadowWithin" "Unchecked Universal" "Escapes"; do
  name=${group%% *}
  args=()
  for module in $group; do args+=(--module "AuditClaims.$module"); done
  status=0
  python3 -B scripts/assumptions.py --no-build --output "$out/assurance-$name.json" "${args[@]}" \
    2> "$out/assurance-$name.stderr" || status=$?
  echo "assumptions.py [$group] exit $status"
done
