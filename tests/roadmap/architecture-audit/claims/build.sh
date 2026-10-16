#!/usr/bin/env bash
# Compile the architecture-audit claim fixtures (module root AuditClaims) into a private olean
# directory outside .lake/build/lib/lean (proof receipts reject untracked compiled modules there),
# then extract their assurance report. Builds the library modules the fixtures import first
# (scripts/lean-deps.py --build; the extractor builds AssuranceTools itself): run it under
# scripts/build-guard.py. With AIR2LEAN_CAS_DIR set, a fixture whose source and import closure are
# unchanged is copied from the shared cache instead of compiled (scripts/lean_cache.py).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
src=tests/roadmap/architecture-audit/claims
out=.lake/architecture-audit/claims
python3 -B scripts/lean-deps.py --build "$src"
mkdir -p "$out/lib/AuditClaims"
export LEAN_PATH="$repo_root/$out/lib"
python3 -B scripts/lean_cache.py compile --root "$src" --out "$out/lib" \
  "$src"/AuditClaims/{Gen,Vacuous,Shadow,Unchecked,AsmTotal,ShadowWithin,Universal}.lean
# The audits below share their kernel replays of identical Lake-built oleans (this build only).
replay_cache=$out/replay-cache.json
rm -f "$replay_cache"
# Separate audits: Shadow declares its own Zig.Full.FTotalTriple, exactly as a project contract
# audited alone with --module, and ShadowWithin its own Zig.Full.FTTotalTriple. The audit environment
# imports the registered claim heads (tools/Assurance.lean), so both audits must fail with a
# name clash; their stderr is kept.
# Unchecked and Universal are audited apart because kernel replay (S1) rejects them and so
# fails their whole report.
for group in "Vacuous AsmTotal" "Shadow" "ShadowWithin" "Unchecked Universal"; do
  name=${group%% *}
  args=()
  for module in $group; do args+=(--module "AuditClaims.$module"); done
  status=0
  python3 -B scripts/assumptions.py --no-build --replay-cache "$replay_cache" --output "$out/assurance-$name.json" \
    "${args[@]}" 2> "$out/assurance-$name.stderr" || status=$?
  echo "assumptions.py [$group] exit $status"
done
