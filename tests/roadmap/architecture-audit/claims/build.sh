#!/usr/bin/env bash
# Build the architecture-audit claim fixtures (module root AuditClaims), then extract their
# assurance report. The fixtures are the library AuditClaims of the proof-fixture package
# (tests/roadmap/lakefile.toml): scripts/fixtures.py builds them, and the library modules they
# import, into tests/roadmap/.lake/build, outside the root .lake/build/lib/lean (proof receipts
# reject untracked compiled modules there). With AIR2LEAN_CAS_DIR set, unchanged modules come from
# the shared artifact cache (scripts/cas.py run). Run it under scripts/build-guard.py.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
out=.lake/architecture-audit/claims
python3 -B scripts/fixtures.py build AuditClaims
mkdir -p "$out"
export LEAN_PATH="$repo_root/tests/roadmap/.lake/build/lib/lean"
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
