#!/usr/bin/env bash
# Root-only fresh audit. This is the sole guard; do not wrap it in a nested guard.
set -euo pipefail
umask 077
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
guard="$repo_root/scripts/build-guard.py"
guard_pin=()
if [ "${1:-}" = --guard ]; then
  [ "$#" -ge 7 ] && [ "$3" = --guard-sha256 ] || { echo 'external --guard needs --guard-sha256 HASH and three arguments' >&2; exit 2; }
  guard=$2
  guard_pin=(--guard-sha256 "$4")
  shift 4
fi
[ "$#" -ge 3 ] || { echo 'usage: check.sh FRESH_ATTEMPT REAL_LEAN_TOOLCHAIN PROFILE_LABEL [MODULE ...] (optional leading --guard PATH --guard-sha256 HASH)' >&2; exit 2; }
attempt=$1
toolchain=$2
profile=$3
shift 3
python=$(python3 -c 'import pathlib,sys;print(pathlib.Path(sys.executable).resolve())')
helper="$repo_root/scripts/proof-receipt.py"
lock=${AIR2LEAN_BUILD_LOCK:-"$HOME/.cache/air2lean/build.lock"}
modules=()
for module in "$@"; do modules+=(--module "$module"); done
"$python" "$helper" prepare "$attempt" --toolchain "$toolchain" --profile "$profile" --lock "$lock" "${modules[@]}" --guard "$guard" "${guard_pin[@]}"
# Preparation has no compiler commands. Guarded worker snapshots again after locking.
# Absolute physical paths are required by prepare; reuse exactly its recorded values.
inputs=(--input "$attempt/plan.json")
for path in lean-toolchain lakefile.toml assurance/policy.json scripts/assumptions.py tools/Assurance.lean \
            scripts/proof-receipt.py tests/roadmap/proof-receipts/check.sh; do
  inputs+=(--input "$repo_root/$path")
done
inputs+=(--input "$guard")
outputs=()
for path in before.json audit.json after.json; do outputs+=(--output "$attempt/$path"); done
status=0
PATH="$toolchain/bin:$PATH" "$python" "$guard" \
  --cwd "$repo_root" --lock "$lock" --profile "$profile" --phase proof \
  --timeout 900 --rss-mib 8192 --log-bytes 1048576 \
  --report "$attempt/guard.json" --log "$attempt/guard.log" \
  "${inputs[@]}" "${outputs[@]}" --tool "$toolchain/bin/lean" --tool "$toolchain/bin/lake" \
  -- "$python" "$helper" worker "$attempt" || status=$?
if [ "$status" -ne 0 ]; then
  echo "proof receipt incomplete: guarded audit exited $status; retaining $attempt" >&2
  exit "$status"
fi
"$python" "$helper" seal "$attempt"
"$python" "$helper" verify "$attempt"
