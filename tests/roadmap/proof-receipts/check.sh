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
prepare_args=()
for module in "$@"; do prepare_args+=(--module "$module"); done
# A receipt from a tree with uncommitted tracked changes is refused unless explicitly allowed;
# the permission is recorded in the plan and the sealed receipt.
case "${AIR2LEAN_RECEIPT_ALLOW_DIRTY:-0}" in
  0) ;;
  1) prepare_args+=(--allow-dirty) ;;
  *) echo 'AIR2LEAN_RECEIPT_ALLOW_DIRTY must be 0 or 1' >&2; exit 2 ;;
esac
# Refuse to audit generated modules that are not fresh translations of their committed AIR
# (docs/generated-code.md); the guarded worker binds this script's identity as an input.
"$python" "$repo_root/scripts/gen-integrity.py" attest > /dev/null
"$python" "$helper" prepare "$attempt" --toolchain "$toolchain" --profile "$profile" --lock "$lock" ${prepare_args[@]+"${prepare_args[@]}"} --guard "$guard" ${guard_pin[@]+"${guard_pin[@]}"}
# Preparation has no compiler commands. Guarded worker snapshots again after locking.
# Absolute physical paths are required by prepare; reuse exactly its recorded values.
inputs=(--input "$attempt/plan.json")
for path in lean-toolchain lakefile.toml assurance/policy.json scripts/assumptions.py tools/Assurance.lean \
            scripts/proof-receipt.py tests/roadmap/proof-receipts/check.sh \
            assurance/float-semantics.json scripts/float-semantics.py scripts/gen-integrity.py \
            scripts/premise_markers.py; do
  inputs+=(--input "$repo_root/$path")
done
inputs+=(--input "$guard")
outputs=()
for path in before.json audit.json after.json; do outputs+=(--output "$attempt/$path"); done
status=0
PATH="$toolchain/bin:$PATH" "$python" "$guard" \
  --cwd "$repo_root" --lock "$lock" --profile "$profile" --phase proof \
  --timeout 900 --rss-mib 12288 --log-bytes 1048576 \
  --report "$attempt/guard.json" --log "$attempt/guard.log" \
  "${inputs[@]}" "${outputs[@]}" --tool "$toolchain/bin/lean" --tool "$toolchain/bin/lake" --tool "$toolchain/bin/leanchecker" \
  -- "$python" "$helper" worker "$attempt" || status=$?
if [ "$status" -ne 0 ]; then
  echo "proof receipt incomplete: guarded audit exited $status; retaining $attempt" >&2
  # Best-effort diagnostics cannot change the failed guard status or seal the attempt.
  "$python" - "$attempt/guard.log" <<'PYLOG' || true
import os, stat, sys
try:
    fd = os.open(sys.argv[1], os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        info = os.fstat(stream.fileno())
        if stat.S_ISREG(info.st_mode):
            stream.seek(max(0, info.st_size - 8192))
            sys.stderr.buffer.write(stream.read(8192))
except OSError:
    pass
PYLOG
  exit "$status"
fi
"$python" "$helper" seal "$attempt"
"$python" "$helper" verify "$attempt"
