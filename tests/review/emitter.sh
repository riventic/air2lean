#!/usr/bin/env bash
# Called by the root's monitored validation queue. Never run compiler checks in parallel.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"
if [ "$#" -gt 1 ]; then echo 'usage: emitter.sh [OUTPUT_DIR]' >&2; exit 2; fi
if [ "$#" = 0 ]; then
  output=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-emitter.XXXXXX")
  trap 'rm -rf "$output"' EXIT
else
  output=$1
fi
lake env lean --run tests/review/Emitter.lean "$output"
# Preserve the caller's Parser outputs and check them in the same serial sequence.
while IFS= read -r source; do
  lake env lean "$source"
done < <(find "$output" -maxdepth 1 -type f -name '*.lean' | LC_ALL=C sort)
echo 'emitter regressions passed'
