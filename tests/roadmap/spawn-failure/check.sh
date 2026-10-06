#!/usr/bin/env bash
# Compiler entry point: run only from the exclusive qualification queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
[ "$#" -le 1 ] || { echo 'usage: check.sh --synthetic|--full' >&2; exit 2; }
exec python3 tests/roadmap/spawn-failure/qualify.py "${1:---synthetic}"
