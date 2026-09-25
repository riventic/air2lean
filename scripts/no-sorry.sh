#!/usr/bin/env bash
# Fail if a proof uses `sorry`, `admit` or `native_decide`. Lean accepts `sorry` with only a
# warning, and `native_decide` adds the compiler to the trusted base.
#
# Usage: no-sorry.sh
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

# BSD grep with --include exits 1 (no match) for a missing dir, so check the dirs first.
for d in ZigLean Proofs; do
  [ -d "$d" ] || { echo "error: $d/ not found; nothing was checked" >&2; exit 1; }
done
# grep exits 0 on a match, 1 on no match, 2 on an error: only 1 passes.
status=0
grep -rnwE --include='*.lean' 'sorry|admit|native_decide' ZigLean Proofs || status=$?
case $status in
  0) echo "error: sorry/admit/native_decide found (see above)" >&2; exit 1 ;;
  1) echo "no sorry/admit/native_decide in ZigLean/ and Proofs/" ;;
  *) echo "error: grep failed (exit $status); nothing was checked" >&2; exit 1 ;;
esac
