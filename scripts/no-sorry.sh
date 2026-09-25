#!/usr/bin/env bash
# Fail if a proof uses `sorry`, `admit` or `native_decide`. Lean accepts `sorry` with only a
# warning, and `native_decide` adds the compiler to the trusted base.
#
# Usage: no-sorry.sh
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

if grep -rnwE --include='*.lean' 'sorry|admit|native_decide' ZigLean Proofs; then
  echo "error: sorry/admit/native_decide found (see above)" >&2
  exit 1
fi
echo "no sorry/admit/native_decide in ZigLean/ and Proofs/"
