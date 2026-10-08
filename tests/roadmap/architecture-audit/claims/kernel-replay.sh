#!/usr/bin/env bash
# Structural-fix probe for finding S1: replay fixture modules through the kernel with the
# toolchain's own `leanchecker`. Usage: kernel-replay.sh MODULE... (after build.sh).
# Exit 0 only if every module's declarations re-check.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
toolchain=$(dirname "$(dirname "$(elan which lean)")")
export LEAN_PATH="$repo_root/.lake/architecture-audit/claims/lib:$repo_root/.lake/build/lib/lean:$toolchain/lib/lean"
status=0
for module in "$@"; do
  if "$toolchain/bin/leanchecker" "$module"; then
    echo "kernel replay passed: $module"
  else
    echo "kernel replay FAILED: $module"
    status=1
  fi
done
exit $status
