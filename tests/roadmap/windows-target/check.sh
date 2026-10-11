#!/usr/bin/env bash
# x86_64-windows-gnu fail-closed rules (docs/windows-target.md). Needs a built translator; runs no
# compiler: air/<case>/ are the recorded Zig 0.17.0 exports of src/<case>.zig for
# x86_64-windows-gnu (patched compiler, -OReleaseSafe -fno-error-tracing -mcpu=baseline).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
exec python3 tests/roadmap/windows-target/test_rules.py "$translator"
