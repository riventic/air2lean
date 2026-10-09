#!/usr/bin/env bash
# Fail if a theorem-universe source uses `sorry`, `admit` or `native_decide`, or a kernel escape
# hatch (`debug.skipKernelTC`, `set_option debug.*`; environment edits, `unsafe`, `extern` and
# `implemented_by` outside assurance/kernel-escapes.json). Lean accepts `sorry` with only a
# warning, and `native_decide` adds the compiler to the trusted base. The universe is ZigLean/,
# Proofs/ and every module docs/premise-index.md indexes (scripts/theorem_universe.py). This is
# defense in depth: the compiled audit (`theorem_universe.py audit`) is authoritative.
#
# Usage: no-sorry.sh
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
exec python3 -B "$repo_root/scripts/theorem_universe.py" scan
