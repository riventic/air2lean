#!/usr/bin/env bash
# The general symbolic executor `fsym` (ZigLean/Sep/Full/Auto.lean, docs/proof-automation.md) on
# small library-only examples: the arithmetic solver and walks/returns. Its large user is the
# FixedBufferAllocator (tests/roadmap/alloc-fba/AllocFba/Full.lean). Needs
# `lake build ZigLean.Sep.Full.Auto`; runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/sep-auto
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-sep-auto.XXXXXX")
trap 'rm -rf "$work"' EXIT
for m in Arith Walk; do
  { cat "$here/$m.lean"; echo; grep -o '^theorem [^ :({\[]*' "$here/$m.lean" | while read -r _ t; do
      echo "#print axioms SepAuto.$m.$t"; done; } > "$work/$m.lean"
  "${lean_cmd[@]}" "$work/$m.lean" > "$work/$m.txt" 2>&1 || { cat "$work/$m.txt" >&2; exit 1; }
  python3 - "$work/$m.txt" "$(grep -c '^theorem ' "$here/$m.lean")" <<'PY'
import re, sys
text, n = open(sys.argv[1]).read(), int(sys.argv[2])
groups = re.findall(r"depends on axioms: \[([^\]]*)\]|(does not depend on any axioms)", text)
used = {a.strip() for g, _ in groups for a in g.split(",") if a.strip()}
assert ": error" not in text and len(groups) == n, text
assert used <= {"propext", "Classical.choice", "Quot.sound"}, text
PY
done
echo "sep-auto: ok"
