#!/usr/bin/env bash
# The one proof logic's library pieces on small library-only examples (docs/proof-framework.md):
# the strength harness (legacy statements from full-state ones), loops, the start memory. Needs
# `lake build ZigLean.Sep.Full.Strength ZigLean.Sep.Full.Loop ZigLean.Sep.Full.Init
# ZigLean.Sep.Full.Auto`; runs no compiler. Every theorem's axioms are the standard three.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/one-logic
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-one-logic.XXXXXX")
trap 'rm -rf "$work"' EXIT
for m in Strength Loop Init; do
  ns=$(grep -o '^namespace [^ ]*' "$here/$m.lean" | head -1 | cut -d' ' -f2)
  { cat "$here/$m.lean"; echo; grep -o '^theorem [^ :({\[]*' "$here/$m.lean" | while read -r _ t; do
      echo "#print axioms $ns.$t"; done; } > "$work/$m.lean"
  "${lean_cmd[@]}" "$work/$m.lean" > "$work/$m.txt" 2>&1 || { cat "$work/$m.txt" >&2; exit 1; }
  python3 - "$work/$m.txt" "$(grep -c '^theorem ' "$here/$m.lean")" <<'PY'
import re, sys
text, n = open(sys.argv[1]).read(), int(sys.argv[2])
groups = re.findall(r"depends on axioms: \[([^\]]*)\]|(does not depend on any axioms)", text)
used = {a.strip() for g, _ in groups for a in g.split(",") if a.strip()}
assert ": error" not in text and len(groups) == n, text
assert used <= {"propext", "Classical.choice", "Quot.sound"}, text
PY
  cat "$work/$m.txt"
done
echo "one-logic: ok"
