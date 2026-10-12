#!/usr/bin/env bash
# The one proof logic's library pieces on small library-only examples (docs/proof-framework.md):
# the strength harness (legacy statements from full-state ones), loops, the start memory, blocks.
# Every `*.lean` here is checked: it builds the library modules the examples import, then each
# example's theorems must use only the standard three axioms. The examples of `fsym` import only
# the umbrella `Full/AutoAll`, which must reach every rule of the library. Runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/one-logic
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-one-logic.XXXXXX")
trap 'rm -rf "$work"' EXIT
# The umbrella `Full/AutoAll` reaches every library module that declares an `fsym` rule.
python3 - <<'PY'
import re
from pathlib import Path
rule = re.compile(r"^\s*(?:@\[|attribute \[)[^\]]*\bfsym(?:_\w+)?\b", re.M)
imports = lambda p: re.findall(r"^import\s+(\S+)", p.read_text(), re.M)
seen, todo = set(), ["ZigLean.Sep.Full.AutoAll"]
while todo:
    m = todo.pop()
    p = Path(m.replace(".", "/") + ".lean")
    if m not in seen and p.exists():
        seen.add(m)
        todo += imports(p)
missing = sorted(str(p) for p in Path("ZigLean").rglob("*.lean")
                 if rule.search(p.read_text()) and str(p)[:-5].replace("/", ".") not in seen)
assert not missing, f"Full/AutoAll does not import the fsym rules of {missing}"
PY
# shellcheck disable=SC2046
lake build $(sed -n 's/^import \(ZigLean\.[^ ]*\)$/\1/p' "$here"/*.lean | sort -u)
for f in "$here"/*.lean; do
  m=$(basename "$f" .lean)
  ns=$(grep -o '^namespace [^ ]*' "$f" | head -1 | cut -d' ' -f2)
  { cat "$f"; echo; grep -o '^theorem [^ :({\[]*' "$f" | while read -r _ t; do
      echo "#print axioms $ns.$t"; done; } > "$work/$m.lean"
  "${lean_cmd[@]}" "$work/$m.lean" > "$work/$m.txt" 2>&1 || { cat "$work/$m.txt" >&2; exit 1; }
  python3 - "$work/$m.txt" "$(grep -c '^theorem ' "$f")" <<'PY'
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
