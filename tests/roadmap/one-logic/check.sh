#!/usr/bin/env bash
# The one proof logic's library pieces on small library-only examples (docs/proof-framework.md):
# the strength harness (legacy statements from full-state ones), loops, the start memory, blocks.
# Every `*.lean` here is checked: each is a module of the fixture's library OneLogic (OneLogic/),
# and every theorem must use only the standard three axioms. The examples of `fsym` import only
# the umbrella `Full/AutoAll`, which must reach every rule of the library. Runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
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
# Every example is a module of the library OneLogic (tests/roadmap/lakefile.toml), built by Lake
# with what it imports; the axioms of every theorem, from the built environment (scripts/fixtures.py).
python3 -B scripts/fixtures.py build OneLogic
python3 -B scripts/fixtures.py audit --library OneLogic
echo "one-logic: ok"
