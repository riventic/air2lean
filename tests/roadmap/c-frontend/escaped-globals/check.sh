#!/usr/bin/env bash
# G5 (docs/c-frontend.md): globals whose initial value is a comptime call and whose address
# escapes. Needs a built translator and `lake build ZigLean`; runs no compiler. Every committed
# AIR global carries its `init`; the retained translation must equal the fresh one; #guards
# check every export against `native.txt`. `--native` also reruns `native.zig` with a stock
# Zig 0.16.0 (AIR2LEAN_ZIG_NATIVE) and compares its output with `native.txt`.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/c-frontend/escaped-globals
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-escaped-globals.XXXXXX")
trap 'rm -rf "$work"' EXIT

python3 - "$here/air/0.16.0" <<'PY'
import json, sys
from pathlib import Path
seen = set()
for f in sorted(Path(sys.argv[1]).glob("*.json")):
    for g in json.loads(f.read_text()).get("globals", []):
        assert "init" in g, f"{f.name}: global {g.get('name')} has no init (G5)"
        seen.add(g.get("name"))
assert {"escaped.pool", "escaped.data", "escaped.counter"} <= seen, seen
PY

"$translator" "$here/air/0.16.0" -o "$work/Gen.lean" --namespace EscapedGlobals --prefix escaped.
cmp "$work/Gen.lean" "$here/EscapedGlobals/Gen.lean"

python3 - "$here/native.txt" "$work/Gen.lean" > "$work/Check.lean" <<'PY'
import sys
native, gen = sys.argv[1], sys.argv[2]
out = [open(gen).read(), "namespace EscapedGlobals.Check",
       "def run (r : Zig.MemM (BitVec 32)) : Zig.Result (BitVec 32) := r.run' EscapedGlobals.mem0",
       "def isOk (v : BitVec 32) (r : Zig.Result (BitVec 32)) : Bool :=",
       "  match r with | some (.ok x) => x == v | _ => false"]
seen = set()
for line in open(native).read().split("\n"):
    if line:
        name, a, b, v = line.split()
        seen.add(name)
        out.append(f"#guard isOk {v}#32 (run (EscapedGlobals.{name} {a}#32 {b}#32))")
assert seen == {"poolList", "dataAddr", "counterBump"}, seen
out.append("end EscapedGlobals.Check")
print("\n".join(out))
PY
"${lean_cmd[@]}" "$work/Check.lean"

if [ "${1:-}" = --native ]; then
  zig=${AIR2LEAN_ZIG_NATIVE:?set AIR2LEAN_ZIG_NATIVE to a stock Zig 0.16.0}
  (cd "$here" && "$zig" run -OReleaseSafe native.zig 2> "$work/native.txt")
  cmp "$work/native.txt" "$here/native.txt"
fi
echo "escaped-globals ok"
