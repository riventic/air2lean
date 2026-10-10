#!/usr/bin/env bash
# G2 (docs/c-frontend.md): pointer casts through `*anyopaque`/byte views and self-referential
# structs. Needs a built translator and `lake build ZigLean`; runs no compiler. The retained
# translation must equal the fresh one; `entry`-style #guards check every defined export against
# `native.txt` and every negative against its model outcome; `reject.zig`'s AIR must be rejected
# with the finite error-storage diagnostics. `--native` also reruns `native.zig` with a stock
# Zig 0.16.0 (AIR2LEAN_ZIG_NATIVE) and compares its output with `native.txt`.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/c-frontend/ptrcasts
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-ptrcasts.XXXXXX")
trap 'rm -rf "$work"' EXIT

"$translator" "$here/air/0.16.0" -o "$work/Gen.lean" --namespace PtrCasts --prefix ptrcasts.
cmp "$work/Gen.lean" "$here/PtrCasts/Gen.lean"

# Defined exports agree with native Zig; negatives give their model outcome on every input.
python3 - "$here/native.txt" "$work/Gen.lean" > "$work/Check.lean" <<'PY'
import sys
native, gen = sys.argv[1], sys.argv[2]
inputs = [(0, 0), (1, 2), (4294967295, 7), (305419896, 2863311530)]
# pointerAsInt reads a pointer's bytes as an integer: the address under the placement (MM-1),
# so it returns a placement-dependent value; it is checked to return.
negatives = {"byteAsBool": ".illegal",
             "misalignedChecked": ".panic", "misalignedUnchecked": ".illegal"}
out = [open(gen).read(), "namespace PtrCasts.Check",
       "def run (r : Zig.MemM (BitVec 32)) : Zig.Result (BitVec 32) := r.run' (PtrCasts.mem0 .fresh)",
       "def isOk (v : BitVec 32) (r : Zig.Result (BitVec 32)) : Bool :=",
       "  match r with | some (.ok x) => x == v | _ => false",
       "def isErr (e : Zig.Error) (r : Zig.Result (BitVec 32)) : Bool :=",
       "  match r with | some (.error x) => decide (x = e) | _ => false"]
seen = set()
for line in open(native).read().split("\n"):
    if not line:
        continue
    name, a, b, v = line.split()
    seen.add(name)
    out.append(f"#guard isOk {v}#32 (run (PtrCasts.{name} {a}#32 {b}#32))")
assert seen == {"listSum", "treeInsert", "voidRoundTrip", "byteView", "opaqueContext",
                "byteVectorCopy"}, seen
for a, b in inputs:
    out.append(f"#guard match run (PtrCasts.pointerAsInt {a}#32 {b}#32) with | some (.ok _) => true | _ => false")
for name, err in negatives.items():
    for a, b in inputs:
        out.append(f"#guard isErr {err} (run (PtrCasts.{name} {a}#32 {b}#32))")
out.append("end PtrCasts.Check")
print("\n".join(out))
PY
"${lean_cmd[@]}" "$work/Check.lean"

# Error storage cannot pass through `*anyopaque`; a cyclic error-bearing graph stays rejected.
"$translator" --diagnostics-json "$here/air-reject/0.16.0" --diagnostic-limit 64 > "$work/reject.json" || true
python3 - "$work/reject.json" <<'PY'
import json, sys
doc = json.load(open(sys.argv[1]))
assert doc.get("status") != "checked", "reject.zig was accepted"
got = {}
for d in doc.get("diagnostics", []):
    fn = d.get("function")
    fn = fn.get("name") if isinstance(fn, dict) else fn
    got[fn] = got.get(fn, "") + (d.get("message") or "")
want = {"reject.errorThroughOpaque": "a pointer cast exposing symbolic error storage",
        "reject.cyclicErrorView": "unresolved or cyclic symbolic storage provenance",
        "reject.wordVectorView": "a pointer cast between a vector and another pointee type"}
for fn, msg in want.items():
    assert msg in got.get(fn, ""), f"{fn}: expected '{msg}', got {got.get(fn)!r}"
print("ptrcasts rejections ok")
PY

if [ "${1:-}" = --native ]; then
  zig=${AIR2LEAN_ZIG_NATIVE:?set AIR2LEAN_ZIG_NATIVE to a stock Zig 0.16.0}
  (cd "$here" && "$zig" run -OReleaseSafe native.zig 2> "$work/native.txt")
  cmp "$work/native.txt" "$here/native.txt"
fi
echo "ptrcasts ok"
