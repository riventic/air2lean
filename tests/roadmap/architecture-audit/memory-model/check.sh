#!/usr/bin/env bash
# Architecture audit 2/6 (memory model): reproduce the counterexamples of
# docs/architecture-audit/memory-model.md. Each fixture is exported to AIR (patched compiler,
# ReleaseSafe), translated, run in Lean from the generated `mem0`, and compared with the
# native ReleaseSafe build. The script asserts that the model and native results DIFFER as
# recorded (the findings are open). When a structural fix lands, the matching assertion
# fails and the fixture should be turned into an agreement test.
#
#   AIR2LEAN_AUDIT_ZIG_AIR=/opt/dev/air2lean-build/zig-air-0.16.0/bin/zig \
#   AIR2LEAN_AUDIT_ZIG_NATIVE=$HOME/.cache/air2lean/host-0.16.0/zig \
#     tests/roadmap/architecture-audit/memory-model/check.sh
# Manual fixture (not run here): memcpy_overlap.zig (control, model and native both panic).
# stack_depth.zig is an agreement test since MM-5 was fixed: under the 8 MiB budget of the
# native main thread the model overflows (`.stackOverflow`) where the native build dies.
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$here/../../../.." && pwd)
cd "$repo_root"
zig_air=${AIR2LEAN_AUDIT_ZIG_AIR:?set the patched AIR compiler (0.16.0)}
zig_native=${AIR2LEAN_AUDIT_ZIG_NATIVE:?set the stock native compiler (0.16.0)}
translator=${AIR2LEAN_AUDIT_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ "$("$zig_air" version)" = 0.16.0 ] || { echo 'AIR compiler is not 0.16.0' >&2; exit 1; }
[ "$("$zig_native" version)" = 0.16.0 ] || { echo 'native compiler is not 0.16.0' >&2; exit 1; }
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-audit-mem.XXXXXX")
trap 'rm -rf "$work"' EXIT

# export <module> <namespace> <runner>: AIR of every function but `main`, translation, Lean run.
lean_run() {
  local mod=$1 ns=$2 runner=$3
  mkdir -p "$work/air-$mod" "$work/in-$mod"
  ZIG_AIR_JSON_DIR="$work/air-$mod" ZIG_AIR_JSON_FILTER="$mod." \
    "$zig_air" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$here/$mod.zig" \
    --cache-dir "$work/air-cache" >/dev/null 2>&1 || true
  find "$work/air-$mod" -name '*.json' ! -name "$mod.main.json" -exec cp {} "$work/in-$mod/" \;
  "$translator" "$work/in-$mod" -o "$work/$mod.lean" --namespace "$ns" --prefix "$mod."
  cat "$here/$runner" >> "$work/$mod.lean"
  lake env lean --run "$work/$mod.lean" > "$work/$mod.lean.txt"
}
native_run() {
  local mod=$1
  "$zig_native" build-exe -OReleaseSafe -fno-error-tracing "$here/$mod.zig" \
    -femit-bin="$work/native-$mod" --cache-dir "$work/native-cache"
  "$work/native-$mod" > /dev/null 2> "$work/$mod.native.txt" || echo "exit $?" >> "$work/$mod.native.txt"
}
field() { awk -v k="$1" '$1 == k { $1 = ""; sub(/^ /, ""); print; exit }' "$2"; }

lake build ZigLean air2lean

lean_run memmodel MemModel Runner.lean
native_run memmodel
lean_run oob_ptr OobPtr OobRunner.lean
native_run oob_ptr

L=$work/memmodel.lean.txt N=$work/memmodel.native.txt
echo "--- model"; cat "$L"; echo "--- native"; grep -v '^ \|^/\|^???\|^\s*\^' "$N" || true
# MM-1: a fixed model address.
[ "$(field addrOfLocal "$L")" = 4096 ] || { echo 'MM-1: model address changed' >&2; exit 1; }
[ "$(field addrOfLocal "$N")" != 4096 ] || { echo 'MM-1: native address coincides' >&2; exit 1; }
# MM-4: structural `==` vs equal addresses (native: both true = 3).
[ "$(field eqVsAddr "$L")" = 1 ] && [ "$(field eqVsAddr "$N")" = 3 ] ||
  { echo 'MM-4 no longer diverges' >&2; exit 1; }
# MM-1: cross-block distance is the model's layout (1-byte gap), not the native frame.
[ "$(field crossDistance "$L")" = 9 ] && [ "$(field crossDistance "$N")" != 9 ] ||
  { echo 'MM-1 (distance) no longer diverges' >&2; exit 1; }
# MM-2: the over-aligning @alignCast passes in the model and panics natively.
[ "$(field overAlign "$L")" = 2 ] && grep -q 'panic: incorrect alignment' "$N" ||
  { echo 'MM-2 no longer diverges' >&2; exit 1; }

L=$work/oob_ptr.lean.txt N=$work/oob_ptr.native.txt
echo "--- model"; cat "$L"; echo "--- native"; cat "$N"
# MM-3: inbounds-GEP poison: native folds the comparison, the model compares addresses.
[ "$(field 'oobCompare(2^63)' "$L")" = 1 ] && [ "$(field 'oobCompare(2^63)' "$N")" = 0 ] ||
  { echo 'MM-3 no longer diverges' >&2; exit 1; }

lean_run stack_depth StackDepth StackRunner.lean
native_run stack_depth
L=$work/stack_depth.lean.txt N=$work/stack_depth.native.txt
echo "--- model"; cat "$L"; echo "--- native"; grep -v '^ \|^/\|^???\|^\s*\^' "$N" || true
# MM-5 (fixed): both overflow for depth(10^7); depth(1000) returns 1000 on both.
[ "$(field 'depth(1000)' "$L")" = 1000 ] && [ "$(field 'depth(1000,8MiB)' "$L")" = 1000 ] &&
  [ "$(field 'depth(10000000,8MiB)' "$L")" = 'error Zig.Error.stackOverflow' ] &&
  grep -q '^depth(1000) 1000$' "$N" && grep -q '^exit ' "$N" &&
  ! grep -q '^depth(10000000)' "$N" || { echo 'MM-5: model and native disagree on stack overflow' >&2; exit 1; }

# The model facts above are theorems (kernel + `native_decide`), and the emitter placeholders
# are successful no-ops in the logic (MM-6).
sed '/^-- Appended to the fresh/,$d' "$work/memmodel.lean" > "$work/thm.lean"
cat "$here/Theorems.lean" >> "$work/thm.lean"
lake env lean "$work/thm.lean"
lake env lean "$here/PanicDefault.lean"

echo "memory-model audit counterexamples reproduced (MM-1, MM-2, MM-3, MM-4, MM-6); MM-5 agrees"
