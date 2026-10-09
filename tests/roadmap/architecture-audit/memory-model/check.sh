#!/usr/bin/env bash
# Architecture audit 2/6 (memory model): reproduce the counterexamples of
# docs/architecture-audit/memory-model.md. Each fixture is exported to AIR (patched compiler,
# ReleaseSafe), translated, run in Lean from the generated `mem0 σ` under several placements,
# and compared with the native ReleaseSafe build. MM-1, MM-2 and MM-4 are fixed by the
# placement oracle (docs/address-placement.md): the script asserts agreement with native, or
# that the result depends on the placement (Theorems.lean: the old statements are not
# provable for every placement). MM-3 and MM-6 are still open: their divergence is asserted.
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
fail() { echo "$1" >&2; exit 1; }
# MM-1 (fixed): the address of a local is the placement's (Zig.Placement), not a constant.
[ "$(field addrOfLocal "$L")" = 4096 ] && [ "$(field addrOfLocal@high "$L")" = 1099511627776 ] ||
  fail 'MM-1: the model address does not follow the placement'
[ "$(field addrOfLocal "$N")" != 4096 ] || fail 'MM-1: native address coincides'
# MM-4 (fixed): `==` compares addresses, so the model agrees with native (3) under placements.
[ "$(field eqVsAddr "$L")" = 3 ] && [ "$(field eqVsAddr@adjacent "$L")" = 3 ] &&
  [ "$(field eqVsAddr "$N")" = 3 ] || fail 'MM-4: pointer == disagrees with native'
# MM-1 (fixed): distance and order of two locals follow the placement; the native frame's
# adjacent layout (distance 8) is one of the placements.
[ "$(field crossDistance@adjacent "$L")" = "$(field crossDistance "$N")" ] ||
  fail 'MM-1: the adjacent placement does not give the native distance'
[ "$(field crossDistance "$L")" = 9 ] && [ "$(field crossOrder "$L")" = 1 ] &&
  [ "$(field crossOrder@swapped "$L")" = 0 ] || fail 'MM-1: order/distance not placement-dependent'
# MM-2 (fixed): the over-aligning @alignCast panics under a placement without the extra
# alignment, as natively; it passes only where the placement happens to give it.
grep -q 'panic: incorrect alignment' "$N" || fail 'MM-2: native no longer panics'
case "$(field overAlign@misaligned "$L")" in error*) ;; *) fail 'MM-2: misaligned placement does not panic';; esac

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

# Kernel checks (no `native_decide`): the old address theorems are not provable for every
# placement (addrOfLocal = 4096, crossDistance = 9, overAlign never panics), and the emitter
# placeholders are successful no-ops in the logic (MM-6, open).
sed '/^-- Appended to the fresh/,$d' "$work/memmodel.lean" > "$work/thm.lean"
cat "$here/Theorems.lean" >> "$work/thm.lean"
lake env lean "$work/thm.lean"
lake env lean "$here/PanicDefault.lean"

echo "memory-model audit: MM-1, MM-2, MM-4 fixed (placement oracle), MM-5 agrees (stack budget); MM-3, MM-6 reproduced"
