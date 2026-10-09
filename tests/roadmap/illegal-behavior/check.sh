#!/usr/bin/env bash
# Illegal-behaviour gate (docs/illegal-behavior.md). Every compiler invocation runs sequentially.
#   - translates the retained 0.16.0 AIR of ib.zig (air/) and compares it with Gen.lean;
#   - translates each probe.zig function alone (probe-air/) and checks expected.json;
#   - runs Runtime.lean (runtime ops) and Cases.lean (generated functions) and the
#     emitter-output mutants of mutations.py, each of which Cases.lean must reject.
# Optional: AIR2LEAN_ZIG_AIR=patched-0.16/bin/zig re-exports the AIR and compares it with air/;
# AIR2LEAN_ZIG=stock 0.16.0 zig reruns native.zig in ReleaseSafe and ReleaseFast and compares
# its output with native/<mode>.txt.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/illegal-behavior
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-illegal.XXXXXX")
trap 'rm -rf "$work"' EXIT
lake build ZigLean Air2Lean air2lean

if [ -n "${AIR2LEAN_ZIG_AIR:-}" ]; then
  for src in ib probe; do
    dir=air; [ "$src" = probe ] && dir=probe-air
    mkdir "$work/$dir"
    ZIG_AIR_JSON_DIR="$work/$dir" ZIG_AIR_JSON_FILTER="$src." "$AIR2LEAN_ZIG_AIR" build-obj \
      -fno-emit-bin -OReleaseSafe -target x86_64-linux -mcpu=baseline -fno-error-tracing "$here/$src.zig"
    diff -r "$here/$dir" "$work/$dir"
  done
fi

lake exe air2lean "$here/air" -o "$work/Gen.lean" --namespace IllegalBehavior --prefix ib.
cmp "$work/Gen.lean" "$here/Gen.lean"
python3 -B "$here/probes.py" "$repo_root/.lake/build/bin/air2lean"

lake env lean --run "$here/Runtime.lean"
lake env lean -R "$work" -o "$work/Gen.olean" "$work/Gen.lean"
LEAN_PATH="$work:$(lake env printenv LEAN_PATH)" lake env lean -R "$work" --run "$here/Cases.lean"

python3 -B "$here/mutations.py" "$work/Gen.lean" "$work/mutants"
for dir in "$work"/mutants/*/; do
  name=$(basename "$dir")
  lake env lean -R "$dir" -o "$dir/Gen.olean" "$dir/Gen.lean"
  status=0
  LEAN_PATH="$dir:$(lake env printenv LEAN_PATH)" lake env lean -R "$dir" --run "$here/Cases.lean" \
    > "$dir/log" 2>&1 || status=$?
  if [ "$status" = 0 ] || ! grep -q '^uncaught exception: illegal-behavior case' "$dir/log"; then
    echo "mutant $name survived (status $status)" >&2; cat "$dir/log" >&2; exit 1
  fi
  echo "mutant $name killed"
done

if [ -n "${AIR2LEAN_ZIG:-}" ]; then
  [ "$("$AIR2LEAN_ZIG" version)" = 0.16.0 ] || { echo 'native.zig needs stock Zig 0.16.0' >&2; exit 1; }
  for mode in ReleaseSafe ReleaseFast; do
    "$AIR2LEAN_ZIG" build-exe "-O$mode" -mcpu=baseline -femit-bin="$work/native-$mode" \
      --dep ib -Mroot="$here/native.zig" -Mib="$here/ib.zig"
    "$work/native-$mode" 2> "$work/$mode.txt"
    cmp "$work/$mode.txt" "$here/native/$mode.txt"
  done
fi
python3 -B tests/roadmap/architecture-audit/trust-chain/check.py --require-fixed unchecked-memcpy
echo 'illegal-behavior passed'
