#!/usr/bin/env bash
# ROOT/CI serialized existing Linux16 job: actual generated module required.
set -euo pipefail
: "${AIR2LEAN_GLOBAL_ACTUAL_GEN:?fresh source-bound actual Gen.lean}"
: "${AIR2LEAN_GLOBAL_CLIENT_OUT:?fresh retained client output directory}"
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
clients=tests/roadmap/global-payload-pointers
out=$AIR2LEAN_GLOBAL_CLIENT_OUT
test ! -e "$out"; mkdir -p "$out/baseline"
cp "$AIR2LEAN_GLOBAL_ACTUAL_GEN" "$out/baseline/Gen.lean"
lean_path=$(lake env printenv LEAN_PATH)
lake env lean -R "$out/baseline" -o "$out/baseline/Gen.olean" "$out/baseline/Gen.lean"
cp "$clients/GeneratedProofs.lean" "$out/baseline/GeneratedProofs.lean"
cp "$clients/GeneratedRuntime.lean" "$out/baseline/GeneratedRuntime.lean"
# Compiled and audited (axioms, sorry, kernel replay), not only elaborated: it is indexed (F2).
python3 -B scripts/theorem_universe.py gate "$out/baseline/GeneratedProofs.lean" --root "$out/baseline" \
  --lean-path "$out/baseline" --output-dir "$out/universe" > "$out/proofs.log" 2>&1
LEAN_PATH="$out/baseline:$lean_path" lake env lean -R "$out/baseline" --run "$out/baseline/GeneratedRuntime.lean" > "$out/runtime.log" 2>&1
python3 "$clients/generated-mutations.py" "$out/baseline/Gen.lean" "$out/mutants"
for name in control wrong_global missing_small_payload_offset forget_parent; do
 work=$out/mutants/$name
 lake env lean -R "$work" -o "$work/Gen.olean" "$work/Gen.lean" > "$work/definitions.log" 2>&1
 LEAN_PATH="$work:$lean_path" lake env lean -R "$work" "$work/Oracle.defs.lean" > "$work/oracle-definitions.log" 2>&1
 status=0
 LEAN_PATH="$work:$lean_path" lake env lean -R "$work" "$work/Oracle.lean" > "$work/oracle.log" 2>&1 || status=$?
 if test "$name" = control; then
  test "$status" = 0
 else
  python3 tests/roadmap/error-storage/classify_mutant.py "$status" "$work/Oracle.lean" "$work/oracle.log"
 fi
done
cmp "$AIR2LEAN_GLOBAL_ACTUAL_GEN" "$out/baseline/Gen.lean"
printf '%s\n' 'Actual generated alias/read/write/frame clients and three typed semantic mutants passed; stage2 qualified profile only.' > "$out/scope.txt"
touch "$out/passed"
