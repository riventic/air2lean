#!/usr/bin/env bash
# Check the original Flow production source, regenerate AIR/Lean, test boundaries,
# and kernel-check the generated definitions and their universal proofs.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"
check_proofs() {
  local proof_work=$1
  local status=0
  rg -n -w 'sorry|admit|native_decide|axiom' case-studies/flow-time/FlowTime || status=$?
  case "$status" in
    0) echo 'untrusted proof declaration in Flow case study' >&2; exit 1 ;;
    1) ;;
    *) echo "proof scan failed (exit $status)" >&2; exit 1 ;;
  esac
  lake build ZigLean
  lake env lean -R "$proof_work" -o "$proof_work/FlowTime/Gen.olean" "$proof_work/FlowTime/Gen.lean"
  LEAN_PATH="$proof_work${LEAN_PATH:+:$LEAN_PATH}" lake env lean -R case-studies/flow-time case-studies/flow-time/FlowTime/Proofs.lean
}
if [ "${1:-}" = --check-artifacts ] && [ "$#" = 1 ]; then
  python3 tests/roadmap/flow-time/test_compat.py
  work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-flow-time.XXXXXX")
  trap 'rm -rf "$work"' EXIT
  mkdir -p "$work/FlowTime"
  cp case-studies/flow-time/FlowTime/Gen.lean "$work/FlowTime/Gen.lean"
  python3 tests/roadmap/flow-time/compare-air.py case-studies/flow-time/air case-studies/flow-time/air
  check_proofs "$work"
  echo 'Flow committed generated definitions and universal proofs passed'
  exit 0
fi
source=${FLOW_TIME_SOURCE:-/opt/dev/boxhub/optimizer/engine/src/des/time.zig}
python3 case-studies/flow-time/check-source.py "$source"
if [ "${1:-}" = --check-source ] && [ "$#" = 1 ]; then exit 0; fi
if [ "$#" != 0 ]; then echo 'usage: flow-time.sh [--check-source|--check-artifacts]' >&2; exit 2; fi
: "${AIR2LEAN_ZIG_AIR:?set AIR2LEAN_ZIG_AIR to an existing patched Zig 0.16.0 compiler}"
: "${AIR2LEAN_ZIG_NATIVE:?set AIR2LEAN_ZIG_NATIVE to a stock Zig 0.16.0 compiler for host tests}"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$AIR2LEAN_ZIG_AIR" ] || { echo "compiler unavailable: $AIR2LEAN_ZIG_AIR" >&2; exit 1; }
[ -x "$AIR2LEAN_ZIG_NATIVE" ] || { echo "native compiler unavailable: $AIR2LEAN_ZIG_NATIVE" >&2; exit 1; }
[ -x "$translator" ] || { echo "translator unavailable: $translator" >&2; exit 1; }
[ "$("$AIR2LEAN_ZIG_NATIVE" version)" = 0.16.0 ] || { echo "native compiler must be Zig 0.16.0" >&2; exit 1; }
# Resolve external modules before changing directories or invoking the compiler.
source=$(python3 -c 'import pathlib,sys; print(pathlib.Path(sys.argv[1]).resolve())' "$source")
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-flow-time.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/air" "$work/FlowTime"
env ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER=flow_time. "$AIR2LEAN_ZIG_AIR" \
  build-obj -fno-emit-bin -fllvm -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline \
  --dep flow_time_original -Mroot=case-studies/flow-time/flow_time.zig \
  "-Mflow_time_original=$source"
python3 case-studies/flow-time/check-source.py "$source"
# Validate the exact fresh profile before translation or compatibility normalization.
python3 tests/roadmap/flow-time/compare-air.py case-studies/flow-time/air "$work/air" --validate-fresh
"$translator" "$work/air" -o "$work/FlowTime/Gen.lean" --namespace FlowTime --prefix flow_time. \
  --profile abi64-le-v1 --float-semantics ieee
python3 scripts/normalize-generated.py report "$work/FlowTime/Gen.lean" "$work/air" "$work/check-report.json"
python3 tests/roadmap/flow-time/compare-air.py case-studies/flow-time/air "$work/air" \
  --generated "$work/FlowTime/Gen.lean" --check-report "$work/check-report.json"
python3 scripts/normalize-generated.py compare case-studies/flow-time/FlowTime/Gen.lean \
  "$work/FlowTime/Gen.lean" "$work/check-report.json"
"$AIR2LEAN_ZIG_NATIVE" test -OReleaseSafe --dep flow_time_wrapper \
  -Mroot=tests/roadmap/flow-time/boundaries.zig --dep flow_time_original \
  -Mflow_time_wrapper=case-studies/flow-time/flow_time.zig "-Mflow_time_original=$source"
check_proofs "$work"
echo 'Flow original timestamp source, generated AIR/Lean, boundaries, and proofs passed'
