#!/usr/bin/env bash
# Compiler/Lean commands run only in the root's exclusive validation lane.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case "${1:-}" in
  --kernel)
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig}"
    : "${AIR2LEAN_LEAN:?set Lean with built ZigLean in LEAN_PATH}"
    "$AIR2LEAN_ZIG_NATIVE" test zig-patch/air-json/pointer-offset.zig -OReleaseSafe
    "$AIR2LEAN_LEAN" --run tests/roadmap/global-payload-pointers/Model.lean
    work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/payload-mutants.XXXXXX")
    trap 'rm -rf "$work"' EXIT
    for name in forget-parent forget-payload wrap-offset unbounded; do
      python3 tests/roadmap/global-payload-pointers/mutations.py create "$name" \
        zig-patch/air-json/pointer-offset.zig "$work/$name.zig"
      # Compilation must succeed before the executable's assertion failure is evaluated.
      "$AIR2LEAN_ZIG_NATIVE" test "$work/$name.zig" --test-no-exec -OReleaseSafe -femit-bin="$work/$name"
      status=0
      "$work/$name" >"$work/$name.log" 2>&1 || status=$?
      if ! python3 tests/roadmap/global-payload-pointers/mutations.py classify \
          "$name" "$status" "$work/$name.log"; then
        cat "$work/$name.log" >&2; exit 1
      fi
    done
    ;;
  --native)
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig}"
    "$AIR2LEAN_ZIG_NATIVE" test tests/roadmap/global-payload-pointers/global_payloads.zig -OReleaseSafe \
      -fno-llvm -fno-lld -target x86_64-linux -mcpu=baseline
    ;;
  --export|--export-reject)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --export EMPTY_OUTPUT_DIR|--export-reject EMPTY_OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a freshly patched compiler with this exporter}"
    : "${AIR2LEAN_ZIG_VERSION:?set the exact patched compiler version}"
    : "${AIR2LEAN_ZIG_BACKEND:?set the exact expected stage2 backend}"
    [ "$AIR2LEAN_ZIG_BACKEND" = stage2_x86_64 ] || { echo 'payload qualification requires stage2_x86_64' >&2; exit 2; }
    mkdir -p "$2"
    [ -z "$(find "$2" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo 'output must be empty' >&2; exit 1; }
    air_output=$(cd -- "$2" && pwd)
    fixture=global_payloads
    check_args=()
    if [ "$1" = --export-reject ]; then fixture=reject; check_args=(--reject); fi
    ZIG_AIR_JSON_DIR="$air_output" ZIG_AIR_JSON_FILTER="$fixture." \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline "tests/roadmap/global-payload-pointers/$fixture.zig"
    python3 tests/roadmap/global-payload-pointers/check-export.py "$air_output" \
      --version "$AIR2LEAN_ZIG_VERSION" --backend "$AIR2LEAN_ZIG_BACKEND" "${check_args[@]}"
    ;;
  *) echo 'usage: check.sh --kernel|--native|--export EMPTY_OUTPUT_DIR|--export-reject EMPTY_OUTPUT_DIR' >&2; exit 2 ;;
esac
