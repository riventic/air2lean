#!/usr/bin/env bash
# L09 element-stride vector layout (tests/roadmap/vector-layouts/README.md §Element stride).
# Needs `lake build ZigLean.VecStride`.
#
#   strided.sh [--native]
#
# The model's lines (ModelStrided.lean) equal the recorded probe output
# (stage2-x86_64-linux.txt). `--native` also builds probe_strided.zig with the self-hosted
# x86_64 backend of each stock Zig compiler that is set (AIR2LEAN_ZIG_NATIVE_<major>_<minor>, for
# example AIR2LEAN_ZIG_NATIVE_0_16, or AIR2LEAN_ZIG_NATIVE for one compiler of any version), in
# Debug and ReleaseSafe, runs it (an x86_64-linux host, or a linux/amd64 container) and requires
# the recorded output byte for byte.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/vector-layouts
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
"${lean_cmd[@]}" --run "$here/ModelStrided.lean" "$here/stage2-x86_64-linux.txt"
if [ "${1:-}" = --native ]; then
  # shellcheck source=scripts/rosetta.sh
  source scripts/rosetta.sh
  work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-vector-strided.XXXXXX")
  trap 'rm -rf "$work"' EXIT
  ran=0
  for var in AIR2LEAN_ZIG_NATIVE AIR2LEAN_ZIG_NATIVE_0_17 AIR2LEAN_ZIG_NATIVE_0_16 \
      AIR2LEAN_ZIG_NATIVE_0_15 AIR2LEAN_ZIG_NATIVE_0_14; do
    zig=${!var:-}
    [ -n "$zig" ] || continue
    for mode in Debug ReleaseSafe; do
      # shellcheck disable=SC2086 # the Rosetta link flags (scripts/rosetta.sh) are whitespace-separated
      "$zig" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} -fno-llvm -fno-lld -O"$mode" \
        -target x86_64-linux -mcpu=baseline "$here/probe_strided.zig" \
        -femit-bin="$work/probe-$var-$mode"
      "$work/probe-$var-$mode" 2> "$work/$var-$mode.txt"
      cmp "$work/$var-$mode.txt" "$here/stage2-x86_64-linux.txt"
      ran=1
    done
  done
  [ "$ran" = 1 ] || { echo "error: --native needs AIR2LEAN_ZIG_NATIVE or AIR2LEAN_ZIG_NATIVE_<major>_<minor>" >&2; exit 1; }
fi
echo "vector-layouts strided: ok"
