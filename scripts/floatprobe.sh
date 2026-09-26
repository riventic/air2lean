#!/usr/bin/env bash
# Float target probe: build+run tests/floatprobe/probe.zig and compare its output with
# tests/floatprobe/expected.txt. The expected file holds the results on the reference target
# (x86_64-linux, -mcpu=baseline; docs/floats.md). The float model follows these results, so a
# difference means that the target or the Zig version changed a case the model depends on.
#
# Usage: floatprobe.sh
# Env:
#   AIR2LEAN_ZIG   Stock zig to build the probe. Default: zig (on PATH).
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

zig_bin=${AIR2LEAN_ZIG:-zig}
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-floatprobe.XXXXXX")
trap 'rm -rf "$build_dir"' EXIT

"$zig_bin" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$build_dir/probe" \
  tests/floatprobe/probe.zig
"$build_dir/probe" > "$build_dir/probe.out"

if ! diff -u tests/floatprobe/expected.txt "$build_dir/probe.out"; then
  echo "error: float probe output differs from tests/floatprobe/expected.txt (see above)" >&2
  exit 1
fi
echo "float probe: output equals tests/floatprobe/expected.txt"
