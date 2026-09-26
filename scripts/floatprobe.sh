#!/usr/bin/env bash
# Float target probe: build+run tests/floatprobe/probe.zig and compare its output with
# tests/floatprobe/expected.txt. The expected file holds the results on the reference target
# (x86_64-linux, -mcpu=baseline; docs/floats.md). The float model follows these results, so a
# difference means that the target or the Zig version changed a case the model depends on.
#
# If tests/floatprobe/expected.<zig version>.txt exists, it overrides expected.txt line-by-line
# for a Zig version that legitimately changed one of these cases (keyed on the first two fields —
# type and case name — so an override only needs to list the differing lines).
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
  --dep compat -Mroot=tests/floatprobe/probe.zig -Mcompat=tests/diff/compat.zig
"$build_dir/probe" > "$build_dir/probe.out"

expected=tests/floatprobe/expected.txt
version=$("$zig_bin" version)
override="tests/floatprobe/expected.$version.txt"
if [[ -f "$override" ]]; then
  merged="$build_dir/expected.merged.txt"
  awk '
    NR == FNR { line[$1 " " $2] = $0; order[++n] = $1 " " $2; next }
    { line[$1 " " $2] = $0 }
    END { for (i = 1; i <= n; i++) print line[order[i]] }
  ' "$expected" "$override" >"$merged"
  expected="$merged"
fi

if ! diff -u "$expected" "$build_dir/probe.out"; then
  echo "error: float probe output differs from $expected (see above)" >&2
  exit 1
fi
echo "float probe: output equals $expected"
