#!/usr/bin/env bash
# Full air2lean pipeline for examples/basic/basic.zig:
#   1. dump AIR-JSON with the patched compiler (zig-patch/) and check it against the golden files
#   2. translate that AIR to Lean (`lake exe air2lean`)
#   3. build the generated Lean
#   4. differential-test it against the real Zig behaviour (scripts/diff.sh)
#
# Usage: check.sh
# Env:
#   AIR2LEAN_ZIG_VERSION  Zig version: selects the golden dir and the default patched zig. Default: 0.15.2
#   AIR2LEAN_ZIG_AIR      Patched zig (zig-patch/build.sh output). Default: zig-air-$AIR2LEAN_ZIG_VERSION/bin/zig
#   AIR2LEAN_CI           If 1: fail when the committed Gen.lean differs from the new translator output.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

zig_version=${AIR2LEAN_ZIG_VERSION:-0.15.2}
zig_air=${AIR2LEAN_ZIG_AIR:-zig-air-$zig_version/bin/zig}
[ -x "$zig_air" ] || {
  echo "error: patched zig not found/executable at $zig_air" >&2
  echo "hint: build one with zig-patch/build.sh $zig_version (see zig-patch/README.md)" >&2
  exit 1
}

golden_dir="tests/golden/$zig_version/air"
air_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-check.XXXXXX")
trap 'rm -rf "$air_dir"' EXIT

echo "== dumping AIR ==" >&2
ZIG_AIR_JSON_DIR="$air_dir" ZIG_AIR_JSON_FILTER=basic. "$zig_air" \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing examples/basic/basic.zig

echo "== checking against golden ($golden_dir) ==" >&2
diff_output=$(diff -r "$golden_dir" "$air_dir" || true)
if [ -n "$diff_output" ]; then
  echo "error: AIR output does not match $golden_dir" >&2
  echo "$diff_output" >&2
  echo "hint: if only the golden files are stale (a deliberate exporter change), regenerate: cp $air_dir/* $golden_dir/" >&2
  exit 1
fi

echo "== translating to Lean ==" >&2
lake exe air2lean "$air_dir" -o Proofs/Basic/Gen.lean --namespace Basic --prefix basic.

if [ "${AIR2LEAN_CI:-0}" = 1 ] && ! git diff --exit-code -- Proofs/Basic/Gen.lean; then
  echo "error: committed Proofs/Basic/Gen.lean differs from the translator output; commit the new file" >&2
  exit 1
fi

echo "== building Lean ==" >&2
lake build

echo "== differential testing ==" >&2
exec scripts/diff.sh
