#!/usr/bin/env bash
# L14: export runtime_tags.zig with the patched compilers (0.16.0, 0.15.2, 0.14.1) into
# air/<version>, or with --check compare a fresh export byte for byte with the committed one.
# Needs zig-air-<version>/bin/zig under $AIR2LEAN_ZIG_AIR (default /opt/dev/air2lean-build). The
# committed exports come from compilers built by zig-patch/build.sh from this tree's exporter;
# an older install (no `src`/`column` fields) makes --check differ.
# on macOS 0.15.2/0.14.1 also a failing `xcrun` shim first on PATH (zig-patch/README.md).
# After a re-export, run `python3 tests/roadmap/runtime-tags/test_provenance.py --refresh`.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
here=tests/roadmap/runtime-tags
root=${AIR2LEAN_ZIG_AIR:-/opt/dev/air2lean-build}
mode=${1:-export}
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-runtime-tags.XXXXXX")
trap 'rm -rf "$work"' EXIT
for version in 0.16.0 0.15.2 0.14.1; do
  out="$work/$version"
  mkdir -p "$out"
  ZIG_AIR_JSON_DIR="$out" ZIG_AIR_JSON_FILTER=runtime_tags. \
    "$root/zig-air-$version/bin/zig" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
    -target x86_64-linux -mcpu=baseline "$here/runtime_tags.zig"
  if [ "$mode" = --check ]; then
    diff -r "$out" "$here/air/$version"
  else
    rm -rf "$here/air/$version"
    mkdir -p "$here/air"
    cp -R "$out" "$here/air/$version"
  fi
done
echo "runtime_tags exports: $mode ok"
