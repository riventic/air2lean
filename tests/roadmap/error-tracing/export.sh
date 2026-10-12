#!/usr/bin/env bash
# L14: export error_tracing.zig with error return tracing (`-ferror-tracing`) by the patched
# compilers of every supported version into air/<version>, or with --check compare a fresh export
# byte for byte with the committed one. AIR2LEAN_ZIG_AIR: a directory holding
# zig-air-<version>/bin/zig (scripts/zig-air.sh builds them from this tree's zig-patch/). --check
# refuses a compiler whose hash differs from provenance.json. On macOS, 0.15.2/0.14.1 also need a
# failing `xcrun` shim first on PATH (zig-patch/README.md). After a re-export, run
# `python3 tests/roadmap/error-tracing/test_provenance.py --refresh`.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
here=tests/roadmap/error-tracing
root=${AIR2LEAN_ZIG_AIR:?set AIR2LEAN_ZIG_AIR to a directory of zig-air-<version> compilers}
mode=${1:-export}
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-error-tracing.XXXXXX")
trap 'rm -rf "$work"' EXIT
sha256() { shasum -a 256 "$1" | cut -d' ' -f1; }
# The roots and the std function every error return calls (`std.lang` in 0.17.0).
filter=error_tracing.bigRet,error_tracing.pass,error_tracing.traceIndex,error_tracing.traced
filter=$filter,error_tracing.handledTwice,builtin.returnError,lang.returnError
for version in 0.17.0 0.16.0 0.15.2 0.14.1; do
  if [ "$mode" = --check ]; then
    recorded=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["patched_compiler_sha256"][sys.argv[2]])' \
      "$here/provenance.json" "$version")
    actual=$(sha256 "$root/zig-air-$version/bin/zig-unlocked")
    [ "$recorded" = "$actual" ] || { echo "error: $root/zig-air-$version is not the recorded compiler" >&2; exit 1; }
  fi
  out="$work/$version"
  mkdir -p "$out"
  ZIG_AIR_JSON_DIR="$out" ZIG_AIR_JSON_FILTER="$filter" \
    "$root/zig-air-$version/bin/zig" build-obj -fno-emit-bin -OReleaseSafe -ferror-tracing \
    -target x86_64-linux -mcpu=baseline "$here/error_tracing.zig" --cache-dir "$work/cache-$version"
  if [ "$mode" = --check ]; then
    diff -r "$out" "$here/air/$version"
  else
    rm -rf "$here/air/$version"
    mkdir -p "$here/air"
    cp -R "$out" "$here/air/$version"
  fi
done
echo "error_tracing exports: $mode ok"
