#!/usr/bin/env bash
# L10: export error_width.zig with the patched compilers (0.16.0, 0.15.2, 0.14.1) at several
# `--error-limit` values into air-fresh/<version>/bits<N>, or with --check compare a fresh
# export byte for byte with the committed one.
#
# The compilers must be built by zig-patch/build.sh from the zig-patch tree of this checkout;
# provenance.json records the hash of each compiler binary (bin/zig-unlocked behind the AIR-only
# lock wrapper). Point AIR2LEAN_ZIG_AIR at a directory holding zig-air-<version>/bin/zig for the
# three versions (default /opt/dev/air2lean-build, which may hold older builds). --check refuses a
# compiler whose hash differs from the record. On macOS 0.15.2 and 0.14.1 also need a failing
# `xcrun` shim first on PATH (zig-patch/README.md).
# After a re-export, run `python3 tests/roadmap/error-width/test_provenance.py --refresh`.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
here=tests/roadmap/error-width
root=${AIR2LEAN_ZIG_AIR:-/opt/dev/air2lean-build}
mode=${1:-export}
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-error-width.XXXXXX")
trap 'rm -rf "$work"' EXIT
sha256() { shasum -a 256 "$1" | cut -d' ' -f1; }
# Width -> --error-limit (the width is bit_length(limit)); 16 is the default and gets no flag.
limit_for() {
  case $1 in
    2) echo 3 ;;
    8) echo 255 ;;
    10) echo 1000 ;;
    16) echo default ;;
    17) echo 100000 ;;
    32) echo 4294967295 ;;
    *) echo "bad width $1" >&2; exit 1 ;;
  esac
}
for version in 0.16.0 0.15.2 0.14.1; do
  if [ "$mode" = --check ]; then
    recorded=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["patched_compiler_sha256"][sys.argv[2]])' \
      "$here/provenance.json" "$version")
    actual=$(sha256 "$root/zig-air-$version/bin/zig-unlocked")
    [ "$recorded" = "$actual" ] || {
      echo "error: $root/zig-air-$version is not the recorded compiler ($actual, expected $recorded);" \
        "build one with zig-patch/build.sh and set AIR2LEAN_ZIG_AIR" >&2
      exit 1
    }
  fi
  for bits in 2 8 10 16 17 32; do
    limit=$(limit_for "$bits")
    flags=()
    [ "$limit" = default ] || flags=(--error-limit "$limit")
    out="$work/$version/bits$bits"
    mkdir -p "$out"
    ZIG_AIR_JSON_DIR="$out" ZIG_AIR_JSON_FILTER=error_width. \
      "$root/zig-air-$version/bin/zig" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline ${flags[@]+"${flags[@]}"} "$here/error_width.zig"
    if [ "$mode" = --check ]; then
      diff -r "$out" "$here/air-fresh/$version/bits$bits"
    else
      rm -rf "$here/air-fresh/$version/bits$bits"
      mkdir -p "$here/air-fresh/$version"
      cp -R "$out" "$here/air-fresh/$version/bits$bits"
    fi
  done
done
echo "error_width exports: $mode ok"
