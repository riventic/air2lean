#!/usr/bin/env bash
# L06: export const_bases.zig on stage2_x86_64 into air-fresh/<version> and llvm_correspondence.zig
# on the LLVM backend into air-llvm/<version>, with the patched compilers of every supported version
# (or the versions given); --check compares a fresh export byte for byte with the committed one.
# AIR2LEAN_ZIG_AIR: a directory holding zig-air-<version>/bin/zig (scripts/zig-air.sh builds them
# from this tree's zig-patch/). On macOS, 0.15.2/0.14.1 also need a failing `xcrun` shim first on
# PATH (zig-patch/README.md). After a re-export, run `python3 test_cli.py --refresh-provenance`.
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=${AIR2LEAN_ZIG_AIR:?set AIR2LEAN_ZIG_AIR to a directory of zig-air-<version> compilers}
mode=export
if [ "${1:-}" = --check ]; then mode=--check; shift; fi
versions=${*:-0.17.0 0.16.0 0.15.2 0.14.1}
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-const-bases.XXXXXX")
trap 'rm -rf "$work"' EXIT
common=(-fno-emit-bin -OReleaseSafe -fno-error-tracing -target x86_64-linux-musl -mcpu=baseline)
for version in $versions; do
  for kind in "air-fresh:const_bases:-fno-llvm -fno-lld" "air-llvm:llvm_correspondence:-fllvm"; do
    IFS=: read -r dir source backend <<< "$kind"
    out="$work/$dir/$version"
    mkdir -p "$out"
    # shellcheck disable=SC2086 # the backend flags are words
    ZIG_AIR_JSON_DIR="$out" ZIG_AIR_JSON_FILTER="$source." "$root/zig-air-$version/bin/zig" build-obj \
      "${common[@]}" $backend "$here/$source.zig" --cache-dir "$work/cache-$version"
    if [ "$mode" = --check ]; then
      diff -r "$out" "$here/$dir/$version"
    else
      rm -rf "${here:?}/$dir/$version"
      mkdir -p "$here/$dir"
      cp -R "$out" "$here/$dir/$version"
    fi
  done
done
echo "const-bases exports: $mode ok"
