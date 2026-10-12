#!/usr/bin/env bash
# L05: export nullpointers.zig (every root of `main`) and reject.zig with the patched compilers of
# every supported version (or the versions given) into air/<version> and air-reject/<version>, or
# with --check compare a fresh export byte for byte with the committed one. AIR2LEAN_ZIG_AIR: a directory holding
# zig-air-<version>/bin/zig (scripts/zig-air.sh builds them from this tree's zig-patch/). On macOS,
# 0.15.2/0.14.1 also need a failing `xcrun` shim first on PATH (zig-patch/README.md). After a
# re-export, run `python3 tests/roadmap/null-pointers/test_provenance.py --refresh`.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
here=tests/roadmap/null-pointers
root=${AIR2LEAN_ZIG_AIR:?set AIR2LEAN_ZIG_AIR to a directory of zig-air-<version> compilers}
mode=export
if [ "${1:-}" = --check ]; then mode=--check; shift; fi
# The versions to export (default: every supported version).
versions=${*:-0.17.0 0.16.0 0.15.2 0.14.1}
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-null-pointers.XXXXXX")
trap 'rm -rf "$work"' EXIT
roots="cNull allowzeroAddress allowzeroManyAddress castChecked cRead cZero storeLoad storedIsNull
  allowzeroStoreLoad nodeNext nodeVal nodeRoundTrip arrayItem cAdd cSub cIndex cElem nextPtr valPtr
  allowzeroNextPtr allowzeroAdd toOptional fromOptional addIsNull optIsNull optUnwrap optWrap optEq
  optStoreLoad optPayloadPtr optCIsNull optFromOrdinary boxPtr boxSet pairMake pairFirst errPtr
  errStore sliceAz arrayAz sliceC memsetAz memcpyAz memsetC parentFirst parentSecond mmioIsNull"
filter=$(printf 'nullpointers.%s,' $roots)
flags=(-fno-emit-bin -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline)
for version in $versions; do
  zig="$root/zig-air-$version/bin/zig"
  for kind in "air:nullpointers:${filter%,}" "air-reject:reject:reject."; do
    IFS=: read -r dir source names <<< "$kind"
    out="$work/$dir/$version"
    mkdir -p "$out"
    ZIG_AIR_JSON_DIR="$out" ZIG_AIR_JSON_FILTER="$names" "$zig" build-obj "${flags[@]}" \
      "$here/$source.zig" --cache-dir "$work/cache-$version"
    if [ "$mode" = --check ]; then
      diff -r "$out" "$here/$dir/$version"
    else
      rm -rf "$here/$dir/$version"
      mkdir -p "$here/$dir"
      cp -R "$out" "$here/$dir/$version"
    fi
  done
done
echo "null-pointer exports: $mode ok"
