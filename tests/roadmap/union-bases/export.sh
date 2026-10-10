#!/usr/bin/env bash
# Re-export air/<version> (and air-reject/<version>) from patched compilers built by
# zig-patch/build.sh from this tree's exporter, then print the hashes for provenance.json.
# usage: export.sh <version>=<patched zig> ...   (e.g. 0.16.0=/path/zig-air-0.16.0/bin/zig)
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$here"
[ $# -gt 0 ] || { echo 'usage: export.sh <version>=<patched zig> ...' >&2; exit 2; }
flags=(-fno-emit-bin -OReleaseSafe -fno-error-tracing -fno-llvm -fno-lld -target x86_64-linux-musl -mcpu=baseline)
for spec in "$@"; do
  version=${spec%%=*} zig=${spec#*=}
  for kind in air:union_bases air-reject:union_reject; do
    dir=${kind%%:*}/$version src=${kind#*:}
    rm -rf "$dir"
    mkdir -p "$dir"
    ZIG_AIR_JSON_DIR="$here/$dir" ZIG_AIR_JSON_FILTER="$src." "$zig" build-obj "${flags[@]}" "$src.zig"
  done
done
