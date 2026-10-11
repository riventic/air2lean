#!/usr/bin/env bash
# Export loops.zig with a patched compiler (one with the I05 exporter change: `src`/`column`
# provenance) into <out>/<zig version>/. Runs only the supplied compiler, with -fno-emit-bin.
#   usage: export.sh <patched zig> <out>
set -euo pipefail
zig=${1:?usage: export.sh <patched zig> <out>}
out=${2:?usage: export.sh <patched zig> <out>}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
version=$("$zig" version)
air="$out/$version"
mkdir -p "$air"
cache=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-p08-cache.XXXXXX")
trap 'rm -rf "$cache"' EXIT
ZIG_AIR_JSON_DIR="$air" ZIG_AIR_JSON_FILTER=loops. \
  "$zig" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
  --cache-dir "$cache/local" --global-cache-dir "$cache/global" "$here/loops.zig"
ls "$air"/*.json >/dev/null
