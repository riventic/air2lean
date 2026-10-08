#!/usr/bin/env bash
# Export fixture.zig with a patched compiler into <out>/<zig version>/ for test_cli.py
# --export-air <out>. Runs only the supplied compiler, with -fno-emit-bin.
#   usage: export.sh <patched zig> <out>
set -euo pipefail
zig=${1:?usage: export.sh <patched zig> <out>}
out=${2:?usage: export.sh <patched zig> <out>}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
version=$("$zig" version)
air="$out/$version"
mkdir -p "$air"
cache=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-i05-cache.XXXXXX")
trap 'rm -rf "$cache"' EXIT
ZIG_AIR_JSON_DIR="$air" \
ZIG_AIR_JSON_FILTER=fixture.volatileTwice,fixture.unorderedLoad,fixture.callsMissing \
  "$zig" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
  --cache-dir "$cache/local" --global-cache-dir "$cache/global" "$here/fixture.zig"
ls "$air"/*.json >/dev/null
