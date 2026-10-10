#!/usr/bin/env bash
# Export the analyzed 0.16.0 AIR of na.zig into $2 with the patched compiler $1.
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$2"
ZIG_AIR_JSON_DIR="$2" ZIG_AIR_JSON_FILTER="na." "$1" build-obj \
  -fno-emit-bin -OReleaseSafe -target x86_64-linux -mcpu=baseline -fno-error-tracing "$here/na.zig"
