#!/usr/bin/env bash
# Print the path of the patched AIR-only compiler (bin/zig) for this checkout's zig-patch/ tree:
#
#   AIR2LEAN_ZIG_AIR=$(scripts/zig-air.sh 0.16.0)
#
# With AIR2LEAN_CAS_DIR set, the compiler comes from the shared content-addressed cache (built
# once per zig-patch input set and host, under scripts/build-guard.py, on a miss). Unset, it is
# <checkout>/zig-air-<version>, rebuilt when its recorded inputs differ from the checkout's.
# The stock Zig of that version bootstraps a build (scripts/cas.py). See docs/build-cache.md.
set -euo pipefail
[ $# = 1 ] || { echo "usage: scripts/zig-air.sh <version>" >&2; exit 2; }
exec python3 -B "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/cas.py" zig-air "$1"
