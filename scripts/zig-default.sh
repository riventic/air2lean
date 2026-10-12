#!/usr/bin/env bash
# The default Zig version, read from compatibility.json (`zig.default`) through scripts/compat.py.
# Source this file, or run it (prints the version). Nothing else may spell the default.
#   . "$repo_root/scripts/zig-default.sh"
#   zig_version=${AIR2LEAN_ZIG_VERSION:-$(air2lean_default_zig_version "$repo_root")}
# A script that tests one particular version says so with a plain assignment (`version=0.16.0`);
# scripts/version-literals.py rejects a version literal in a defaulting position (`${V:-0.16.0}`).
air2lean_default_zig_version() {
  python3 "$1/scripts/compat.py" default --root "$1"
}
if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  air2lean_default_zig_version "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
fi
