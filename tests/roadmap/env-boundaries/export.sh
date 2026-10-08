#!/usr/bin/env bash
# E03 std I/O fixtures: fresh AIR export with the patched 0.15.2 and 0.16.0 compilers.
# Compiler execution: run under scripts/build-guard.py.
# usage: export.sh [--update]   (default: compare with the committed air/)
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
here="$repo/tests/roadmap/env-boundaries"
: "${AIR2LEAN_ZIG_AIR_015:?set the patched Zig 0.15.2 compiler}"
: "${AIR2LEAN_ZIG_AIR_016:?set the patched Zig 0.16.0 compiler}"
mode=--check
[ "${1:-}" = --update ] && mode=
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-env-io.XXXXXX")
trap 'rm -rf "$work"' EXIT
export_one() { # zig source dir filter
  mkdir -p "$work/$3"
  (cd "$work" && ZIG_AIR_JSON_DIR="$work/$3" ZIG_AIR_JSON_FILTER="$4" "$1" build-obj -fno-emit-bin \
    -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline "$here/$2")
}
export_one "$AIR2LEAN_ZIG_AIR_015" std_io15.zig std15 'std_io15.,fs.File.,posix.,os.linux.'
export_one "$AIR2LEAN_ZIG_AIR_016" std_io16.zig std16 'std_io16.,posix.,os.linux.,Io.Threaded.closeFd,Io.Threaded.recoverableOsBugDetected'
python3 -B "$here/refresh-air.py" "$work/std15" "$here/air/std15" \
  std_io15.writeAllClose std_io15.readAllClose $mode
python3 -B "$here/refresh-air.py" "$work/std16" "$here/air/std16" std_io16.readClose $mode
echo "env-boundaries: fresh export matches air/ (${mode:-updated})"
