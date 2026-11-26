#!/usr/bin/env bash
# The native witness of the `@mulAdd` lowering rule (witness.zig): x86_64-linux at
# `-mcpu=baseline` and `-mcpu=haswell`, compared with expected/<zig version>.txt.
#
#   native.sh --build DIR   cross-build both binaries with the stock Zig $AIR2LEAN_ZIG_NATIVE
#                           (any host; set AIR2LEAN_ROSETTA=1 when they will run under Rosetta)
#   native.sh --run DIR     run them on an x86_64-linux CPU with FMA and compare
#   native.sh DIR           both
#
# On the development Mac: `--build` on the host, `--run` in a `--platform linux/amd64` container
# (docs/rosetta.md). The Zig version is read from the compiler and recorded in DIR/version.
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$here/../../.." && pwd)
step=all
case "${1:-}" in --build|--run) step=${1#--}; shift ;; esac
[ "$#" -eq 1 ] || { echo 'usage: native.sh [--build|--run] DIR' >&2; exit 2; }
mkdir -p "$1"
dir=$(cd -- "$1" && pwd)
if [ "$step" != run ]; then
  : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig (0.14.1, 0.15.2, 0.16.0 or 0.17.1)}"
  # shellcheck source=/dev/null
  . "$repo_root/scripts/rosetta.sh"
  "$AIR2LEAN_ZIG_NATIVE" version > "$dir/version"
  for cpu in baseline haswell; do
    # shellcheck disable=SC2086
    "$AIR2LEAN_ZIG_NATIVE" build-exe -OReleaseSafe -target x86_64-linux "-mcpu=$cpu" \
      ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} "$here/witness.zig" "-femit-bin=$dir/witness-$cpu" \
      --cache-dir "$dir/zig-cache" --global-cache-dir "$dir/zig-global-cache"
  done
fi
if [ "$step" != build ]; then
  grep -qw fma /proc/cpuinfo || { echo 'native.sh: this CPU has no FMA; the haswell binary cannot run' >&2; exit 1; }
  version=$(cat "$dir/version")
  for cpu in baseline haswell; do
    echo "$cpu $("$dir/witness-$cpu" 2>&1)"
  done > "$dir/observed.txt"
  diff -u "$here/expected/$version.txt" "$dir/observed.txt"
  echo "mul-add-lowering native witness matches expected/$version.txt"
fi
