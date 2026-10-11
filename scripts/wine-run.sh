#!/usr/bin/env bash
# Runs a Windows executable under Wine in a linux/amd64 container (Rosetta on Apple silicon), in
# the current directory: local evidence for pure computations only, never Windows OS evidence
# (docs/windows-target.md §Native evidence). The image is Dockerfile.wine's:
#   docker build --platform linux/amd64 -f Dockerfile.wine -t air2lean-wine:amd64 .
# Usage: wine-run.sh EXE [ARG...]   Env: AIR2LEAN_WINE_IMAGE (default air2lean-wine:amd64).
set -euo pipefail
[ "$#" -ge 1 ] || { echo "usage: wine-run.sh EXE [ARG...]" >&2; exit 2; }
image=${AIR2LEAN_WINE_IMAGE:-air2lean-wine:amd64}
exe_dir=$(cd -- "$(dirname -- "$1")" && pwd)
exe=$exe_dir/$(basename -- "$1")
shift
cwd=$(pwd)
docker image inspect "$image" >/dev/null 2>&1 || {
  echo "error: no Wine image $image; build it from Dockerfile.wine (see this script's header)" >&2
  exit 2
}
# The working directory and the executable's directory, at the same paths as on the host.
mounts=(-v "$cwd:$cwd")
case "$exe_dir/" in "$cwd"/*) ;; *) mounts+=(-v "$exe_dir:$exe_dir:ro") ;; esac
exec docker run --rm -i --platform linux/amd64 "${mounts[@]}" -w "$cwd" -e WINEDEBUG=-all \
  "$image" wine "$exe" "$@"
