#!/usr/bin/env bash
# Rosetta support, sourced (docs/rosetta.md): the one place that knows how Rosetta for Linux
# (Docker Desktop on Apple silicon, `--platform linux/amd64`) differs from a real x86_64 Linux.
#
# Rosetta refuses an ELF with an empty PT_LOAD segment ("rosetta error: bss_size overflow"), which
# LLD emits for the empty RELRO of most release-mode builds and of the JIT-compiled `zig build`
# runner of Zig 0.17 (`maker`). Two mechanisms, both no-ops on a real x86_64 Linux:
#
#   AIR2LEAN_ROSETTA_LINK_FLAGS   exported here under Rosetta, else unset/empty: extra `zig build-exe`
#       flags (`-z norelro`) for every x86_64-linux binary a script builds and runs. Scripts append
#       ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} to their build-exe command line and know nothing else.
#   air2lean_rosetta_run CMD...   runs CMD; when CMD (a `zig build`) died on a binary it JIT-built
#       itself, patches the empty segment out of the executables in Zig's caches
#       (scripts/rosetta-elf.py) and runs CMD again.
#
# Detection: Rosetta reports the CPU vendor "VirtualApple" in /proc/cpuinfo. AIR2LEAN_ROSETTA=1/0
# forces it: scripts/build-mode-docker.sh cross-builds the x86_64-linux harness on the Mac, for a
# Docker that may run it under Rosetta, and sets 1.
air2lean_under_rosetta() {
  case "${AIR2LEAN_ROSETTA:-}" in
    1) return 0 ;;
    0) return 1 ;;
  esac
  grep -qs VirtualApple /proc/cpuinfo
}

if air2lean_under_rosetta; then
  export AIR2LEAN_ROSETTA_LINK_FLAGS=${AIR2LEAN_ROSETTA_LINK_FLAGS-'-z norelro'}
else
  unset AIR2LEAN_ROSETTA_LINK_FLAGS
fi

air2lean_rosetta_run() {
  if ! air2lean_under_rosetta; then "$@"; return; fi
  local here log status fixed tries=0
  here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
  log=$(mktemp "${TMPDIR:-/tmp}/air2lean-rosetta.XXXXXX")
  while :; do
    if "$@" 2>"$log"; then status=0; else status=$?; fi
    cat "$log" >&2
    if [ "$status" = 0 ] || ! grep -q 'bss_size overflow' "$log" || [ "$tries" -ge 8 ]; then break; fi
    tries=$((tries + 1))
    # The caches of the failed command: Zig's global cache and the project cache in the cwd.
    fixed=$(python3 -I "$here/rosetta-elf.py" "${ZIG_GLOBAL_CACHE_DIR:-$HOME/.cache/zig}/o" \
      "${ZIG_LOCAL_CACHE_DIR:-.zig-cache}/o" 2>&2)
    echo "rosetta: patched $fixed executables in Zig's caches, running again ($tries)" >&2
    [ "$fixed" -gt 0 ] || break
  done
  rm -f "$log"
  return "$status"
}
