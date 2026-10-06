#!/usr/bin/env bash
# Shared default eligibility only. Explicit AIR2LEAN_EXAMPLES selections bypass this helper.
air2lean_default_examples() (
  local root=$1 version=$2 arch=$3 d
  cd "$root/examples" || exit 1
  for d in */; do
    [ -d "$d" ] || continue
    if [ "${d%/}" = asm ] && [ "$arch" != x86_64 ]; then continue; fi
    if [ -f "${d}zig-versions" ] && ! grep -qx "$version" "${d}zig-versions"; then continue; fi
    printf '%s ' "${d%/}"
  done
)
