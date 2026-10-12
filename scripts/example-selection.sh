#!/usr/bin/env bash
# Shared default eligibility only. Explicit AIR2LEAN_EXAMPLES selections bypass this helper.
# With AIR2LEAN_CHANGED_FROM=REF (local runs only), only the eligible examples that the changes
# since REF can affect (scripts/changed-examples.py).
air2lean_default_examples() (
  local root=$1 version=$2 arch=$3 d selected=''
  cd "$root/examples" || exit 1
  for d in */; do
    [ -d "$d" ] || continue
    if [ "${d%/}" = asm ] && [ "$arch" != x86_64 ]; then continue; fi
    if [ -f "${d}zig-versions" ] && ! grep -qx "$version" "${d}zig-versions"; then continue; fi
    selected="$selected${d%/} "
  done
  if [ -n "${AIR2LEAN_CHANGED_FROM:-}" ] && [ -n "$selected" ]; then
    # shellcheck disable=SC2086  # a space-separated list
    selected=$(python3 -B "$root/scripts/changed-examples.py" --base "$AIR2LEAN_CHANGED_FROM" $selected) || exit 1
    [ -z "$selected" ] || selected="$selected "
  fi
  printf '%s' "$selected"
)
