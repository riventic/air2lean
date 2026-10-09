#!/usr/bin/env bash
# Tagged unions with a `noreturn` variant (B1): retained translation, client proofs against the
# 0.16.0 and 0.15.2 exports, and CLI rejections. Needs a built translator and
# `lake build ZigLean`; runs no compiler (README.md has the export and native commands).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/noreturn-variants
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-noreturn-variants.XXXXXX")
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
for version in 0.16.0 0.15.2; do
  out="$work/$version"
  mkdir -p "$out/NoreturnVariants"
  "$translator" "$here/air/$version" -o "$out/NoreturnVariants/Gen.lean" \
    --namespace NoreturnVariants --prefix noreturn_variants.
  # The retained translation is the fresh 0.16.0 one, byte for byte.
  if [ "$version" = 0.16.0 ]; then
    cmp "$out/NoreturnVariants/Gen.lean" "$here/NoreturnVariants/Gen.lean"
  fi
  LEAN_PATH="$out:$LEAN_PATH" "${lean_cmd[@]}" -R "$out" -o "$out/NoreturnVariants/Gen.olean" \
    "$out/NoreturnVariants/Gen.lean"
  LEAN_PATH="$out:$LEAN_PATH" "${lean_cmd[@]}" -R "$here" "$here/NoreturnVariants/Proofs.lean"
done
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
