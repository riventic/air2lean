#!/usr/bin/env bash
# Stores of `undefined` to locals: byte locals, dead stores. Needs a built
# translator and `lake build ZigLean`; runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-undef-locals.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/UndefLocals"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The retained translation is the fresh one, byte for byte.
"$translator" tests/roadmap/undef-locals/air/0.16.0 -o "$work/UndefLocals/Gen.lean" \
  --namespace UndefLocals --prefix undef_locals.
cmp "$work/UndefLocals/Gen.lean" tests/roadmap/undef-locals/UndefLocals/Gen.lean
"${lean_cmd[@]}" -R "$work" -o "$work/UndefLocals/Gen.olean" "$work/UndefLocals/Gen.lean"
"${lean_cmd[@]}" -R tests/roadmap/undef-locals tests/roadmap/undef-locals/UndefLocals/Proofs.lean
