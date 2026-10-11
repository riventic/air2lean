#!/usr/bin/env bash
# L12: explicit external initial state and absent-initializer rejection. Needs a built
# translator and `lake build ZigLean.Sep`; runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-global-init.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/GlobalInit"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The retained translation is the fresh one, byte for byte.
"$translator" tests/roadmap/global-init/air/0.16.0 --profile legacy-abi64-le -o "$work/GlobalInit/Gen.lean" \
  --namespace GlobalInit --prefix global_init.
cmp "$work/GlobalInit/Gen.lean" tests/roadmap/global-init/GlobalInit/Gen.lean
"${lean_cmd[@]}" -R "$work" -o "$work/GlobalInit/Gen.olean" "$work/GlobalInit/Gen.lean"
"${lean_cmd[@]}" -R tests/roadmap/global-init tests/roadmap/global-init/GlobalInit/Proofs.lean
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/global-init/test_cli.py "$translator"
