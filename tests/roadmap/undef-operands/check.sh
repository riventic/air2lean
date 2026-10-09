#!/usr/bin/env bash
# Partly `undefined` constant operands: explicit undefined bytes or rejection. Needs a built
# translator and `lake build ZigLean`; runs no compiler.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-undef-operands.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/UndefOperands"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
# The retained translation is the fresh one, byte for byte.
"$translator" tests/roadmap/undef-operands/air/0.16.0 --profile legacy-abi64-le -o "$work/UndefOperands/Gen.lean" \
  --namespace UndefOperands --prefix undef_operands.
cmp "$work/UndefOperands/Gen.lean" tests/roadmap/undef-operands/UndefOperands/Gen.lean
"${lean_cmd[@]}" -R "$work" -o "$work/UndefOperands/Gen.olean" "$work/UndefOperands/Gen.lean"
"${lean_cmd[@]}" -R tests/roadmap/undef-operands tests/roadmap/undef-operands/UndefOperands/Proofs.lean
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/undef-operands/test_cli.py "$translator"
