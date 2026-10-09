#!/usr/bin/env bash
# E03 environment boundary gate: documentation checks, the hand-written Env client, the ENV-03
# registry translation of real std I/O (Zig 0.15.2 and 0.16.0) and the proofs about it.
# Run under scripts/build-guard.py. Build first: lake build ZigLean air2lean ZigLean.Env.Linux
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
here=tests/roadmap/env-boundaries
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-env-boundaries.XXXXXX")
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work:$repo/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"

python3 -B "$here/test_env_boundaries.py"
"${lean_cmd[@]}" "$here/WriteAll.lean"
"$here/translate.sh" "$work"
for ns in EnvStd15 EnvStd16; do
  "${lean_cmd[@]}" -R "$work" -o "$work/$ns/Gen.olean" "$work/$ns/Gen.lean"
done
"${lean_cmd[@]}" -R "$work" "$here/StdIo.lean"
echo "env-boundaries passed: contract client, ENV-03 bindings, translated std I/O and its proofs"
