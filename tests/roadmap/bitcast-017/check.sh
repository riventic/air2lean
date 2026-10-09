#!/usr/bin/env bash
# Zig 0.17.0 logical-order @bitCast gate (docs/bitcast-semantics.md). Run in the serialized queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/bitcast-017
case "${1:---check}" in
  --native)
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig 0.17.0}"
    "$AIR2LEAN_ZIG_NATIVE" test "$dir/bitcast017.zig" -OReleaseSafe
    exit ;;
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a patched Zig 0.17.0 with the AIR exporter}"
    mkdir -p "$2"
    air_output=$(cd -- "$2" && pwd)
    ZIG_AIR_JSON_DIR="$air_output" ZIG_AIR_JSON_FILTER=bitcast017. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline "$dir/bitcast017.zig"
    exit ;;
  --check) ;;
  *) echo 'usage: check.sh [--check|--native|--export OUTPUT_DIR]' >&2; exit 2 ;;
esac
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build translator first' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-bitcast017.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/BitCastReal"
"$translator" "$dir/air/0.17.0" -o "$work/BitCastReal/Gen.lean" --namespace BitCastReal --prefix bitcast017.
cmp "$work/BitCastReal/Gen.lean" "$dir/BitCastReal/Gen.lean"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -R "$work" -o "$work/BitCastReal/Gen.olean" "$work/BitCastReal/Gen.lean"
lake env lean -R "$dir" --run "$dir/BitCastReal/Runtime.lean"
semantics=$(lake env lean "$dir/Semantics.lean")
printf '%s\n' "$semantics"
if grep -q sorryAx <<<"$semantics"; then echo 'ZigLean.BitCast lemma depends on sorry' >&2; exit 1; fi
lake env lean --run "$dir/Pipeline.lean" "$work/Synthetic.lean"
lake env lean --run "$work/Synthetic.lean"
