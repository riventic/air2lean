#!/usr/bin/env bash
# L09 lane pointers: translate the committed lanes.zig AIR, compare with Lanes/Gen.lean, check
# the theorems and the concrete runs; --native runs lanes.zig's test with a stock Zig;
# --export DIR exports fresh AIR with the patched Zig 0.16.0 and checks its translation.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/vector-layouts
case "${1:---check}" in
  --native)
    [ "$#" -eq 1 ] || { echo 'usage: lanes.sh --native' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig 0.16.0}"
    "$AIR2LEAN_ZIG_NATIVE" test -fllvm -OReleaseSafe "$dir/lanes.zig"
    exit ;;
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: lanes.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set the patched Zig 0.16.0}"
    mkdir -p "$2/air"
    [ -z "$(find "$2/air" -mindepth 1 -print -quit)" ] || { echo 'AIR output must be empty' >&2; exit 1; }
    ZIG_AIR_JSON_DIR="$(cd -- "$2/air" && pwd)" ZIG_AIR_JSON_FILTER=lanes. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline "$dir/lanes.zig"
    .lake/build/bin/air2lean "$2/air" -o "$2/Gen.lean" --namespace Lanes --prefix lanes.
    cmp "$2/Gen.lean" "$dir/Lanes/Gen.lean"
    echo 'lanes: fresh 0.16.0 export translates to the committed Lanes/Gen.lean'
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: lanes.sh [--check|--native|--export DIR]' >&2; exit 2; } ;;
  *) echo 'usage: lanes.sh [--check|--native|--export DIR]' >&2; exit 2 ;;
esac
python3 "$dir/lanes_checks.py" --check
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-lanes.XXXXXX")
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work/0.16.0:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
for version in 0.16.0 0.15.2; do
  mkdir -p "$work/$version/Lanes"
  .lake/build/bin/air2lean "$dir/air/$version" -o "$work/$version/Lanes/Gen.lean" \
    --namespace Lanes --prefix lanes.
  if [ "$version" = 0.16.0 ]; then cmp "$work/$version/Lanes/Gen.lean" "$dir/Lanes/Gen.lean"; fi
  lake env lean -R "$work/$version" -o "$work/$version/Lanes/Gen.olean" "$work/$version/Lanes/Gen.lean"
  LEAN_PATH="$work/$version:$LEAN_PATH" lake env lean -R "$dir" "$dir/Lanes/Checks.lean"
done
lake env lean -R "$dir" "$dir/Lanes/Proofs.lean"
echo 'lanes: translations, theorems and concrete runs checked (0.16.0, 0.15.2)'
