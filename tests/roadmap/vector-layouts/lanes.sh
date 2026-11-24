#!/usr/bin/env bash
# L09 lane pointers: translate the committed lanes.zig AIR of every version (0.17.1, 0.16.0,
# 0.15.2), compare the 0.16.0 translation with Lanes/Gen.lean, and check the theorems and the
# concrete runs on each version's translation; --native runs lanes.zig's test with a stock Zig
# (any of these versions); --export DIR [VERSION] exports fresh AIR with the patched Zig VERSION
# (default 0.16.0) and compares its translation with that of the committed air/VERSION.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/vector-layouts
versions=(0.17.1 0.16.0 0.15.2)
usage='usage: lanes.sh [--check|--native|--export DIR [VERSION]]'
case "${1:---check}" in
  --native)
    [ "$#" -eq 1 ] || { echo "$usage" >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig (0.17.1, 0.16.0 or 0.15.2)}"
    "$AIR2LEAN_ZIG_NATIVE" test -fllvm -OReleaseSafe "$dir/lanes.zig"
    exit ;;
  --export)
    [ "$#" -eq 2 ] || [ "$#" -eq 3 ] || { echo "$usage" >&2; exit 2; }
    version=${3:-0.16.0}
    [ -d "$dir/air/$version" ] || { echo "lanes.sh: no committed air/$version" >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set the patched Zig of the exported version}"
    mkdir -p "$2/air"
    [ -z "$(find "$2/air" -mindepth 1 -print -quit)" ] || { echo 'AIR output must be empty' >&2; exit 1; }
    ZIG_AIR_JSON_DIR="$(cd -- "$2/air" && pwd)" ZIG_AIR_JSON_FILTER=lanes. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline "$dir/lanes.zig"
    .lake/build/bin/air2lean "$2/air" -o "$2/Gen.lean" --namespace Lanes --prefix lanes.
    .lake/build/bin/air2lean "$dir/air/$version" -o "$2/Committed.lean" --namespace Lanes --prefix lanes.
    cmp "$2/Gen.lean" "$2/Committed.lean"
    if [ "$version" = 0.16.0 ]; then cmp "$2/Gen.lean" "$dir/Lanes/Gen.lean"; fi
    echo "lanes: fresh $version export translates as the committed air/$version"
    exit ;;
  --check) [ "$#" -le 1 ] || { echo "$usage" >&2; exit 2; } ;;
  *) echo "$usage" >&2; exit 2 ;;
esac
python3 "$dir/lanes_checks.py" --check
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-lanes.XXXXXX")
trap 'rm -rf "$work"' EXIT
base_path="$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
for version in "${versions[@]}"; do
  mkdir -p "$work/$version/Lanes"
  .lake/build/bin/air2lean "$dir/air/$version" -o "$work/$version/Lanes/Gen.lean" \
    --namespace Lanes --prefix lanes.
  if [ "$version" = 0.16.0 ]; then cmp "$work/$version/Lanes/Gen.lean" "$dir/Lanes/Gen.lean"; fi
  export LEAN_PATH="$work/$version:$base_path"
  lake env lean -R "$work/$version" -o "$work/$version/Lanes/Gen.olean" "$work/$version/Lanes/Gen.lean"
  lake env lean -R "$dir" "$dir/Lanes/Checks.lean"
  # The theorems are stated on the translated lane clients, whichever version exported them.
  lake env lean -R "$dir" "$dir/Lanes/Proofs.lean"
done
echo "lanes: translations, theorems and concrete runs checked (${versions[*]})"
