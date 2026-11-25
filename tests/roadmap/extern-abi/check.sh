#!/usr/bin/env bash
# X01: the C-ABI conversion at a bound extern call (docs/c-frontend.md §libc boundary). Needs a
# built translator and `lake build ZigLean`; runs no compiler. abi.c's translate-c declarations
# (abi.zig: `zig translate-c -target x86_64-linux-musl -lc abi.c` of stock Zig 0.17.1, its host
# paths written `$ZIG_LIB_DIR/`) bind to Zig 0.17.1's libc definitions through the conversion
# (EXT-07: Zig's libc exports them weakly); the translation evaluates to expected.txt and to
# `.illegal` for each value the definition's type does not admit (Eval.lean). test_cli.py checks
# the conversions and the pairs left rejected (air-reject: rejected.c). The AIR is pinned by
# exports.lock.json (scripts/fixture-exports.py). `--native` runs native.zig with a stock Zig 0.17.1
# (AIR2LEAN_ZIG_NATIVE) on x86_64-linux against expected.txt.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/extern-abi
if [ "${1:-}" = --native ]; then
  : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig 0.17.1 on x86_64-linux}"
  work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-extern-abi.XXXXXX")
  trap 'rm -rf "$work"' EXIT
  "$AIR2LEAN_ZIG_NATIVE" build-exe -OReleaseSafe -target x86_64-linux-musl -mcpu=baseline -lc \
    "$here/native.zig" --cache-dir "$work/cache" --global-cache-dir "$work/cache" \
    -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  diff "$here/expected.txt" "$work/native.txt"
  echo "extern-abi native: ok"
  exit 0
fi
python3 -B scripts/lean-deps.py --build "$here"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-extern-abi.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/ExternAbi"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
python3 -B scripts/fixture-exports.py check extern-abi
# The retained translation is the fresh one, byte for byte.
"$translator" "$here/air/0.17.1" -o "$work/ExternAbi/Gen.lean" --allocator-model translated \
  --assume-weak-exports --namespace ExternAbi --prefix abi.
cmp "$work/ExternAbi/Gen.lean" "$here/ExternAbi/Gen.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/ExternAbi/Gen.olean" "$work/ExternAbi/Gen.lean"
"${lean_cmd[@]}" "$here/Eval.lean"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
echo "extern-abi: ok"
