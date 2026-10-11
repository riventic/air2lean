#!/usr/bin/env bash
# L04 alias/cleanup gate. All tool invocations must run in the root's serialized queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
case_dir=tests/roadmap/try-pointers/aliases
case "${1:---check-artifacts}" in
  --native)
    [ "$#" -eq 1 ] || { echo 'usage: check.sh --native' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a qualified stock host Zig}"
    "$AIR2LEAN_ZIG_NATIVE" test tests/roadmap/try-pointers/try_aliases.zig -OReleaseSafe
    exit ;;
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a qualified patched compiler with the updated exporter}"
    mkdir -p "$2"
    [ -z "$(find "$2" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo 'AIR output must be empty' >&2; exit 1; }
    air_output=$(cd -- "$2" && pwd)
    ZIG_AIR_JSON_DIR="$air_output" ZIG_AIR_JSON_FILTER=try_aliases. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline tests/roadmap/try-pointers/try_aliases.zig
    exit ;;
  --check-artifacts) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check-artifacts]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check-artifacts|--native|--export OUTPUT_DIR]' >&2; exit 2 ;;
esac
python3 "$case_dir/check-artifacts.py"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build translator first' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-try-aliases.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/TryPointers" "$work/TryAliases"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
"$translator" "$case_dir/air/0.16.0" --profile legacy-abi64-le -o "$work/TryAliases/Gen.lean" \
  --namespace TryAliases --prefix try_aliases.
cmp "$work/TryAliases/Gen.lean" "$case_dir/TryAliases/Gen.lean"
# The retained compiler-exported pointer-try module supplies writeAlias/cleanup/coldPayload.
"${lean_cmd[@]}" -R tests/roadmap/try-pointers -o "$work/TryPointers/Gen.olean" \
  tests/roadmap/try-pointers/TryPointers/Gen.lean
"${lean_cmd[@]}" -R tests/roadmap/try-pointers -o "$work/TryPointers/AliasProofs.olean" \
  tests/roadmap/try-pointers/TryPointers/AliasProofs.lean
"${lean_cmd[@]}" -R "$work" -o "$work/TryAliases/Gen.olean" "$work/TryAliases/Gen.lean"
"${lean_cmd[@]}" -R "$case_dir" "$case_dir/TryAliases/Proofs.lean"
"${lean_cmd[@]}" -R "$case_dir" --run "$case_dir/TryAliases/Runtime.lean"
echo 'pointer-try alias/cleanup ownership and generated runtime gates passed'
