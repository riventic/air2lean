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
  --check-artifacts) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check-artifacts]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check-artifacts|--native]' >&2; exit 2 ;;
esac
python3 -B scripts/lean-deps.py --build "$case_dir"
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
"${lean_cmd[@]}" -R "$case_dir" -o "$work/TryAliases/Proofs.olean" "$case_dir/TryAliases/Proofs.lean"
"${lean_cmd[@]}" -R "$case_dir" --run "$case_dir/TryAliases/Runtime.lean"
# The strength log of every pointer-try triple (tests/roadmap/strength-log).
"${lean_cmd[@]}" -R tests/roadmap/try-pointers -o "$work/TryPointers/Proofs.olean" \
  tests/roadmap/try-pointers/TryPointers/Proofs.lean
"${lean_cmd[@]}" tests/roadmap/strength-log/TryPointers.lean
echo 'pointer-try alias/cleanup ownership and generated runtime gates passed'
