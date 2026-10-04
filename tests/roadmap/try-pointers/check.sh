#!/usr/bin/env bash
# All tool invocations must run in the root's exclusive serialized validation queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case "${1:---check-artifacts}" in
  --native)
    [ "$#" -eq 1 ] || { echo 'usage: check.sh --native' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a qualified stock host Zig}"
    "$AIR2LEAN_ZIG_NATIVE" test tests/roadmap/try-pointers/try_pointers.zig -OReleaseSafe
    exit ;;
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a qualified patched compiler with the updated exporter}"
    mkdir -p "$2"
    [ -z "$(find "$2" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo 'AIR output must be empty' >&2; exit 1; }
    air_output=$(cd -- "$2" && pwd)
    ZIG_AIR_JSON_DIR="$air_output" ZIG_AIR_JSON_FILTER=try_pointers. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline tests/roadmap/try-pointers/try_pointers.zig
    exit ;;
  --check-artifacts) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check-artifacts]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check-artifacts|--native|--export OUTPUT_DIR]' >&2; exit 2 ;;
esac
python3 tests/roadmap/try-pointers/check-artifacts.py
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build translator first' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-try-pointers.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/TryPointers"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
"$translator" tests/roadmap/try-pointers/air/0.16.0 -o "$work/TryPointers/Gen.lean" \
  --namespace TryPointers --prefix try_pointers.
if [ -f tests/roadmap/try-pointers/integration-qualification.json ]; then
  python3 scripts/normalize-generated.py report "$work/TryPointers/Gen.lean" \
    tests/roadmap/try-pointers/air/0.16.0 "$work/generated-report.json"
  python3 scripts/normalize-generated.py compare tests/roadmap/try-pointers/TryPointers/Gen.lean \
    "$work/TryPointers/Gen.lean" "$work/generated-report.json"
else
  cmp "$work/TryPointers/Gen.lean" tests/roadmap/try-pointers/TryPointers/Gen.lean
fi
"${lean_cmd[@]}" -R "$work" -o "$work/TryPointers/Gen.olean" "$work/TryPointers/Gen.lean"
"${lean_cmd[@]}" -R tests/roadmap/try-pointers tests/roadmap/try-pointers/TryPointers/Proofs.lean
"${lean_cmd[@]}" -R tests/roadmap/try-pointers --run tests/roadmap/try-pointers/TryPointers/Runtime.lean
"${lean_cmd[@]}" --run tests/roadmap/try-pointers/Pipeline.lean "$work/Synthetic.lean"
"${lean_cmd[@]}" --run "$work/Synthetic.lean"
"${lean_cmd[@]}" --run "$work/Synthetic.lean.loads.lean"
"${lean_cmd[@]}" --run "$work/Synthetic.lean.memory.lean"
# Compile a well-typed offset mutant first; only the same proof's located equality
# failure counts. Import, syntax, tool, unrelated proof and signal failures do not.
mutant="$work/offset-mutant"
mkdir -p "$mutant/TryPointers"
python3 tests/roadmap/try-pointers/mutate-offset.py create \
  --source "$work/TryPointers/Gen.lean" --output "$mutant/TryPointers/Gen.lean"
cp tests/roadmap/try-pointers/TryPointers/Proofs.lean "$mutant/TryPointers/Proofs.lean"
LEAN_PATH="$mutant:$LEAN_PATH" "${lean_cmd[@]}" -R "$mutant" \
  -o "$mutant/TryPointers/Gen.olean" "$mutant/TryPointers/Gen.lean"
mutant_status=0
LEAN_PATH="$mutant:$LEAN_PATH" "${lean_cmd[@]}" -R "$mutant" \
  "$mutant/TryPointers/Proofs.lean" >"$mutant/proof.log" 2>&1 || mutant_status=$?
if ! python3 tests/roadmap/try-pointers/mutate-offset.py classify \
  --status "$mutant_status" --proof "$mutant/TryPointers/Proofs.lean" --log "$mutant/proof.log"; then
  # The outer validation log retains the exact diagnostics before EXIT cleans the
  # temporary tree. Classification stays strict; evidence is ordinary runner output.
  cat "$mutant/proof.log" >&2
  exit 1
fi
echo 'pointer-try artifact, ownership, generated runtime, malformed-AIR and offset-mutant gates passed'
