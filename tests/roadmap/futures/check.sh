#!/usr/bin/env bash
# C08 gate: Io.Future model, translation, proofs and runtime schedules (docs/futures.md).
# Compiler calls are sequential; run from the root's exclusive validation queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case_dir=tests/roadmap/futures
case "${1:---check-artifacts}" in
  --native)
    [ "$#" -eq 1 ] || { echo 'usage: check.sh --native' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig 0.16.0 binary}"
    [ "$("$AIR2LEAN_ZIG_NATIVE" version)" = 0.16.0 ] || { echo 'futures need Zig 0.16.0' >&2; exit 1; }
    "$AIR2LEAN_ZIG_NATIVE" test -OReleaseSafe --dep futures_source \
      -Mroot=$case_dir/native.zig -Mfutures_source=$case_dir/futures.zig
    exit
    ;;
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a qualified patched 0.16.0 AIR compiler}"
    mkdir -p "$2"
    [ -z "$(find "$2" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo 'AIR output must be empty' >&2; exit 1; }
    air_output=$(cd -- "$2" && pwd)
    mkdir "$air_output/air"
    ZIG_AIR_JSON_DIR="$air_output/air" ZIG_AIR_JSON_FILTER=futures. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline $case_dir/futures.zig --cache-dir "$air_output/cache"
    translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
    "$translator" "$air_output/air" -o "$air_output/Gen.lean" --namespace Futures --prefix futures.
    diff <(grep -v '^-- air2lean-profile:' "$air_output/Gen.lean") \
      <(grep -v '^-- air2lean-profile:' $case_dir/Futures/Gen.lean)
    echo 'fresh futures export translates to the committed Gen.lean'
    exit
    ;;
  --check-artifacts) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check-artifacts]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check-artifacts|--native|--export OUTPUT_DIR]' >&2; exit 2 ;;
esac
for proof in $case_dir/Futures/Proofs.lean ZigLean/Conc/FutureLemmas.lean ZigLean/Conc/Future.lean; do
  if grep -nE '\b(sorry|admit|native_decide|axiom)\b' "$proof"; then
    echo "untrusted declaration in $proof" >&2; exit 1
  fi
done
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-futures.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/Futures" "$work/FuturesFallible"
"$translator" $case_dir/air/0.16.0 -o "$work/Futures/Gen.lean" --namespace Futures --prefix futures.
cmp "$work/Futures/Gen.lean" $case_dir/Futures/Gen.lean
"$translator" $case_dir/air/0.16.0 -o "$work/FuturesFallible/Gen.lean" \
  --namespace FuturesFallible --prefix futures. --spawn-policy fallible
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
"${lean_cmd[@]}" -R "$work" -o "$work/Futures/Gen.olean" "$work/Futures/Gen.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/FuturesFallible/Gen.olean" "$work/FuturesFallible/Gen.lean"
"${lean_cmd[@]}" -R $case_dir $case_dir/Futures/Proofs.lean
"${lean_cmd[@]}" -R $case_dir --run $case_dir/Futures/Runtime.lean
"${lean_cmd[@]}" --run $case_dir/FallibleRuntime.lean
"${lean_cmd[@]}" --run $case_dir/Pipeline.lean
echo 'futures translation, proofs, runtime schedules and boundary gates passed'
