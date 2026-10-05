#!/usr/bin/env bash
# All compiler calls are sequential; run from the root's exclusive validation queue.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
case "${1:---check-artifacts}" in
  --native)
    [ "$#" -eq 1 ] || { echo 'usage: check.sh --native' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock host Zig binary}"
    version=$("$AIR2LEAN_ZIG_NATIVE" version)
    case "$version" in 0.14.1|0.15.2|0.16.0) ;; *) echo "unsupported native Zig: $version" >&2; exit 1;; esac
    "$AIR2LEAN_ZIG_NATIVE" test -OReleaseSafe --dep thread_tuple_source \
      -Mroot=tests/roadmap/thread-tuples/native.zig \
      -Mthread_tuple_source=tests/roadmap/thread-tuples/thread_tuples.zig
    exit
    ;;
  --export)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --export OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a qualified patched AIR compiler}"
    mkdir -p "$2"
    [ -z "$(find "$2" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo 'AIR output must be empty' >&2; exit 1; }
    air_output=$(cd -- "$2" && pwd)
    export_filter=$(paste -sd, tests/roadmap/thread-tuples/filter)
    [ -n "$export_filter" ] || { echo 'AIR filter is empty' >&2; exit 1; }
    ZIG_AIR_JSON_DIR="$air_output" ZIG_AIR_JSON_FILTER="$export_filter" \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline tests/roadmap/thread-tuples/thread_tuples.zig
    python3 tests/roadmap/thread-tuples/check-export.py "$air_output"
    exit
    ;;
  --adapter-contract)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --adapter-contract OUTPUT_DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set matching patched 0.16 AIR compiler}"
    mkdir -p "$2"
    [ -z "$(find "$2" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo 'adapter output must be empty' >&2; exit 1; }
    adapter_output=$(cd -- "$2" && pwd)
    cp tests/roadmap/thread-tuples/adapter-contract.zig "$adapter_output/thread_adapter_contract.zig"
    mkdir "$adapter_output/air"
    ZIG_AIR_JSON_DIR="$adapter_output/air" \
    ZIG_AIR_JSON_FILTER='thread_adapter_contract.mutableCapture,thread_adapter_contract.strongCapture,thread_adapter_contract.weakCapture,thread_adapter_contract.sliceWorker' \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline "$adapter_output/thread_adapter_contract.zig" --cache-dir "$adapter_output/cache"
    python3 tests/roadmap/thread-tuples/check-export.py "$adapter_output/air" --adapter
    translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
    "$translator" "$adapter_output/air" -o "$adapter_output/Gen.lean" \
      --namespace ThreadAdapterContract --prefix thread_adapter_contract.
    export LEAN_PATH="$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
    if [ -n "${AIR2LEAN_LEAN:-}" ]; then
      "$AIR2LEAN_LEAN" "$adapter_output/Gen.lean"
    else
      lake env lean "$adapter_output/Gen.lean"
    fi
    echo 'fresh adapter source export, translation and kernel gate passed'
    exit
    ;;
  --check-artifacts) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check-artifacts]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check-artifacts|--native|--export OUTPUT_DIR|--adapter-contract OUTPUT_DIR]' >&2; exit 2 ;;
esac
python3 tests/roadmap/thread-tuples/check-artifacts.py
python3 - tests/roadmap/thread-tuples/ThreadTuples/Proofs.lean <<'PYPROOF'
from pathlib import Path
import re
import sys

path = Path(sys.argv[1])
try:
    source = path.read_text(encoding="utf-8")
except (OSError, UnicodeError) as error:
    sys.exit(f"proof scan failed: {path}: {error}")
for number, line in enumerate(source.splitlines(), 1):
    if re.search(r"\b(sorry|admit|native_decide|axiom)\b", line):
        sys.exit(f"proof contains an untrusted declaration: {path}:{number}: {line}")
PYPROOF
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-thread-tuples.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/ThreadTuples"
"$translator" tests/roadmap/thread-tuples/air/0.16.0 -o "$work/ThreadTuples/Gen.lean" \
  --namespace ThreadTuples --prefix thread_tuples.
python3 scripts/normalize-generated.py report "$work/ThreadTuples/Gen.lean" \
  tests/roadmap/thread-tuples/air/0.16.0 "$work/generated-report.json"
python3 scripts/normalize-generated.py compare tests/roadmap/thread-tuples/ThreadTuples/Gen.lean \
  "$work/ThreadTuples/Gen.lean" "$work/generated-report.json"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
"${lean_cmd[@]}" -R "$work" -o "$work/ThreadTuples/Gen.olean" "$work/ThreadTuples/Gen.lean"
"${lean_cmd[@]}" -R "$repo_root/tests/roadmap/thread-tuples" tests/roadmap/thread-tuples/ThreadTuples/Proofs.lean
"${lean_cmd[@]}" -R "$repo_root/tests/roadmap/thread-tuples" --run tests/roadmap/thread-tuples/ThreadTuples/Runtime.lean
"${lean_cmd[@]}" --run tests/roadmap/thread-tuples/Pipeline.lean "$work/TuplePipeline.lean"
"${lean_cmd[@]}" -R "$work" "$work/TuplePipeline.lean"
"${lean_cmd[@]}" -R "$work" "$work/TuplePipeline.lean.slices.lean"
"${lean_cmd[@]}" -R "$work" "$work/TuplePipeline.lean.single.lean"
"${lean_cmd[@]}" -R "$work" "$work/TuplePipeline.lean.nested.lean"
"${lean_cmd[@]}" -R "$work" "$work/TuplePipeline.lean.mutable-slices.lean"
"${lean_cmd[@]}" -R "$work" --run "$work/TuplePipeline.lean.aligned-slices.lean"
python3 - "$work/TuplePipeline.lean" "$work/Mutated.lean" <<'PYMUTATE'
from pathlib import Path
import sys
source = Path(sys.argv[1]).read_text()
old = "worker capture0 capture1 capture2"
if source.count(old) != 1:
    raise SystemExit("tuple order mutation did not find exactly one dispatcher")
Path(sys.argv[2]).write_text(source.replace(old, "worker capture0 capture2 capture1"))
PYMUTATE
mutation_status=0
"${lean_cmd[@]}" -R "$work" "$work/Mutated.lean" >"$work/mutation.log" 2>&1 || mutation_status=$?
# Require normal exit 1 and only the located dispatcher equality's rfl diagnostic.
python3 tests/roadmap/thread-tuples/classify_mutant.py "$mutation_status" "$work/mutation.log" "$work/Mutated.lean"
echo 'thread tuple artifact, runtime, signature, slice, and order mutation gates passed'
