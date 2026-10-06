#!/usr/bin/env bash
# ROOT's single bounded Linux lane only. No background compiler processes or version calls.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
: "${AIR2LEAN_ZIG_AIR:?set a qualified patched compiler}"
: "${AIR2LEAN_ZIG_NATIVE:?set the matching qualified stock compiler}"
: "${AIR2LEAN_ERROR_STORAGE_VERSION:?set an owner-verified compiler label}"
: "${AIR2LEAN_ERROR_STORAGE_OUT_DIR:?set a fresh retained output directory}"
case "$AIR2LEAN_ERROR_STORAGE_VERSION" in 0.14.1|0.15.2|0.16.0) ;; *) echo 'unsupported label' >&2; exit 2;; esac
work=$AIR2LEAN_ERROR_STORAGE_OUT_DIR
[ ! -e "$work" ] || { echo 'output already exists' >&2; exit 2; }
mkdir -p "$work/air" "$work/mutants"
if [ "${AIR2LEAN_ERROR_STORAGE_BUILD:-0}" = 1 ]; then lake build ZigLean Air2Lean air2lean; fi
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
"${lean_cmd[@]}" --run tests/roadmap/error-storage/Runtime.lean
"${lean_cmd[@]}" --run tests/roadmap/error-storage/Pipeline.lean "$work/Synthetic.lean"
"${lean_cmd[@]}" -R "$work" "$work/Synthetic.lean"
"$AIR2LEAN_ZIG_NATIVE" test tests/roadmap/error-storage/error_storage.zig -OReleaseSafe
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER=error_storage. \
  "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
  -target x86_64-linux -mcpu=baseline tests/roadmap/error-storage/error_storage.zig
python3 - "$work/air" <<'PY_INVENTORY'
import json
import sys
from pathlib import Path
expected = {"overwrite", "readError", "writeError", "writePayload", "globalRoundtrip", "propagate", "nestedOuter", "payloadUnion"}
files = list(Path(sys.argv[1]).glob("*.json"))
observed = {json.loads(p.read_text())["name"].removeprefix("error_storage.") for p in files}
if observed != expected or len(files) != len(expected):
    raise SystemExit(f"error storage export mismatch: {observed}")
PY_INVENTORY
"$translator" "$work/air" -o "$work/Gen.lean" --namespace ErrorStorage --prefix error_storage.
"${lean_cmd[@]}" -R "$work" "$work/Gen.lean"
python3 tests/roadmap/error-storage/patch-observations.py "$work/Gen.lean" tests/roadmap/error-storage/DiffMain.lean.inc "$work/Diff.lean"
"${lean_cmd[@]}" -R "$work" "$work/Diff.lean"
"$AIR2LEAN_ZIG_NATIVE" build-exe -OReleaseSafe -mcpu=baseline \
  -femit-bin="$work/native" tests/roadmap/error-storage/native.zig
"$work/native" 2> "$work/native.txt"
"${lean_cmd[@]}" -R "$work" --run "$work/Diff.lean" > "$work/lean.txt"
[ "$(wc -l < "$work/native.txt" | tr -d ' ')" = 3 ] || { echo 'incomplete observations' >&2; exit 1; }
cmp "$work/native.txt" "$work/lean.txt"
python3 tests/roadmap/error-storage/mutations.py "$work/mutants"
"${lean_cmd[@]}" -R "$work/mutants" "$work/mutants/control.lean"
mutant_count=0
while IFS= read -r name; do
  [ -n "$name" ] || { echo 'empty mutant name' >&2; exit 1; }
  "${lean_cmd[@]}" -R "$work/mutants" "$work/mutants/$name.defs.lean"
  status=0
  "${lean_cmd[@]}" -R "$work/mutants" "$work/mutants/$name.lean" > "$work/mutants/$name.log" 2>&1 || status=$?
  python3 tests/roadmap/error-storage/classify_mutant.py "$status" "$work/mutants/$name.lean" "$work/mutants/$name.log"
  mutant_count=$((mutant_count + 1))
done < "$work/mutants/mutants.txt"
[ "$mutant_count" -gt 0 ] || { echo 'empty mutation inventory' >&2; exit 1; }
printf '%s\n' "$AIR2LEAN_ERROR_STORAGE_VERSION" > "$work/owner-version-label.txt"
echo "finite error storage passed: 8 exports, 3 proved semantic observation rows (9 predicates each), $mutant_count killed typed dictionary mutants"
