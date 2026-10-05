#!/usr/bin/env bash
# Called by the root's monitored validation queue. Never run compiler checks in parallel.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"
if [ "$#" -gt 1 ]; then echo 'usage: emitter.sh [OUTPUT_DIR]' >&2; exit 2; fi
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-emitter.XXXXXX")
trap 'rm -rf "$work"' EXIT
output=${1:-"$work/output"}
# Absolute paths also prevent find from treating a leading-hyphen directory as a predicate.
case "$output" in /*) ;; *) output="$repo_root/$output" ;; esac
: > "$work/caller"
for source in "$output"/*.lean; do
  [ ! -f "$source" ] || printf '%s\n' "$source" >> "$work/caller"
done
# Generate from scratch: a reused output directory must not mask a dropped semantic case.
generated="$work/generated"
lake env lean --run tests/review/Emitter.lean "$generated"
while IFS= read -r source; do
  [ -f "$source" ] || { echo "error: caller fixture removed: $source" >&2; exit 1; }
done < "$work/caller"
# Pin every emitted semantic case, including both float modes: a lost generator case fails.
required='pointerCasts tuples names indirectCapture blockLoopExits unionTagCapture spawnedSlice floatIeee floatCompilerRt legacyUnionTag escapingSafetyCheck derivedInstanceNames binderTypeNames classNames underscoreName ctorIndexNames generatedBinderTypeNames indexedBinderTypeNames generatedBinderFunctionNames reservedKeywordNames'
for name in $required; do
  [ -f "$generated/$name.lean" ] || { echo "error: missing emitter fixture: $name" >&2; exit 1; }
done
mkdir -p "$output"
# Publish only fresh generated fixtures, preserving the caller's Parser outputs.
cp "$generated"/*.lean "$output/"
# Materialize the checked producer. An independent glob inventory detects truncated output.
find "$output" -maxdepth 1 -type f -name '*.lean' | LC_ALL=C sort > "$work/manifest"
: > "$work/glob"
expected=0
for source in "$output"/*.lean; do
  [ -f "$source" ] || continue
  printf '%s\n' "$source" >> "$work/glob"
  expected=$((expected + 1))
done
LC_ALL=C sort "$work/glob" > "$work/expected"
listed=$(wc -l < "$work/manifest" | tr -d ' ')
[ "$listed" -eq "$expected" ] && cmp -s "$work/manifest" "$work/expected" || {
  echo "error: emitter fixture listing incomplete: listed $listed, expected $expected" >&2
  exit 1
}
checked=0
while IFS= read -r source; do
  lake env lean "$source"
  checked=$((checked + 1))
done < "$work/manifest"
echo "emitter regressions passed: $checked fixtures checked"
