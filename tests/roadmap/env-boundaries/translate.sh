#!/usr/bin/env bash
# E03 std I/O fixtures: committed AIR -> registry template -> ENV-03 registry -> Lean.
# No compiler or Lean runs here; check.sh elaborates the result.
# usage: translate.sh OUTPUT_DIR [--update]
#   OUTPUT_DIR gets EnvStd15/Gen.lean and EnvStd16/Gen.lean; without --update they must equal
#   expected/ and registry/ byte for byte; with --update those are rewritten.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
here="$repo/tests/roadmap/env-boundaries"
translator=${AIR2LEAN_TRANSLATOR:-"$repo/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
[ "$#" -ge 1 ] || { echo 'usage: translate.sh OUTPUT_DIR [--update]' >&2; exit 2; }
out=$1
update=${2:-}
for v in 15 16; do
  ns=EnvStd$v zv=0.$v.0
  [ "$v" = 15 ] && zv=0.15.2
  mkdir -p "$out/$ns"
  "$translator" "$here/air/$zv" -o "$out/$ns/template.json" --namespace "$ns" --model-registry-template
  python3 -B "$here/fill_registry.py" "$out/$ns/template.json" "$out/$ns/registry.json"
  "$translator" "$here/air/$zv" -o "$out/$ns/Gen.lean" --namespace "$ns" --prefix "std_io$v." \
    --model-registry "$out/$ns/registry.json"
  if [ "$update" = --update ]; then
    cp "$out/$ns/registry.json" "$here/registry/std$v.json"
    cp "$out/$ns/Gen.lean" "$here/expected/$ns.lean"
  fi
  cmp "$out/$ns/registry.json" "$here/registry/std$v.json"
  cmp "$out/$ns/Gen.lean" "$here/expected/$ns.lean"
done
echo "env-boundaries: std15/std16 translated with the ENV-03 registry; output matches expected/"
