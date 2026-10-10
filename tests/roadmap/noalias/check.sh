#!/usr/bin/env bash
# noalias gate (docs/illegal-behavior.md, "noalias"):
#   - translates the retained 0.16.0 AIR of na.zig (air/) and compares it with Gen.lean;
#   - checks that the translator rejects the function whose noalias pointer escapes (probe-air/);
#   - runs Cases.lean: overlapping calls are `.illegal`, disjoint or read-only ones return values.
# Optional: AIR2LEAN_ZIG_AIR=patched-0.16/bin/zig re-exports the AIR and compares it with air/ and
# probe-air/.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/noalias
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-noalias.XXXXXX")
trap 'rm -rf "$work"' EXIT
lake build ZigLean Air2Lean air2lean

if [ -n "${AIR2LEAN_ZIG_AIR:-}" ]; then
  bash "$here/export.sh" "$AIR2LEAN_ZIG_AIR" "$work/fresh"
  mkdir "$work/fresh-probe"
  mv "$work/fresh/na.escape.json" "$work/fresh-probe/"
  cp "$work/fresh/na.sink.json" "$work/fresh-probe/"
  diff -r "$here/air" "$work/fresh"
  diff -r "$here/probe-air" "$work/fresh-probe"
fi

lake exe air2lean "$here/air" -o "$work/Gen.lean" --namespace Noalias --prefix na.
cmp "$work/Gen.lean" "$here/Gen.lean"

status=0
lake exe air2lean "$here/probe-air" -o "$work/Probe.lean" --namespace Probe --prefix na. \
  > "$work/probe.log" 2>&1 || status=$?
if [ "$status" = 0 ] || ! grep -q 'na.escape: inst [0-9]*: a value based on a noalias parameter' "$work/probe.log"; then
  echo "escape probe was not rejected (status $status)" >&2; cat "$work/probe.log" >&2; exit 1
fi

lake env lean -R "$work" -o "$work/Gen.olean" "$work/Gen.lean"
LEAN_PATH="$work:$(lake env printenv LEAN_PATH)" lake env lean -R "$work" --run "$here/Cases.lean"
echo 'noalias passed'
