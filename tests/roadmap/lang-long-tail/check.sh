#!/usr/bin/env bash
# L-series long tail (tests/roadmap/lang-long-tail/README.md). Needs a built translator and
# `lake build ZigLean Air2Lean`; runs no compiler unless --native (`export.sh --check`
# re-exports with the recorded patched compilers).
#
#   check.sh [--native]
#
# For every fixture source: the committed exports match provenance.json; the export of every
# supported Zig version (0.17.0, 0.16.0, 0.15.2, 0.14.1) translates to the retained
# `LangLongTail/<Ns>.lean` (byte for byte for 0.16.0, the same body for the others); the
# retained translation elaborates; the proofs check; the model's lines equal the committed
# native output of every version; the negative tests reject. `--native` also runs each probe
# with the stock Zig compilers named by AIR2LEAN_ZIG_NATIVE_<major>_<minor> (for example
# AIR2LEAN_ZIG_NATIVE_0_16) that are set, and compares their output with the model.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/lang-long-tail
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-lang-long-tail.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/LangLongTail"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
python3 "$here/test_provenance.py"

# stem, Lean namespace (= retained module name), extra translator arguments.
fixtures=(
  "error_params ErrorParams"
)
versions=(0.17.0 0.16.0 0.15.2 0.14.1)
for entry in "${fixtures[@]}"; do
  read -r stem ns extra <<< "$entry"
  retained="$here/LangLongTail/$ns.lean"
  for version in "${versions[@]}"; do
    # shellcheck disable=SC2086 # extra holds whitespace-separated translator flags
    "$translator" "$here/air/$stem/$version" -o "$work/$ns-$version.lean" \
      --namespace "$ns" --prefix "$stem." $extra
    if [ "$version" = 0.16.0 ]; then
      cmp "$work/$ns-$version.lean" "$retained"
    else
      cmp <(tail -n +2 "$work/$ns-$version.lean") <(tail -n +2 "$retained")
    fi
  done
  cp "$retained" "$work/LangLongTail/$ns.lean"
  "${lean_cmd[@]}" -R "$work" -o "$work/LangLongTail/$ns.olean" "$work/LangLongTail/$ns.lean"
  if [ -f "$here/Proofs$ns.lean" ]; then
    "${lean_cmd[@]}" "$here/Proofs$ns.lean"
  fi
  for version in "${versions[@]}"; do
    "${lean_cmd[@]}" --run "$here/Model$ns.lean" "$here/native/$stem-$version.txt"
  done
done
python3 "$here/test_cli.py" "$translator"
if [ "${1:-}" = --native ]; then
  for entry in "${fixtures[@]}"; do
    read -r stem ns _ <<< "$entry"
    ran=0
    for version in "${versions[@]}"; do
      var="AIR2LEAN_ZIG_NATIVE_$(echo "$version" | cut -d. -f1-2 | tr . _)"
      zig=${!var:-}
      [ -n "$zig" ] || continue
      (cd "$here" && "$zig" run -OReleaseSafe "probe_$stem.zig") 2> "$work/$stem-$version.txt"
      "${lean_cmd[@]}" --run "$here/Model$ns.lean" "$work/$stem-$version.txt"
      ran=1
    done
    [ "$ran" = 1 ] || { echo "error: --native needs AIR2LEAN_ZIG_NATIVE_<major>_<minor> for at least one version" >&2; exit 1; }
  done
fi
echo "lang-long-tail: ok"
