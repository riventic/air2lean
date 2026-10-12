#!/usr/bin/env bash
# L-series long tail (tests/roadmap/lang-long-tail/README.md). Needs a built translator and
# `lake build ZigLean ZigLean.VecCast Air2Lean`; runs no compiler unless --native (`export.sh --check`
# re-exports with the recorded patched compilers).
#
#   check.sh [--native]
#
# For every fixture source: the committed exports match provenance.json; the export of every
# supported Zig version (0.17.0, 0.16.0, 0.15.2, 0.14.1) translates to its retained translation
# (`retained_of` below); each elaborates and its model lines equal the committed native output
# of its version; the proofs check; the negative tests reject and the semantic mutants
# (mutants.py) are killed. `--native` also runs each probe
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
base_path="$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
python3 "$here/test_provenance.py"

# stem, Lean namespace (= retained module name), extra translator arguments.
fixtures=(
  "error_params ErrorParams"
  "vector_casts VectorCasts"
)
versions=(0.17.0 0.16.0 0.15.2 0.14.1)
# The retained translation of a version: LangLongTail/<Ns>-<version>.lean where the version's
# export translates to another text (std code that differs by version, 0.17's bit-cast rules),
# else LangLongTail/<Ns>.lean, the 0.16.0 translation. Each is compared without its profile
# header (line 1), elaborated as the module LangLongTail.<Ns> and run against the native output
# of its version; the proofs are about the 0.16.0 translation.
retained_of() {
  if [ -f "$here/LangLongTail/$1-$2.lean" ]; then echo "$here/LangLongTail/$1-$2.lean"
  else echo "$here/LangLongTail/$1.lean"; fi
}
# Elaborate one version's translation of the namespace in $work/<version>; print its LEAN_PATH.
elaborate() {
  local ns=$1 version=$2 dir="$work/$2"
  mkdir -p "$dir/LangLongTail"
  cp "$(retained_of "$ns" "$version")" "$dir/LangLongTail/$ns.lean"
  LEAN_PATH="$dir:$base_path" "${lean_cmd[@]}" -R "$dir" -o "$dir/LangLongTail/$ns.olean" \
    "$dir/LangLongTail/$ns.lean" >&2
  echo "$dir:$base_path"
}
for entry in "${fixtures[@]}"; do
  read -r stem ns extra <<< "$entry"
  for version in "${versions[@]}"; do
    # shellcheck disable=SC2086 # extra holds whitespace-separated translator flags
    "$translator" "$here/air/$stem/$version" -o "$work/$ns-$version.lean" \
      --namespace "$ns" --prefix "$stem." $extra
    cmp <(tail -n +2 "$work/$ns-$version.lean") <(tail -n +2 "$(retained_of "$ns" "$version")")
    path=$(elaborate "$ns" "$version")
    LEAN_PATH="$path" "${lean_cmd[@]}" --run "$here/Model$ns.lean" "$here/native/$stem-$version.txt"
  done
  if [ -f "$here/Proofs$ns.lean" ]; then
    LEAN_PATH="$work/0.16.0:$base_path" "${lean_cmd[@]}" "$here/Proofs$ns.lean"
  fi
done
python3 "$here/test_cli.py" "$translator"
python3 "$here/mutants.py" "$work/mutants"
if [ "${1:-}" = --native ]; then
  for entry in "${fixtures[@]}"; do
    read -r stem ns _ <<< "$entry"
    ran=0
    for version in "${versions[@]}"; do
      var="AIR2LEAN_ZIG_NATIVE_$(echo "$version" | cut -d. -f1-2 | tr . _)"
      zig=${!var:-}
      [ -n "$zig" ] || continue
      (cd "$here" && "$zig" run -OReleaseSafe "probe_$stem.zig") 2> "$work/$stem-$version.txt"
      LEAN_PATH="$work/$version:$base_path" "${lean_cmd[@]}" --run "$here/Model$ns.lean" \
        "$work/$stem-$version.txt"
      ran=1
    done
    [ "$ran" = 1 ] || { echo "error: --native needs AIR2LEAN_ZIG_NATIVE_<major>_<minor> for at least one version" >&2; exit 1; }
  done
fi
echo "lang-long-tail: ok"
