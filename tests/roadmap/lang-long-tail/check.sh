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
python3 -B scripts/lean-deps.py --build tests/roadmap/lang-long-tail
here=tests/roadmap/lang-long-tail
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-lang-long-tail.XXXXXX")
trap 'rm -rf "$work"' EXIT
base_path="$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
python3 "$here/test_provenance.py"

# stem, Lean namespace (the module LangLongTail.<Ns> that Model<Ns>.lean imports), retained-file
# key (LangLongTail/<Key>[-<version>].lean, default <Ns>), extra translator arguments.
fixtures=(
  "error_params ErrorParams"
  "vector_casts VectorCasts"
  "tls_pointers TlsPointers"
  "extern_storage ExternStorage"
  "error_ints ErrorInts"
  "error_ints_w8 ErrorInts ErrorIntsW8"
  "runtime_lanes RuntimeLanes"
  "float_lanes FloatLanes"
)
versions=(0.17.0 0.16.0 0.15.2 0.14.1)
# The retained translation of a version: LangLongTail/<Key>-<version>.lean where the version's
# export translates to another text (std code that differs by version, 0.17's bit-cast rules,
# the error numbering), else LangLongTail/<Key>.lean, the 0.16.0 translation. Each is compared
# without its profile header (line 1), elaborated as the module LangLongTail.<Ns> and run
# against the native output of its version; the proofs are about the 0.16.0 translation.
retained_of() {
  if [ -f "$here/LangLongTail/$1-$2.lean" ]; then echo "$here/LangLongTail/$1-$2.lean"
  else echo "$here/LangLongTail/$1.lean"; fi
}
# Elaborate one version's translation (retained key $1) as LangLongTail.$2 in $work/$1/<version>;
# print its LEAN_PATH.
elaborate() {
  local key=$1 ns=$2 version=$3 dir="$work/$1/$3"
  mkdir -p "$dir/LangLongTail"
  cp "$(retained_of "$key" "$version")" "$dir/LangLongTail/$ns.lean"
  LEAN_PATH="$dir:$base_path" "${lean_cmd[@]}" -R "$dir" -o "$dir/LangLongTail/$ns.olean" \
    "$dir/LangLongTail/$ns.lean" >&2
  echo "$dir:$base_path"
}
# <stem>.reject: `<version> <message>` lines, the versions whose export the translator must
# reject (fail closed), with a fragment of the diagnostic.
rejected() { [ -f "$here/$1.reject" ] && grep -q "^$2 " "$here/$1.reject"; }
# The settings of <stem>.export (export.sh): `module` (the fixture's name prefix), `root_src`
# (the native probe that is also the exported program), `args` (compiler flags of both),
# `native_extra` (more inputs of the native build, a C file and -lc), `only_versions` (the
# versions that compile the source; default all).
load_export() {
  root_src="" module="$1." args="" native_extra="" only_versions=""
  # shellcheck disable=SC1090
  [ -f "$here/$1.export" ] && . "$here/$1.export"
  return 0
}
# The version compiles the loaded fixture's source (`only_versions`).
in_versions() { [ -z "$only_versions" ] || [[ " $only_versions " == *" $1 "* ]]; }
for entry in "${fixtures[@]}"; do
  read -r stem ns key extra <<< "$entry"
  key=${key:-$ns}
  load_export "$stem"
  for version in "${versions[@]}"; do
    in_versions "$version" || continue
    if rejected "$stem" "$version"; then
      message=$(grep "^$version " "$here/$stem.reject" | cut -d' ' -f2-)
      # shellcheck disable=SC2086 # extra holds whitespace-separated translator flags
      if "$translator" "$here/air/$stem/$version" -o "$work/rejected.lean" --namespace "$ns" \
          --prefix "$module" $extra 2> "$work/rejected.err"; then
        echo "error: $stem $version: the translator accepted an export it must reject" >&2; exit 1
      fi
      grep -qF -- "$message" "$work/rejected.err" || {
        echo "error: $stem $version: rejected with another diagnostic:" >&2; cat "$work/rejected.err" >&2; exit 1; }
      continue
    fi
    # shellcheck disable=SC2086 # extra holds whitespace-separated translator flags
    "$translator" "$here/air/$stem/$version" -o "$work/$key-$version.lean" \
      --namespace "$ns" --prefix "$module" $extra
    cmp <(tail -n +2 "$work/$key-$version.lean") <(tail -n +2 "$(retained_of "$key" "$version")")
    path=$(elaborate "$key" "$ns" "$version")
    LEAN_PATH="$path" "${lean_cmd[@]}" --run "$here/Model$ns.lean" "$here/native/$stem-$version.txt"
  done
  # The proofs are about LangLongTail/<Key>.lean: the 0.16.0 translation, or the newest version
  # that compiles the source.
  if [ -f "$here/Proofs$key.lean" ]; then
    proved=0.16.0
    [ -n "$only_versions" ] && proved=${only_versions%% *}
    LEAN_PATH="$work/$key/$proved:$base_path" "${lean_cmd[@]}" "$here/Proofs$key.lean"
  fi
done
python3 "$here/test_cli.py" "$translator"
python3 "$here/mutants.py" "$work/mutants"
# --native: build each probe with the stock compiler of every version that is set, for
# x86_64-linux with the export's flags (the error numbering is per compilation and target, so
# this needs an x86_64-linux host), run it and compare its output with the model.
if [ "${1:-}" = --native ]; then
  # A fixture whose versions have no stock compiler set is skipped (`runtime_lanes` exists for
  # 0.14.1/0.15.2 only); at least one probe must run.
  ran=0
  for entry in "${fixtures[@]}"; do
    read -r stem ns key _ <<< "$entry"
    key=${key:-$ns}
    load_export "$stem"
    for version in "${versions[@]}"; do
      in_versions "$version" || continue
      var="AIR2LEAN_ZIG_NATIVE_$(echo "$version" | cut -d. -f1-2 | tr . _)"
      zig=${!var:-}
      [ -n "$zig" ] || continue
      rejected "$stem" "$version" && continue
      # shellcheck disable=SC2086 # args, native_extra and the Rosetta link flags (scripts/rosetta.sh) hold whitespace-separated flags
      (cd "$here" && "$zig" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} -OReleaseSafe -fno-error-tracing -target x86_64-linux \
        -mcpu=baseline $args "${root_src:-probe_$stem.zig}" $native_extra \
        -femit-bin="$work/probe-$stem-$version")
      "$work/probe-$stem-$version" 2> "$work/$stem-$version.txt"
      LEAN_PATH="$work/$key/$version:$base_path" "${lean_cmd[@]}" --run "$here/Model$ns.lean" \
        "$work/$stem-$version.txt"
      ran=1
    done
  done
  [ "$ran" = 1 ] || { echo "error: --native needs AIR2LEAN_ZIG_NATIVE_<major>_<minor> for at least one version" >&2; exit 1; }
fi
echo "lang-long-tail: ok"
