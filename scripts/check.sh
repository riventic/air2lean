#!/usr/bin/env bash
# Full air2lean pipeline for each examples/<ex>/<ex>.zig:
#   1. dump AIR-JSON with the patched compiler (zig-patch/) and check it against the golden files
#   2. translate that AIR to Lean (`lake exe air2lean`)
#   3. build the generated Lean
#   4. differential-test it against the real Zig behaviour (scripts/diff.sh)
#
# Usage: check.sh
# Env:
#   AIR2LEAN_ZIG_VERSION  Zig version: selects the golden dir and the default patched zig. Default: 0.15.2
#   AIR2LEAN_ZIG_AIR      Patched zig (zig-patch/build.sh output). Default: zig-air-$AIR2LEAN_ZIG_VERSION/bin/zig
#   AIR2LEAN_CI           If 1: fail when a committed Proofs/<Ex>/Gen.lean differs from the new
#                         translator output.
#   AIR2LEAN_EXAMPLES     Space-separated example dirs to check. Default: every dir in examples/.
#                         Also forwarded (via the environment) to scripts/diff.sh at the end.
#   AIR2LEAN_DIFF         If 0: skip step 4. For a Zig version whose std cannot build the diff
#                         harness; the stale-Gen.lean check (AIR2LEAN_CI=1) then shows that the
#                         translation equals the one that the diff test checks.
#
# examples/<ex>/translate.args, if present: one line of extra `lake exe air2lean` arguments for
# that example (e.g. `--float-semantics compiler-rt`; docs/generated-code.md). Opt-in per
# example, since most examples never need a non-default flag.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

zig_version=${AIR2LEAN_ZIG_VERSION:-0.15.2}
zig_air=${AIR2LEAN_ZIG_AIR:-zig-air-$zig_version/bin/zig}
[ -x "$zig_air" ] || {
  echo "error: patched zig not found/executable at $zig_air" >&2
  echo "hint: build one with zig-patch/build.sh $zig_version (see zig-patch/README.md)" >&2
  exit 1
}

examples=${AIR2LEAN_EXAMPLES:-$(cd examples && for d in */; do printf '%s ' "${d%/}"; done)}

for ex in $examples; do
  # <Ex>: the namespace/dir form of <ex> (layout convention) — first letter uppercased. No
  # `${ex^}`: that's a bash-4 operator, and macOS ships bash 3.2.
  Ex="$(printf '%s' "${ex:0:1}" | tr '[:lower:]' '[:upper:]')${ex:1}"
  golden_dir="tests/golden/$zig_version/$ex/air"
  air_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-check.XXXXXX")
  trap 'rm -rf "$air_dir"' EXIT

  echo "== $ex: dumping AIR ==" >&2
  ZIG_AIR_JSON_DIR="$air_dir" ZIG_AIR_JSON_FILTER="$ex." "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "examples/$ex/$ex.zig"

  echo "== $ex: checking against golden ($golden_dir) ==" >&2
  # diff exits 1 on a difference and 2 on an error (e.g. a missing golden dir): both fail.
  if ! diff_output=$(diff -r "$golden_dir" "$air_dir" 2>&1); then
    echo "error: AIR output for $ex does not match $golden_dir" >&2
    echo "$diff_output" >&2
    echo "hint: if only the golden files are stale (a deliberate exporter change), regenerate: cp $air_dir/* $golden_dir/" >&2
    exit 1
  fi

  echo "== $ex: translating to Lean ==" >&2
  translate_args=""
  if [ -f "examples/$ex/translate.args" ]; then
    translate_args=$(cat "examples/$ex/translate.args")
  fi
  lake exe air2lean "$air_dir" -o "Proofs/$Ex/Gen.lean" --namespace "$Ex" --prefix "$ex." $translate_args

  # `git status` against HEAD: also catches a Gen.lean that is only staged or never added.
  if [ "${AIR2LEAN_CI:-0}" = 1 ] && [ -n "$(git status --porcelain -- "Proofs/$Ex/Gen.lean")" ]; then
    git status --short -- "Proofs/$Ex/Gen.lean" >&2
    git diff HEAD -- "Proofs/$Ex/Gen.lean" >&2 || true
    echo "error: committed Proofs/$Ex/Gen.lean differs from the translator output; commit the new file" >&2
    exit 1
  fi

  rm -rf "$air_dir"
  trap - EXIT
done

echo "== building Lean ==" >&2
lake build

if [ "${AIR2LEAN_DIFF:-1}" = 0 ]; then
  echo "== differential testing: skipped (AIR2LEAN_DIFF=0) ==" >&2
  exit 0
fi

echo "== differential testing ==" >&2
exec scripts/diff.sh
