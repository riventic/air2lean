#!/usr/bin/env bash
# Dispatch-loop template: tactic regressions, and the proof about a fresh compiler-exported
# tokenizer state machine. Run only under the root's serialized compiler guard.
#   --template-only  tactic regressions only (no Zig)
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
native=1
case "$#" in
  0) ;;
  1) case "$1" in
    --template-only) native=0 ;;
    *) echo 'usage: dispatch-templates/check.sh [--template-only]' >&2; exit 2 ;;
  esac ;;
  *) echo 'too many arguments' >&2; exit 2 ;;
esac
here=tests/roadmap/dispatch-templates
lake build ZigLean.Sep.DispatchTemplate ZigLean.Range air2lean
lake env lean "$here/Template.lean"
if [ "$native" = 0 ]; then echo 'dispatch template regressions passed'; exit 0; fi

version=${AIR2LEAN_DISPATCH_ZIG_VERSION:-0.16.0}
zig_air=${AIR2LEAN_DISPATCH_ZIG_AIR:-"$repo_root/zig-air-$version/bin/zig"}
zig_stock=${AIR2LEAN_DISPATCH_ZIG_STOCK:-zig}
# The proof names the 0.16.0 translation's loop (`loop10`/`dispatchValue10`).
[ "$version" = 0.16.0 ] || { echo "dispatch-template proof is qualified on 0.16.0 only, not $version" >&2; exit 2; }
[ "$("$zig_stock" version)" = "$version" ] || { echo 'stock compiler version mismatch' >&2; exit 1; }
[ "$("$zig_air" version)" = "$version" ] || { echo 'exporter version mismatch' >&2; exit 1; }
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-dispatch-templates.XXXXXX")
case "${AIR2LEAN_DISPATCH_KEEP_WORK:-0}" in
  0) trap 'rm -rf "$work"' EXIT ;;
  1) trap 'echo "retained dispatch-template artifacts: $work"' EXIT ;;
  *) rm -rf "$work"; echo 'AIR2LEAN_DISPATCH_KEEP_WORK must be 0 or 1' >&2; exit 2 ;;
esac

# Native behavior of the very source that is exported.
"$zig_stock" test "$here/source.zig" -OReleaseSafe
mkdir -p "$work/air" "$work/gen"
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER=source. "$zig_air" \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$here/source.zig"
python3 -B "$here/native_checks.py" "$work/air" "$version" "$work/checks.lean" "$work/mutants"

# Malformed dispatch targets in the real AIR are rejected before emission.
for mutant in "$work/mutants/"*/; do
  target=$(cat "$mutant/target")
  rm "$mutant/target"
  if .lake/build/bin/air2lean "$mutant" -o "$work/mutant.lean" --namespace Tok --prefix source. \
      2> "$work/mutant.err"; then
    echo "accepted a dispatch to $target ($mutant)" >&2; exit 1
  fi
  grep -q "target $target is not an enclosing loop-switch" "$work/mutant.err" ||
    { echo "wrong diagnostic for $mutant:" >&2; cat "$work/mutant.err" >&2; exit 1; }
done

.lake/build/bin/air2lean "$work/air" -o "$work/gen/DispatchTokenizer.lean" --namespace Tok --prefix source.
cat "$work/checks.lean" >> "$work/gen/DispatchTokenizer.lean"
lake env lean -R "$work/gen" -o "$work/gen/DispatchTokenizer.olean" "$work/gen/DispatchTokenizer.lean"
LEAN_PATH="$work/gen:$(lake env printenv LEAN_PATH)" lake env lean "$here/TokenizerProof.lean"
echo "dispatch template regressions and generated tokenizer proof passed: Zig $version"
