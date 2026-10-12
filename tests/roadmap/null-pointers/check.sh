#!/usr/bin/env bash
# L05 gate: offline AIR/checker/emitter cases and a mutant (Generate.lean), then the committed
# compiler exports of every supported version (air/<version>, provenance.json): each translates,
# its model run on the native `main`'s inputs prints expected/<version>.txt, and the compiler
# rejection roots (air-reject/<version>) stay rejected.
#   check.sh                 the gate above (needs `lake`; no compiler)
#   check.sh --export [V..]  export.sh --check: a fresh export equals the committed one
#                            (AIR2LEAN_ZIG_AIR: directory of zig-air-<version> compilers)
#   check.sh --native ZIG    run nullpointers.zig with a stock Zig on this host and compare its
#                            transcript (native-transcript.py) with expected/<version>.txt
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/null-pointers
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-null-pointers.XXXXXX")
trap 'rm -rf "$work"' EXIT
case "${1:-}" in
  --export) shift; exec bash "$here/export.sh" --check "$@" ;;
  --native)
    zig=${2:?usage: check.sh --native ZIG}
    version=$("$zig" version)
    cp "$here/nullpointers.zig" "$work/"
    "$zig" build-exe -OReleaseSafe -fno-error-tracing "$work/nullpointers.zig" -femit-bin="$work/native" \
      --cache-dir "$work/cache" --global-cache-dir "$work/global-cache"
    code=0
    "$work/native" > "$work/native.stdout" 2> "$work/native.txt" || code=$?
    [ ! -s "$work/native.stdout" ] || { echo 'unexpected native stdout' >&2; exit 1; }
    python3 "$here/native-transcript.py" "$version" "$code" "$work/native.txt" > "$work/transcript.txt"
    grep -v '^model ' "$here/expected/$version.txt" | diff -u - "$work/transcript.txt"
    echo "nullable pointer native: Zig $version, $(wc -l < "$work/transcript.txt") lines match"
    exit 0 ;;
esac
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo "build the translator first (lake build air2lean)" >&2; exit 1; }
lake build ZigLean ZigLean.Mem.NullLemmas
# Imported theorem definitions are kernel checked with the runtime build above; the
# proof-only storage/projection rules (outside the ZigLean umbrella) are built explicitly.
lake env lean --run tests/roadmap/null-pointers/Generate.lean "$work/generated"
for name in cNull cNonNull allowzeroAddress allowzeroManyAddress cZero cCast cUnwrap cLoad cEqual \
    storeLoad storedIsNull allowzeroStoreLoad nodeNext nodeNextNonnull nodeVal nodeRoundTrip arrayItem \
    cAdd cIndex cElem toOptional fromOptional; do
  [ -f "$work/generated/$name.lean" ] || { echo "missing semantic fixture $name" >&2; exit 1; }
  lake env lean "$work/generated/$name.lean"
done
# Invert the emitted null predicate; the fresh baseline must detect a false proposition.
python3 - "$work/generated/cNull.lean" "$work/mutant.lean" <<'PY'
from pathlib import Path
import runpy
import sys
helpers = runpy.run_path('tests/roadmap/null-pointers/classify_mutant.py')
source = helpers['read_bounded'](Path(sys.argv[1]))
Path(sys.argv[2]).write_text(helpers['make_mutant'](source))
PY
mutation_status=0
lake env lean "$work/mutant.lean" >"$work/mutation.log" 2>&1 || mutation_status=$?
python3 tests/roadmap/null-pointers/classify_mutant.py "$mutation_status" \
  "$work/mutation.log" "$work/mutant.lean" "$work/generated/cNull.lean"
for version in 0.17.0 0.16.0 0.15.2 0.14.1; do
  "$translator" "$here/air/$version" -o "$work/Gen-$version.lean" --namespace NullableNative --prefix 'nullpointers.'
  cat "$here/Runner.lean" >> "$work/Gen-$version.lean"
  lake env lean --run "$work/Gen-$version.lean" > "$work/lean-$version.txt"
  diff -u "$here/expected/$version.txt" "$work/lean-$version.txt"
  for name in optional fixed; do
    mkdir -p "$work/reject-$version-$name"
    cp "$here/air-reject/$version/reject.$name.json" "$work/reject-$version-$name/"
    if "$translator" "$work/reject-$version-$name" -o "$work/reject.lean" --namespace Rejected > "$work/reject.log" 2>&1; then
      echo "accepted compiler rejection fixture $version $name" >&2; exit 1
    fi
    expected=$([ "$name" = optional ] && echo 'separate null flag' || echo 'pointer constant without a global')
    grep -q "$expected" "$work/reject.log" || { echo "wrong rejection: $(cat "$work/reject.log")" >&2; exit 1; }
  done
done
python3 -B "$here/test_provenance.py"
echo "nullable pointer gate passed: 27 semantic cases, 1 killed mutant, 4 versions x 27 model lines (expected/<version>.txt), 2 compiler rejection roots per version"
