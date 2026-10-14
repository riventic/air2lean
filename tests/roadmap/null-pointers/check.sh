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
python3 -B scripts/lean-deps.py --build tests/roadmap/null-pointers
here=tests/roadmap/null-pointers
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-null-pointers.XXXXXX")
trap 'rm -rf "$work"' EXIT
case "${1:-}" in
  --export) shift; exec bash "$here/export.sh" --check "$@" ;;
  --native)
    zig=${2:?usage: check.sh --native ZIG}
    version=$("$zig" version)
    [ -f "$here/expected/$version.txt" ] || { echo "no expected/$version.txt: a release Zig of a supported version is required" >&2; exit 1; }
    # `main`, then one variant per `case` (each ends the process with a panic or a fault).
    runs=()
    # The cases are `runCase`'s `comptime eql(u8, case, "<name>")` lines, in order.
    cases=$(grep -o 'comptime eql(u8, case, "[A-Za-z]*")' "$here/nullpointers.zig" | sed 's/.*"\(.*\)")/\1/')
    [ -n "$cases" ] || { echo 'no native cases in nullpointers.zig' >&2; exit 1; }
    for name in main $cases; do
      mkdir -p "$work/$name"
      sed "s/^const case = \"main\";\$/const case = \"$name\";/" "$here/nullpointers.zig" > "$work/$name/nullpointers.zig"
      grep -q "^const case = \"$name\";\$" "$work/$name/nullpointers.zig" || { echo "no case line for $name" >&2; exit 1; }
      "$zig" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} -OReleaseSafe -fno-error-tracing "$work/$name/nullpointers.zig" -femit-bin="$work/$name/native" \
        --cache-dir "$work/cache" --global-cache-dir "$work/global-cache"
      code=0
      "$work/$name/native" > "$work/$name/stdout" 2> "$work/$name/stderr" || code=$?
      [ ! -s "$work/$name/stdout" ] || { echo "unexpected native stdout ($name)" >&2; exit 1; }
      if [ "$name" = main ]; then runs+=("$code" "$work/$name/stderr"); else runs+=("$name" "$code" "$work/$name/stderr"); fi
    done
    python3 "$here/native-transcript.py" "$version" "${runs[@]}" > "$work/transcript.txt"
    grep -v '^model ' "$here/expected/$version.txt" | diff -u - "$work/transcript.txt"
    echo "nullable pointer native: Zig $version, $(wc -l < "$work/transcript.txt") lines match"
    exit 0 ;;
esac
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
lake build ZigLean air2lean ZigLean.Mem.NullLemmas
# Imported theorem definitions are kernel checked with the runtime build above; the
# proof-only storage/projection rules (outside the ZigLean umbrella) are built explicitly.
lake env lean --run tests/roadmap/null-pointers/Generate.lean "$work/generated"
for name in cNull cNonNull allowzeroAddress allowzeroManyAddress cZero cCast cUnwrap cLoad cEqual \
    storeLoad storedIsNull allowzeroStoreLoad nodeNext nodeNextNonnull nodeVal nodeRoundTrip arrayItem \
    cAdd cIndex cElem toOptional fromOptional optStored optStoredIsNull cSlice azMemset azSliceStored \
    azParent unionNullable errorUnionNullable; do
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
  for name in optionalCast fixed; do
    mkdir -p "$work/reject-$version-$name"
    cp "$here/air-reject/$version/reject.$name.json" "$work/reject-$version-$name/"
    if "$translator" "$work/reject-$version-$name" -o "$work/reject.lean" --namespace Rejected > "$work/reject.log" 2>&1; then
      echo "accepted compiler rejection fixture $version $name" >&2; exit 1
    fi
    expected=$([ "$name" = optionalCast ] && echo 'Zig miscompiles it' || echo 'pointer constant without a global')
    grep -q "$expected" "$work/reject.log" || { echo "wrong rejection: $(cat "$work/reject.log")" >&2; exit 1; }
  done
done
python3 -B "$here/test_provenance.py"
echo "nullable pointer gate passed: 30 semantic cases, 1 killed mutant, 4 versions x $(wc -l < "$here/expected/0.17.0.txt" | tr -d ' ') model lines (expected/<version>.txt), 2 compiler rejection roots per version"
