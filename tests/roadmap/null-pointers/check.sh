#!/usr/bin/env bash
# Serial source/export/check/emission/proof/native-diff/mutation gate for L05's fragment.
# The root validation queue supplies one matching toolchain pair at a time.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
zig_air=${AIR2LEAN_NULL_ZIG_AIR:?set matching patched AIR compiler}
zig_native=${AIR2LEAN_NULL_ZIG_NATIVE:?set matching shipping native compiler}
version=${AIR2LEAN_NULL_ZIG_VERSION:?set expected Zig version}
translator=${AIR2LEAN_NULL_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
case "$zig_air" in /*) ;; *) zig_air="$repo_root/$zig_air" ;; esac
case "$zig_native" in /*) ;; *) zig_native=$(command -v "$zig_native");; esac
[ "$("$zig_air" version)" = "$version" ] || { echo 'AIR compiler version mismatch' >&2; exit 1; }
[ "$("$zig_native" version)" = "$version" ] || { echo 'native compiler version mismatch' >&2; exit 1; }
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-null-pointers.XXXXXX")
trap 'rm -rf "$work"' EXIT
lake build ZigLean air2lean ZigLean.Mem.NullLemmas
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
cp tests/roadmap/null-pointers/nullpointers.zig "$work/nullpointers.zig"
# Every exported root of nullpointers.zig (Runner.lean prints the same lines as its main).
native_roots="cNull allowzeroAddress allowzeroManyAddress castChecked cRead cZero storeLoad storedIsNull allowzeroStoreLoad nodeNext nodeVal nodeRoundTrip arrayItem cAdd cSub cIndex cElem nextPtr valPtr allowzeroNextPtr allowzeroAdd toOptional fromOptional addIsNull"
native_filter=$(printf 'nullpointers.%s,' $native_roots); native_filter=${native_filter%,}
mkdir "$work/air"
ZIG_AIR_JSON_DIR="$work/air" \
ZIG_AIR_JSON_FILTER="$native_filter" \
  "$zig_air" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$work/nullpointers.zig" --cache-dir "$work/air-cache"
python3 - "$work/air" "$version" $native_roots <<'PY'
import json,sys
from pathlib import Path
files = [json.loads(p.read_text()) for p in Path(sys.argv[1]).glob('*.json')]
assert {f['name'] for f in files} == {'nullpointers.'+n for n in sys.argv[3:]}
assert all(f['zig_version'] == sys.argv[2] for f in files)
PY
"$translator" "$work/air" -o "$work/Gen.lean" --namespace NullableNative --prefix 'nullpointers.'
cat tests/roadmap/null-pointers/Runner.lean >> "$work/Gen.lean"
lake env lean --run "$work/Gen.lean" > "$work/lean.txt"
"$zig_native" build-exe -OReleaseSafe -fno-error-tracing "$work/nullpointers.zig" -femit-bin="$work/native" --cache-dir "$work/native-cache"
"$work/native" > "$work/native.stdout" 2> "$work/native.txt"
[ ! -s "$work/native.stdout" ] || { echo 'unexpected native stdout' >&2; exit 1; }
# Zig 0.14.1/0.15.2 type a field pointer of a C/allowzero base as a nonnullable `*T`; the model
# keeps address zero out of it (`Zig.ptrProjectNonnull`, conservative), where 0.16.0 keeps
# `allowzero` and the model yields the native address zero. Only those two observations differ.
case "$version" in
  0.14.*|0.15.*) sed -e 's/^nextPtr 0 /nextPtr illegal /' -e 's/^allowzeroNextPtr 0$/allowzeroNextPtr illegal/' \
    "$work/native.txt" > "$work/native-expected.txt" ;;
  *) cp "$work/native.txt" "$work/native-expected.txt" ;;
esac
diff -u "$work/native-expected.txt" "$work/lean.txt"
[ "$(wc -l < "$work/lean.txt")" -eq 25 ] || { echo 'expected 25 observation lines' >&2; exit 1; }
cp tests/roadmap/null-pointers/reject.zig "$work/reject.zig"
mkdir "$work/rejected-air"
ZIG_AIR_JSON_DIR="$work/rejected-air" ZIG_AIR_JSON_FILTER='reject.' \
  "$zig_air" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$work/reject.zig" --cache-dir "$work/reject-cache"
for name in optional fixed; do
  mkdir "$work/reject-$name"
  [ -f "$work/rejected-air/reject.$name.json" ] || { echo "missing compiler rejection fixture $name" >&2; exit 1; }
  cp "$work/rejected-air/reject.$name.json" "$work/reject-$name/"
  if "$translator" "$work/reject-$name" -o "$work/reject-$name.lean" --namespace Rejected > "$work/reject-$name.log" 2>&1; then
    echo "accepted compiler rejection fixture $name" >&2; exit 1
  fi
  python3 - "$work/reject-$name.log" "$name" <<'PY'
from pathlib import Path
import sys
message = Path(sys.argv[1]).read_text()
expected = 'separate null flag' if sys.argv[2] == 'optional' else 'pointer constant without a global'
assert expected in message, 'wrong rejection: '+message
PY
done
echo "nullable pointer gate passed: Zig $version; 27 semantic cases, 1 killed mutant, 25 native observation lines from 24 exported roots, 2 compiler rejection roots"
