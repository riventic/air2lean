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
lake build ZigLean air2lean
# Imported theorem definitions are kernel checked with the runtime build above.
lake env lean --run tests/roadmap/null-pointers/Generate.lean "$work/generated"
for name in cNull cNonNull allowzeroAddress allowzeroManyAddress cZero cCast cUnwrap cLoad cEqual; do
  [ -f "$work/generated/$name.lean" ] || { echo "missing semantic fixture $name" >&2; exit 1; }
  lake env lean "$work/generated/$name.lean"
done
# Invert the emitted null predicate; the fresh baseline must detect a false proposition.
python3 - "$work/generated/cNull.lean" "$work/mutant.lean" <<'PY'
from pathlib import Path
import sys
source = Path(sys.argv[1]).read_text()
assert 'Zig.ptrIsNull' in source, 'null-predicate mutation did not target emitted code'
source = source.replace('Zig.ptrIsNull', 'nullableMutation')
source = source.replace('import ZigLean', 'import ZigLean\nprivate def nullableMutation (p : Zig.Ptr) : Zig.MemM Bool := do pure (!(← Zig.ptrIsNull p))', 1)
Path(sys.argv[2]).write_text(source)
PY
if lake env lean "$work/mutant.lean" >"$work/mutation.log" 2>&1; then
  echo 'null-predicate mutant survived' >&2; exit 1
fi
python3 - "$work/mutation.log" <<'PY'
from pathlib import Path
import sys
message = Path(sys.argv[1]).read_text()
assert 'false' in message and 'decide' in message, 'mutation failed without the intended semantic assertion failure: '+message
PY
cp tests/roadmap/null-pointers/nullpointers.zig "$work/nullpointers.zig"
mkdir "$work/air"
ZIG_AIR_JSON_DIR="$work/air" \
ZIG_AIR_JSON_FILTER='nullpointers.cNull,nullpointers.allowzeroAddress,nullpointers.allowzeroManyAddress,nullpointers.castChecked,nullpointers.cRead,nullpointers.cZero' \
  "$zig_air" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$work/nullpointers.zig" --cache-dir "$work/air-cache"
python3 - "$work/air" "$version" <<'PY'
import json,sys
from pathlib import Path
files = [json.loads(p.read_text()) for p in Path(sys.argv[1]).glob('*.json')]
assert {f['name'] for f in files} == {'nullpointers.'+n for n in ('cNull','allowzeroAddress','allowzeroManyAddress','castChecked','cRead','cZero')}
assert all(f['zig_version'] == sys.argv[2] for f in files)
PY
"$translator" "$work/air" -o "$work/Gen.lean" --namespace NullableNative --prefix 'nullpointers.'
cat tests/roadmap/null-pointers/Runner.lean >> "$work/Gen.lean"
lake env lean --run "$work/Gen.lean" > "$work/lean.txt"
"$zig_native" build-exe -OReleaseSafe -fno-error-tracing "$work/nullpointers.zig" -femit-bin="$work/native" --cache-dir "$work/native-cache"
"$work/native" > "$work/native.stdout" 2> "$work/native.txt"
[ ! -s "$work/native.stdout" ] || { echo 'unexpected native stdout' >&2; exit 1; }
diff -u "$work/native.txt" "$work/lean.txt"
cp tests/roadmap/null-pointers/reject.zig "$work/reject.zig"
mkdir "$work/rejected-air"
ZIG_AIR_JSON_DIR="$work/rejected-air" ZIG_AIR_JSON_FILTER='reject.' \
  "$zig_air" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$work/reject.zig" --cache-dir "$work/reject-cache"
for name in stored fixed; do
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
expected = 'null-byte encoding' if sys.argv[2] == 'stored' else 'pointer constant without a global'
assert expected in message, 'wrong rejection: '+message
PY
done
echo "nullable pointer gate passed: Zig $version; 9 semantic cases, 1 killed mutant, 8 native observations, 2 compiler rejection roots"
