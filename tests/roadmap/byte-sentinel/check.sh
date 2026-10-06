#!/usr/bin/env bash
# Root's global guard serializes all compiler execution, including this gate.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
zig_air=${AIR2LEAN_SENTINEL_ZIG_AIR:?set patched Zig 0.16.0 compiler}
zig_native=${AIR2LEAN_SENTINEL_ZIG_NATIVE:?set shipping Zig 0.16.0 compiler}
translator=${AIR2LEAN_SENTINEL_TRANSLATOR:-"$repo/.lake/build/bin/air2lean"}
[ "$("$zig_air" version)" = '0.16.0' ]
[ "$("$zig_native" version)" = '0.16.0' ]
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-byte-sentinel.XXXXXX")
case "${AIR2LEAN_SENTINEL_KEEP_WORK:-0}" in
  0) trap 'rm -rf "$work"' EXIT ;;
  1) trap 'echo "retained fresh byte sentinel artifacts: $work"' EXIT ;;
  *) rm -rf "$work"; echo 'AIR2LEAN_SENTINEL_KEEP_WORK must be 0 or 1' >&2; exit 2 ;;
esac
lake build air2lean ZigLean ZigLean.Sep.Sentinel
lake env lean --run tests/roadmap/byte-sentinel/Pipeline.lean
cp tests/roadmap/byte-sentinel/{source,native,overflow}.zig "$work/"
mkdir "$work/air"
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER='source.makeZero,source.makeByte,source.releaseZero,source.releaseByte' \
  "$zig_air" build-exe -fno-emit-bin -OReleaseSafe -fno-error-tracing --dep common \
    -Mroot="$work/native.zig" -Mcommon=tests/diff/common.zig --cache-dir "$work/air-cache"
python3 - "$work/air" <<'PY'
import json, sys
from pathlib import Path
files = {f['name']: f for p in Path(sys.argv[1]).glob('*.json') for f in [json.loads(p.read_text())]}
assert set(files) == {'source.' + n for n in ('makeZero','makeByte','releaseZero','releaseByte')}
for name, sentinel in [('makeZero','0'), ('makeByte','42')]:
    f = files['source.'+name]
    assert f['zig_version'] == '0.16.0'
    p = f['types'][f['types'][f['ret']]['payload']]
    assert p['k'] == 'ptr' and p['size'] == 'slice' and p['sentinel']
    assert p.get('sentinel_byte') == sentinel, 'missing exact exported comptime sentinel'
    assert any(i.get('callee', {}).get('func','').startswith('mem.Allocator.allocSentinel__anon_') for i in f['body'])
PY
"$translator" "$work/air" -o "$work/Gen.lean" --namespace ByteSentinel --prefix 'source.'
# Source qualification must lower both allocation and whole-block sentinel free.
python3 - "$work/Gen.lean" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
assert 'Zig.Allocator.allocSentinel' in s and '(42#8)' in s and '(0#8)' in s
assert 'Zig.Allocator.freeSentinel' in s
PY
cat tests/roadmap/byte-sentinel/Runner.lean >> "$work/Gen.lean"
lake env lean --run "$work/Gen.lean" > "$work/lean.txt"
"$zig_native" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$work/native" --dep common \
  -Mroot="$work/native.zig" -Mcommon=tests/diff/common.zig --cache-dir "$work/native-cache"
"$work/native" > "$work/native.stdout" 2> "$work/native.txt"
[ ! -s "$work/native.stdout" ]
[ "$(wc -l < "$work/lean.txt" | tr -d ' ')" = 13 ]
diff -u "$work/native.txt" "$work/lean.txt"
"$zig_native" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$work/overflow" --dep common \
  -Mroot="$work/overflow.zig" -Mcommon=tests/diff/common.zig --cache-dir "$work/native-cache"
"$work/overflow" > "$work/overflow.stdout" 2> "$work/overflow.txt"
[ ! -s "$work/overflow.stdout" ]
printf 'overflow-before-allocation\n' > "$work/overflow.expected"
diff -u "$work/overflow.expected" "$work/overflow.txt"
python3 tests/roadmap/byte-sentinel/mutations.py
echo 'byte sentinel gate: Zig 0.16.0 native64 ReleaseSafe; 13 exact policy/ownership observations; overflow panic; 10 parsed rejections; 3 normalized rejections; 2 kernel mutants'
