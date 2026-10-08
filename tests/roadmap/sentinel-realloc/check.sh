#!/usr/bin/env bash
# M04 sentinel reallocation gate. Root's global guard serializes all compiler execution.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
here=tests/roadmap/sentinel-realloc
zig_air=${AIR2LEAN_SENTINEL_ZIG_AIR:?set patched Zig 0.16.0 compiler}
zig_native=${AIR2LEAN_SENTINEL_ZIG_NATIVE:?set shipping Zig 0.16.0 compiler}
translator=${AIR2LEAN_SENTINEL_TRANSLATOR:-"$repo/.lake/build/bin/air2lean"}
[ "$("$zig_air" version)" = '0.16.0' ]
[ "$("$zig_native" version)" = '0.16.0' ]
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-sentinel-realloc.XXXXXX")
case "${AIR2LEAN_SENTINEL_KEEP_WORK:-0}" in
  0) trap 'rm -rf "$work"' EXIT ;;
  1) trap 'echo "retained sentinel realloc artifacts: $work"' EXIT ;;
  *) rm -rf "$work"; echo 'AIR2LEAN_SENTINEL_KEEP_WORK must be 0 or 1' >&2; exit 2 ;;
esac
lake build air2lean ZigLean ZigLean.Sep.SentinelRealloc ZigLean.Sep.RawAlloc
# Kernel-checked rules, executable model/raw-contract regressions and translator admission.
lake env lean --run "$here/Check.lean"
lake env lean --run "$here/Pipeline.lean"
# Model observations (hand-written ZigLean clients) for the native comparison.
{ echo 'import ZigLean.Sep.SentinelRealloc'; cat "$here/Scenarios.lean" "$here/Model.lean"; } > "$work/Model.lean"
lake env lean --run "$work/Model.lean" > "$work/model.txt"
cp "$here"/{source,native}.zig "$work/"
"$zig_native" build-exe -OReleaseSafe -mcpu=baseline -femit-bin="$work/native" --dep common \
  -Mroot="$work/native.zig" -Mcommon=tests/diff/common.zig --cache-dir "$work/native-cache"
"$work/native" > "$work/native.stdout" 2> "$work/native.txt"
[ ! -s "$work/native.stdout" ]
[ "$(wc -l < "$work/native.txt" | tr -d ' ')" = 9 ]
diff -u "$work/native.txt" "$work/model.txt"
# Zig 0.16.0 itself rejects `realloc` of a sentinel slice: the absorbed buffer is required.
printf 'const std = @import("std");\nexport fn bad(a: *const std.mem.Allocator, s: [*:0]u8, n: usize) void {\n    _ = a.realloc(s[0..n :0], n + 1) catch {};\n}\n' > "$work/direct.zig"
if "$zig_native" build-obj -fno-emit-bin "$work/direct.zig" --cache-dir "$work/native-cache" 2> "$work/direct.txt"; then
  echo 'direct sentinel realloc unexpectedly compiled' >&2; exit 1
fi
grep -q "destination pointer requires '0' sentinel" "$work/direct.txt"
# Fresh source export: realloc is a recognized three-argument call; translation emits the model.
mkdir "$work/air"
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER='source.make,source.append,source.resize,source.release' \
  "$zig_air" build-exe -fno-emit-bin -OReleaseSafe -fno-error-tracing -mcpu=baseline --dep common \
    -Mroot="$work/native.zig" -Mcommon=tests/diff/common.zig --cache-dir "$work/air-cache"
python3 -I -B - "$work/air" <<'PY'
import json, sys
from pathlib import Path
files = {f['name']: f for p in Path(sys.argv[1]).glob('*.json') for f in [json.loads(p.read_text())]}
assert set(files) == {'source.' + n for n in ('make', 'append', 'resize', 'release')}, sorted(files)
calls = []
def walk(x):
    if isinstance(x, dict):
        if x.get('tag') == 'call' and x.get('callee', {}).get('func', '').startswith('mem.Allocator.realloc__anon_'):
            calls.append(x)
        for v in x.values(): walk(v)
    elif isinstance(x, list):
        for v in x: walk(v)
for name in ('append', 'resize'):
    calls.clear(); walk(files['source.' + name]['body'])
    assert len(calls) == 1 and len(calls[0]['args']) == 3, name
    assert files['source.' + name]['zig_version'] == '0.16.0'
PY
"$translator" "$work/air" -o "$work/Gen.lean" --namespace SentinelRealloc --prefix 'source.'
grep -q 'Zig.Allocator.realloc' "$work/Gen.lean"
grep -q 'Zig.Allocator.allocSentinel' "$work/Gen.lean"
grep -q 'Zig.Allocator.freeSentinel' "$work/Gen.lean"
{ echo 'import ZigLean.Sep.SentinelRealloc'; cat "$work/Gen.lean" "$here/Scenarios.lean" "$here/Runner.lean"; } > "$work/Runtime.lean"
lake env lean --run "$work/Runtime.lean" > "$work/lean.txt"
diff -u "$work/native.txt" "$work/lean.txt"
echo 'sentinel realloc gate: Zig 0.16.0 native64 ReleaseSafe; 9 native/model/generated observations; direct sentinel realloc rejected by Zig; 6 translator rejections'
