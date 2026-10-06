#!/usr/bin/env bash
# ROOT's existing global resource lane serializes this actual qualification gate.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo"
patched=${AIR2LEAN_REMAP_ZIG_AIR:?bind existing patched Linux Zig16}
stock=${AIR2LEAN_REMAP_ZIG_NATIVE:?bind existing shipping Linux Zig16}
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-remap.XXXXXX")
echo "retaining byte-remap artifacts: $work"
sha256sum ZigLean/Mem/Basic.lean ZigLean/Mem/Alloc.lean ZigLean/Sep/Remap.lean \
  tests/roadmap/resize-remap/{source,native}.zig \
  tests/roadmap/resize-remap/{Check,Kernel,Runner}.lean > "$work/source.sha256"
python3 -I -B - <<'PY_HASH'
from pathlib import Path
from hashlib import sha256
for name, expected in [
    ('source.zig', 'd1be01de2382a853f169b04b12e4e0c257de7a62dd0cef9e73b42370a8cc5a38'),
    ('native.zig', 'e8416f81d5d787f3011b4d9638989a0db4aa0ebb860617e161557a59401b5aa1')]:
    assert sha256((Path('tests/roadmap/resize-remap')/name).read_bytes()).hexdigest() == expected
PY_HASH
lake build air2lean ZigLean.Sep.Remap
lake env lean tests/roadmap/resize-remap/Kernel.lean
lake env lean --run tests/roadmap/resize-remap/Check.lean > "$work/model-check.txt"
cp tests/roadmap/resize-remap/{source,native}.zig "$work/"
mkdir "$work/air"
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER='source.exercise' \
  "$patched" build-exe -fno-emit-bin -OReleaseSafe -fno-error-tracing -mcpu=baseline \
  "$work/native.zig" --cache-dir "$work/air-cache"
python3 -I -B - "$work/air" <<'PY'
import json,sys
from pathlib import Path
fs=[json.loads(p.read_text()) for p in Path(sys.argv[1]).glob('*.json')]
assert len(fs)==1 and fs[0]['name']=='source.exercise' and fs[0]['schema']==12 and fs[0]['zig_version']=='0.16.0'
calls=[]
def walk(x):
    if isinstance(x,dict):
        if x.get('tag')=='call' and x.get('callee',{}).get('func','').startswith('mem.Allocator.remap__anon_'): calls.append(x)
        for c in x.values():walk(c)
    elif isinstance(x,list):
        for c in x:walk(c)
walk(fs[0]['body'])
assert len(calls)==1 and len(calls[0]['args'])==3
PY
.lake/build/bin/air2lean "$work/air" -o "$work/Gen.lean" --namespace RemapProbe --prefix 'source.'
python3 -I -B scripts/normalize-generated.py report "$work/Gen.lean" "$work/air" "$work/translation.json"
cp "$work/Gen.lean" "$work/Runtime.lean"
cat tests/roadmap/resize-remap/Runner.lean >> "$work/Runtime.lean"
lake env lean --run "$work/Runtime.lean" > "$work/model.txt"
"$stock" build-exe -OReleaseSafe -fno-error-tracing -mcpu=baseline -femit-bin="$work/native" \
  "$work/native.zig" --cache-dir "$work/native-cache"
"$work/native" > "$work/native.stdout" 2> "$work/native.jsonl"
python3 -I -B - "$work" <<'PY'
import json,sys
from pathlib import Path
p=Path(sys.argv[1]);assert not (p/'native.stdout').read_bytes()
rows=[json.loads(x) for x in (p/'native.jsonl').read_text().splitlines()]
expected=[dict(mode=m,result=r,prefix_preserved=True,frame_preserved=True,old_live_after_remap=l,live_after_cleanup=0)
          for m,r,l in [('in_place',101,True),('moved',201,False),('failed',301,True)]]
assert rows==expected
assert (p/'model.txt').read_text().splitlines()==['101','201','301']
print('three exact byte-remap source/native/model observations, restricted kernel rules and representation/lifetime/frame regressions passed')
PY

sha256sum --check "$work/source.sha256" > "$work/source-after.txt"
