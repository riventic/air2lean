"""Seeded loop fixture: `sumUpTo(n)` AIR derived from the committed pointers.sumTo golden.

`sumUpTo(n: u32) u32 { var acc: u32 = 0; var i: u32 = 0; while (i < n) : (i += 1) acc += i; return acc; }`
The correct variant keeps `i < n`; the buggy variant is the classic off-by-one `i <= n`. Both carry
the additive `src`/`column` provenance so source spans can be checked without a patched Zig.
"""
import copy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
GOLDEN = ROOT/'tests/golden/pointers/air/pointers.sumTo.json'
DECL_LINE = 10  # `export fn sumUpTo` in the notional loops.zig


def find(body, ident):
    for inst in body:
        if inst.get('id') == ident: return inst, body
        for key in ('body', 'then', 'else'):
            if isinstance(inst.get(key), list):
                hit = find(inst[key], ident)
                if hit: return hit
    return None


def air(buggy):
    doc = copy.deepcopy(json.loads(GOLDEN.read_text()))
    doc['name'] = 'loops.sumUpTo'
    doc['src'] = dict(file='loops.zig', module='root', decl_line=DECL_LINE)
    doc['ret'] = 0
    doc['types'][3]['child'] = 0  # acc is a *u32 local now
    store, _ = find(doc['body'], 3)
    store['args'][1] = dict(ty=0, val='0')
    final_load, _ = find(doc['body'], 33)
    final_load['ty'] = 0
    call, body = find(doc['body'], 19)
    at = body.index(call)
    call.clear()
    call.update(id=19, tag='load', ty=0, args=[dict(inst=2)])
    body[at+1:at+1] = [dict(id=40, tag='add_safe', ty=0, args=[dict(inst=19), dict(inst=17)]),
                       dict(id=41, tag='store_safe', ty=2, args=[dict(inst=2), dict(inst=40)])]
    cmp, _ = find(doc['body'], 14)
    if buggy: cmp['tag'] = 'cmp_lte'
    column = 5
    def annotate(body):
        for inst in body:
            if inst.get('tag') == 'dbg_stmt': inst['column'] = column
            for key in ('body', 'then', 'else'):
                if isinstance(inst.get(key), list): annotate(inst[key])
    annotate(doc['body'])
    return doc


def write(directory, buggy):
    directory = Path(directory); directory.mkdir(parents=True, exist_ok=True)
    (directory/'loops.sumUpTo.json').write_text(json.dumps(air(buggy)))
    return directory
