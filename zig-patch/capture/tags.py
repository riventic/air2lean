#!/usr/bin/env python3
"""The AIR instruction tags of every supported Zig version, with their data shape and the
exporter's handling (docs/exporter-split.md §Tag tables).

Sources: the pinned pristine compiler of each version (scripts/cas.py src): the declaration order
of `Air.Inst.Tag` (src/Air.zig) and, for each tag, the function of the compiler's own AIR printer
that prints it (src/Air/print.zig; src/print_air.zig in 0.14.1). The printer's `writeInst` switch
has no `else`, so it names every tag, and its writer function fixes the `Air.Inst.Data` field and
the `extra` payload of the tag (KINDS below). The exporter column models the `writeInst` switch of
zig-patch/air-json/json.zig and its `Compat` tag helpers.

  tags.py markdown                  print docs/exporter-air-tags.md
  tags.py zig VERSION               print zig-patch/capture/VERSION/tags.zig (exhaustive switch)
  tags.py write | check             write or check both outputs for every version that has one
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
VERSIONS = ('0.14.1', '0.15.2', '0.16.0', '0.17.0')
MARKDOWN = ROOT / 'docs/exporter-air-tags.md'
# The capture shim exists for these versions (zig-patch/capture/<version>/tags.zig).
ZIG_VERSIONS = ('0.17.0',)

# Printer writer function -> (capture kind, `Air.Inst.Data` field, `extra` payload / trailing data).
KINDS = {
    'writeBinOp': ('bin_op', 'bin_op', ''),
    'writeUnOp': ('un_op', 'un_op', ''),
    'writeNoOp': ('no_op', 'no_op', ''),
    'writeTy': ('ty', 'ty', ''),
    'writeArg': ('arg', 'arg', ''),
    'writeTyOp': ('ty_op', 'ty_op', ''),
    'writeBlock': ('block', 'ty_pl', 'Block or DbgInlineBlock + body'),
    'writeLoop': ('loop', 'ty_pl', 'Block + body'),
    'writeTyPlBin': ('ty_pl_bin', 'ty_pl', 'Bin'),
    'writeCall': ('call', 'pl_op', 'Call + args'),
    'writeDbgVar': ('dbg_var', 'pl_op', 'NullTerminatedString'),
    'writeStructField': ('struct_field', 'ty_pl', 'StructField'),
    'writeAssembly': ('assembly', 'ty_pl', 'Asm + operands, names, source'),
    'writeDbgStmt': ('dbg_stmt', 'dbg_stmt', ''),
    'writeAggregateInit': ('aggregate_init', 'ty_pl', 'element refs (count from the type)'),
    'writeUnionInit': ('union_init', 'ty_pl', 'UnionInit'),
    'writeBr': ('br', 'br', ''),
    'writeRepeat': ('repeat', 'repeat', ''),
    'writeCondBr': ('cond_br', 'pl_op', 'CondBr + then/else bodies'),
    'writeTry': ('try', 'pl_op', 'Try + body'),
    'writeTryPtr': ('try_ptr', 'ty_pl', 'TryPtr + body'),
    'writeSwitchBr': ('switch_br', 'pl_op', 'SwitchBr + cases'),
    'writeCmpxchg': ('cmpxchg', 'ty_pl', 'Cmpxchg'),
    'writeAtomicLoad': ('atomic_load', 'atomic_load', ''),
    'writePrefetch': ('prefetch', 'prefetch', ''),
    'writeAtomicStore': ('atomic_store', 'bin_op', ''),
    'writeAtomicRmw': ('atomic_rmw', 'pl_op', 'AtomicRmw'),
    'writeFieldParentPtr': ('field_parent_ptr', 'ty_pl', 'FieldParentPtr'),
    'writeWasmMemorySize': ('wasm_memory', 'pl_op', ''),
    'writeWasmMemoryGrow': ('wasm_memory', 'pl_op', ''),
    'writeWorkDimension': ('work_dimension', 'pl_op', ''),
    'writeMulAdd': ('pl_op_bin', 'pl_op', 'Bin'),
    'writeSelect': ('pl_op_bin', 'pl_op', 'Bin'),
    'writeShuffle': ('shuffle', 'ty_pl', 'Shuffle (comptime mask)'),
    'writeShuffleOne': ('shuffle_one', 'ty_pl', 'ShuffleOne + mask'),
    'writeShuffleTwo': ('shuffle_two', 'ty_pl', 'ShuffleTwo + mask'),
    'writeReduce': ('reduce', 'reduce', ''),
    'writeCmpVector': ('cmp_vector', 'ty_pl', 'VectorCmp'),
    'writeRuntimeNavPtr': ('runtime_nav_ptr', 'ty_nav', ''),
    'writeVectorStoreElem': ('vector_store_elem', 'vector_store_elem', 'Bin'),
    'writeLegalizeVecStoreElem': ('legalize', 'pl_op', 'Bin (Legalize only)'),
    'writeLegalizeCompilerRtCall': ('legalize', 'legalize_compiler_rt_call', 'args (Legalize only)'),
    '@panic("TODO")': ('inferred_alloc', 'inferred_alloc', ''),
}


def source_dir(version):
    env = dict(os.environ)
    with tempfile.TemporaryDirectory() as scratch:
        out = subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/cas.py'), 'src', version,
                              '--scratch', str(Path(scratch) / 'src')], capture_output=True, text=True, env=env)
        if out.returncode != 0:
            raise SystemExit('tags.py: no pristine source of %s:\n%s' % (version, out.stderr))
        path = Path(out.stdout.strip().splitlines()[-1])
        if not env.get('AIR2LEAN_CAS_DIR'):
            raise SystemExit('tags.py: set AIR2LEAN_CAS_DIR (docs/build-cache.md): the source must outlive this call')
        return path


def switch_arms(text):
    """{tag: right-hand side} of a `switch (tag) { .a, .b => rhs, ... }` body."""
    arms, pending = {}, []
    for line in text.split('\n'):
        left, arrow, right = line.partition('=>')
        pending += [t.strip('@"') for t in re.findall(r'\.(@"[^"]+"|[a-z_0-9]+)', left)]
        if arrow:
            for tag in pending:
                arms[tag] = right.strip()
            pending = []
    return arms


def version_tags(src):
    """(declaration order, {tag: printer writer}) of one compiler source tree."""
    air = (src / 'src/Air.zig').read_text(encoding='utf-8')
    start = air.index('pub const Tag = enum(u8) {')
    body = air[start:air.index('\n        };', start)]
    order = [t.strip('@"') for t in re.findall(r'^\s{8}(@"[^"]+"|[a-z_0-9]+),\s*$', body, re.M) if t != '_']
    printer = src / 'src/Air/print.zig'
    if not printer.is_file():
        printer = src / 'src/print_air.zig'
    text = printer.read_text(encoding='utf-8')
    i = text.index('switch (tag) {', text.index('fn writeInst(w: *Writer'))
    arms = switch_arms(text[i + len('switch (tag) {'):text.index('\n        }\n', i)])
    writers = {}
    for tag, rhs in arms.items():
        m = re.search(r'(write\w+|@panic\("[^"]*"\))', rhs)
        writers[tag] = m.group(1) if m else rhs
    missing, extra = set(order) - set(writers), set(writers) - set(order)
    if missing or extra or any(w not in KINDS for w in writers.values()):
        raise SystemExit('tags.py: printer and Tag disagree in %s: missing %s, extra %s, unknown writers %s' % (
            src, sorted(missing), sorted(extra), sorted({w for w in writers.values() if w not in KINDS})))
    return order, writers


# ------------------------------------------------------------------ the exporter's handling

def exporter_arms():
    """The tags of json.zig's explicit `writeInst` arms (version-independent names)."""
    text = (ROOT / 'zig-patch/air-json/json.zig').read_text(encoding='utf-8')
    i = text.index('switch (tag) {', text.index('fn writeInst(w: *W'))
    i = text.index('switch (tag) {', i + 1)  # the second switch: operands (the first writes `ty`)
    depth, j = 0, text.index('{', i)
    while True:
        depth += {'{': 1, '}': -1}.get(text[j], 0)
        j += 1
        if depth == 0:
            break
    # The arms of this switch start at 12 spaces; deeper lines are their bodies.
    arms = [line for line in text[i:j].split('\n') if re.match(r' {12}(\.|=>)', line)]
    return {tag for tag, rhs in switch_arms('\n'.join(arms)).items()}


def compat(version):
    """json.zig's `Compat` tag helpers for VERSION (the `else` arm of `writeInst`)."""
    v14, v17 = version == '0.14.1', version == '0.17.0'
    ty_op = ({'bitcast', 'intcast', 'intcast_safe'} if v14 else
             {'int_from_float_safe', 'bit_cast', 'bit_cast_safe', 'int_cast', 'int_cast_safe', 'ptr_cast',
              'ptr_from_int', 'int_from_ptr', 'error_cast', 'error_from_int', 'int_from_error', 'union_from_enum',
              'array_to_vector'} if v17 else
             {'int_from_float_safe', 'bitcast', 'intcast', 'intcast_safe'})
    bin_op = {'bool_and', 'bool_or'} if v14 else ({'memmove', 'div_ceil'} if v17 else {'memmove', 'bool_and', 'bool_or'})
    other = {'agg_field_val' if v17 else 'struct_field_val': 'Compat.isFieldVal'}
    if v14:
        other['shuffle'] = 'shuffle (0.14.1)'
    else:
        other.update(shuffle_one='shuffle_one', shuffle_two='shuffle_two', runtime_nav_ptr='Compat.isRuntimeNavPtr')
    return ty_op, bin_op, other


def handling(tag, version, explicit):
    if tag in explicit:
        return 'explicit arm'
    ty_op, bin_op, other = compat(version)
    if tag in ty_op:
        return 'Compat.isNewTyOp'
    if tag in bin_op:
        return 'Compat.isNewBinOp'
    return other.get(tag, 'unsupported')


# ------------------------------------------------------------------ outputs

def markdown(tables):
    explicit = exporter_arms()
    all_tags = []
    for version in VERSIONS:
        for tag in tables[version][0]:
            if tag not in all_tags:
                all_tags.append(tag)
    lines = ['<!-- Generated by zig-patch/capture/tags.py; do not edit. -->',
             '# AIR instruction tags per Zig version',
             '',
             'Every `Air.Inst.Tag` of every supported version, in first-seen declaration order (0.14.1 first,',
             'then the tags later versions add). A version cell is the tag\'s capture kind: the',
             '`Air.Inst.Data` field and `extra` payload that the compiler\'s own AIR printer reads for it',
             '(`—`: the version has no such tag). The exporter column is how `zig-patch/air-json/json.zig`',
             'writes the tag in the versions that have it: an explicit `writeInst` arm, a `Compat` helper,',
             'or `"unsupported": true`. Design: [exporter-split.md](exporter-split.md).',
             '',
             '| Kind | Data field | Extra payload |',
             '|---|---|---|']
    seen = set()
    for kind, field, payload in KINDS.values():
        if kind not in seen:
            seen.add(kind)
            lines.append('| `%s` | `%s` | %s |' % (kind, field, payload or '—'))
    counts = ', '.join('%s: %d' % (v, len(tables[v][0])) for v in VERSIONS)
    lines += ['', 'Tags per version: %s.' % counts, '',
              '| Tag | %s | Exporter |' % ' | '.join(VERSIONS),
              '|---|%s---|' % ('---|' * len(VERSIONS))]
    for tag in all_tags:
        cells, handled = [], []
        for version in VERSIONS:
            order, writers = tables[version]
            if tag in writers:
                cells.append('`%s`' % KINDS[writers[tag]][0])
                h = handling(tag, version, explicit)
                if h not in handled:
                    handled.append(h)
            else:
                cells.append('—')
        lines.append('| `%s` | %s | %s |' % (tag, ' | '.join(cells), ', '.join(handled)))
    return '\n'.join(lines) + '\n'


def zig_switch(version, table):
    order, writers = table
    by_kind = {}
    for tag in order:
        by_kind.setdefault(KINDS[writers[tag]][0], []).append(tag)
    kinds = []
    for kind, _, _ in KINDS.values():
        if kind not in kinds:
            kinds.append(kind)
    ident = lambda t: t if re.fullmatch(r'[a-z_][a-z_0-9]*', t) and t not in ('try', 'null') else '@"%s"' % t
    out = ['//! Generated by zig-patch/capture/tags.py from the pristine Zig %s sources; do not edit.' % version,
           '//! The capture kind of every `Air.Inst.Tag` of this version: which `Air.Inst.Data` field and',
           '//! `extra` payload the instruction has (docs/exporter-air-tags.md). The switch has no `else`:',
           '//! a tag that a new version adds fails to compile until it has a kind.',
           '',
           'const Air = @import("../Air.zig");',
           '',
           'pub const Kind = enum {',
           *['    %s,' % ident(k) for k in kinds],
           '};',
           '',
           'pub fn kind(tag: Air.Inst.Tag) Kind {',
           '    return switch (tag) {']
    for kind in kinds:
        if kind in by_kind:
            out.append('        ' + ',\n        '.join('.' + ident(t) for t in by_kind[kind]) + ',')
            out.append('        => .%s,' % ident(kind))
    out += ['    };', '}', '']
    return '\n'.join(out)


def outputs():
    tables = {v: version_tags(source_dir(v)) for v in VERSIONS}
    files = {MARKDOWN: markdown(tables)}
    for version in ZIG_VERSIONS:
        files[ROOT / 'zig-patch/capture' / version / 'tags.zig'] = zig_switch(version, tables[version])
    return files


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('command', choices=('markdown', 'zig', 'write', 'check'))
    parser.add_argument('version', nargs='?', choices=VERSIONS)
    a = parser.parse_args(argv)
    if a.command == 'markdown':
        sys.stdout.write(markdown({v: version_tags(source_dir(v)) for v in VERSIONS}))
    elif a.command == 'zig':
        sys.stdout.write(zig_switch(a.version or '0.17.0', version_tags(source_dir(a.version or '0.17.0'))))
    else:
        stale = []
        for path, text in outputs().items():
            if not path.is_file() or path.read_text(encoding='utf-8') != text:
                stale.append(path.relative_to(ROOT))
                if a.command == 'write':
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(text, encoding='utf-8')
        if stale and a.command == 'check':
            raise SystemExit('stale (zig-patch/capture/tags.py write): ' + ', '.join(map(str, stale)))
        for path in stale:
            print('wrote', path)
    return 0


if __name__ == '__main__':
    sys.exit(main())
