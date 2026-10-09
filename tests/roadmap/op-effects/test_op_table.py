#!/usr/bin/env python3
"""S2: the exhaustive op classifier and the translator's op table.

`air2lean --print-op-table` must equal the committed `coverage/op-table/op-table.json` that
`scripts/coverage.py` reads; every tag that `normalizeOp` names must be in it, decoded to the
constructor of an `Op`, with an effect class and an emitter route; every `Op` constructor must
be reachable from a tag; an unknown tag (also an unlisted `call*` variant) must be rejected,
not decoded or skipped; and the classifier and the analyses that read it keep no wildcard arm.

usage: test_op_table.py [--self-test] <air2lean binary>
`--self-test` runs only the source checks (no translator).
"""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('coverage_inventory', ROOT / 'scripts/coverage.py')
coverage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(coverage)
BINARY = None

# (file, definition, rule): `no-wildcard` — no default arm at the definition's arm indentation;
# `no-op-match` — reads `Op.effects` instead of matching on the op.
CLASSIFIER_DEFS = [
    ('Air2Lean/Air/Effects.lean', 'Op.effects', 'no-wildcard'),
    ('Air2Lean/Air/Effects.lean', 'Op.ctorName', 'no-wildcard'),
    ('Air2Lean/Air/Effects.lean', 'Control.bodies', 'no-wildcard'),
    ('Air2Lean/Air/Effects.lean', 'Control.jumpTarget?', 'no-wildcard'),
    ('Air2Lean/Air/Effects.lean', 'Op.emitRoute', 'no-wildcard'),
    ('Air2Lean/Check.lean', 'summarizeTryErrors', 'no-wildcard'),
    ('Air2Lean/Check.lean', 'CheckCtx.checkVolatile', 'no-op-match'),
    ('Air2Lean/Check.lean', 'ptrOperands', 'no-op-match'),
    ('Air2Lean/Memory.lean', 'flattenOp', 'no-op-match'),
    ('Air2Lean/Memory.lean', 'valueOperands', 'no-op-match'),
    ('Air2Lean/Memory.lean', 'placeOperands', 'no-op-match'),
    ('Air2Lean/Memory.lean', 'bodyLists', 'no-op-match'),
    ('Air2Lean/Memory.lean', 'memoryOp', 'no-op-match'),
    ('Air2Lean/Memory.lean', 'Func.syncLocally', 'no-op-match'),
    ('Air2Lean/Emit.lean', 'emitScalar', 'no-wildcard'),
    ('Air2Lean/Emit.lean', 'isTerminating', 'no-op-match'),
]


def rule_problems(text, name, rule):
    section = coverage.lean_section(text, name)
    if rule == 'no-op-match':
        return [f'{name}: matches on the op'] if re.search(r'match (?:\w+\.)?op with', section) else []
    arms = re.findall(r'^( *)\| ', section, re.M)
    if not arms:
        return [f'{name}: no match arms']
    indent = arms[0]
    if re.search('^' + indent + r'\| _\s*(?:,\s*_\s*)*=>', section, re.M):
        return [f'{name}: wildcard arm']
    return []


def arm_tags(section):
    """String literals of the two-space-indented match arms (one arm may span lines)."""
    tags = []
    for line in re.findall(r'^  \| ((?:"[^"\n]+"\s*\|?\s*)+)(?:=>.*)?$', section, re.M):
        tags += re.findall(r'"([^"\n]+)"', line)
    return tags


def decoder_tags(text):
    return arm_tags(coverage.lean_section(text, 'normalizeOp'))


def reason_tags(text, name):
    return re.findall(r'"([^"\n]+)"', ' '.join(re.findall(r'\(#\[([^\]]*)\]', coverage.lean_section(text, name))))


def list_tags(text, name):
    return re.findall(r'"([^"\n]+)"', coverage.lean_section(text, name))


def op_constructors(text):
    body = text.split('inductive Op where', 1)[1].split('\nstructure SwitchCase', 1)[0]
    return {a or b for a, b in re.findall(r'^  \| (?:«([^»]+)»|([A-Za-z][A-Za-z0-9]*))', body, re.M)}


class SourceTests(unittest.TestCase):
    def setUp(self):
        self.normalize = (ROOT / 'Air2Lean/Air/Normalize.lean').read_text()
        self.table = coverage.op_table()

    def test_every_decoder_tag_is_in_the_table(self):
        decoded = decoder_tags(self.normalize)
        self.assertGreater(len(decoded), 150)
        self.assertEqual(len(decoded), len(set(decoded)))
        self.assertEqual(decoded, list_tags(self.normalize, 'decodedTags'))
        rows = self.table['tags']
        self.assertEqual({t for t, r in rows.items() if r['constructor']}, set(decoded))
        for tag in decoded:
            self.assertTrue(rows[tag]['effect'] and rows[tag]['emit'], tag)
        for name, column in (('runtimeTagReasons', 'runtime_reason'), ('exporterTagReasons', 'exporter_reason')):
            tags = reason_tags(self.normalize, name)
            self.assertTrue(tags, name)
            self.assertEqual(set(coverage.table_reasons(self.table, column)), set(tags), name)
        self.assertEqual(set(rows), set(decoded) | {t for t, r in rows.items() if r['runtime_reason'] or r['exporter_reason']})

    def test_every_op_constructor_has_a_tag(self):
        ops = op_constructors((ROOT / 'Air2Lean/Air/Op.lean').read_text())
        self.assertGreater(len(ops), 80)
        self.assertEqual({r['constructor'] for r in self.table['tags'].values() if r['constructor']}, ops)

    def test_effect_classes(self):
        rows = self.table['tags']
        expected = {'load': 'read', 'store': 'write', 'memcpy': 'read-write', 'atomic_rmw': 'atomic',
                    'assembly': 'asm', 'call': 'call', 'try_ptr': 'control', 'trap': 'noreturn',
                    'dbg_stmt': 'debug', 'alloc': 'local', 'struct_field_ptr': 'address', 'add': 'value'}
        for tag, effect in expected.items():
            self.assertEqual(rows[tag]['effect'], effect, tag)
        routes = {'ret': 'terminator', 'cond_br': 'terminator', 'switch_dispatch': 'terminator',
                  'loop_switch_br': 'structured', 'try': 'structured', 'dbg_var_val': 'erased', 'load': 'straight-line'}
        for tag, route in routes.items():
            self.assertEqual(rows[tag]['emit'], route, tag)

    def test_classifier_and_analyses_have_no_wildcard(self):
        problems = []
        for path, name, rule in CLASSIFIER_DEFS:
            problems += rule_problems((ROOT / path).read_text(), name, rule)
        self.assertEqual(problems, [])

    def test_lint_detects_wildcards(self):
        sample = 'def Op.effects (op : Op) : Effects :=\n  match op with\n  | .arg _ => x\n  | _ => y\n'
        self.assertEqual(rule_problems(sample, 'Op.effects', 'no-wildcard'), ['Op.effects: wildcard arm'])
        nested = 'def Op.effects (op : Op) : Effects :=\n  match op with\n  | .arg _ => match v with\n    | _ => y\n'
        self.assertEqual(rule_problems(nested, 'Op.effects', 'no-wildcard'), [])
        self.assertEqual(rule_problems('def memoryOp (op : Op) : Bool :=\n  match op with\n  | .a => true\n',
                                       'memoryOp', 'no-op-match'), ['memoryOp: matches on the op'])
        self.assertEqual(arm_tags('  | "a" | "b" =>\n    x\n  | "c"\n  | "d" =>\n      | "inner" => y\n'), ['a', 'b', 'c', 'd'])


# A minimal 0.16.0 function: `r.f` returns `*global` read through `op`.
U32 = dict(k="int", signed=False, bits=32, abi_size=4, abi_align=4)
TYPES = [U32, dict(k="void", abi_size=0, abi_align=1),
         dict(k="ptr", size="one", const=True, child=0, ptr_align=4, volatile=False, allowzero=False,
              sentinel=False, host_size=0, abi_size=8, abi_align=8),
         dict(k="noreturn"), dict(k="other", name="fn () *const u32")]
GLOBAL_PTR = {'ty': 2, 'ptr': {'global': 0, 'off': 0}}


def document(body):
    return dict(schema=11, zig_version="0.16.0", target_endian="little", name="r.f", params=[], ret=0,
                body=body, types=copy.deepcopy(TYPES),
                globals=[dict(name="r.limit", ty=0, const=True, threadlocal=False, extern=True)])


def through(tag):
    """`load(tag(&r.limit))`: the global's pointer passes through an op tagged `tag`."""
    callee = dict(callee=dict(ty=4, func="r.g", noreturn=False)) if tag.startswith('call') else {}
    return document([dict(id=0, tag=tag, ty=2, args=[GLOBAL_PTR], **callee),
                     dict(id=1, tag="load", ty=0, args=[dict(inst=0)]),
                     dict(id=2, tag="ret_safe", ty=3, args=[dict(inst=1)])])


class CliTests(unittest.TestCase):
    def run_cli(self, doc, *extra):
        with tempfile.TemporaryDirectory() as tmp:
            air = Path(tmp) / 'air'
            air.mkdir()
            (air / 'r.f.json').write_text(json.dumps(doc))
            out = Path(tmp) / 'Gen.lean'
            # The synthetic file is schema 11: legacy AIR needs the explicit profile opt-in.
            legacy = ['--profile', 'legacy-abi64-le'] if doc.get('schema', 12) < 12 else []
            translated = subprocess.run([BINARY, str(air), '-o', str(out), '--namespace', 'R', *legacy, *extra],
                                        capture_output=True, text=True, timeout=600)
            diagnosed = subprocess.run([BINARY, '--diagnostics-json', str(air), *legacy],
                                       capture_output=True, text=True, timeout=600)
            return translated, (out.read_text() if out.exists() else None), diagnosed

    def test_printed_table_is_the_committed_table(self):
        printed = subprocess.run([BINARY, '--print-op-table'], capture_output=True, text=True, timeout=600)
        self.assertEqual(printed.returncode, 0, printed.stderr)
        self.assertEqual(printed.stdout, (ROOT / coverage.OP_TABLE).read_text(),
                         f'regenerate: air2lean --print-op-table > {coverage.OP_TABLE}')

    def test_unknown_tags_are_rejected_not_skipped(self):
        # `call_async` once matched the `call*` prefix and was decoded as a call.
        for tag in ('frobnicate', 'call_async', 'load_volatile', 'try_new'):
            translated, _, diagnosed = self.run_cli(through(tag))
            self.assertEqual(translated.returncode, 1, tag)
            self.assertIn(f"unknown AIR tag '{tag}'", translated.stderr, tag)
            self.assertNotEqual(diagnosed.returncode, 0, tag)
            self.assertIn(f"unknown AIR tag '{tag}'", diagnosed.stdout, tag)
        for tag in ('bitcast', 'call_never_inline'):
            self.assertNotIn('unknown AIR tag', self.run_cli(through(tag))[0].stderr, tag)

    def test_place_constant_makes_a_memory_function(self):
        # A pointer constant that only a place operand (here `bitcast`'s) names is memory: the
        # function reads the global, so it is a `Zig.MemM` function with the global's `mem0`.
        translated, lean, _ = self.run_cli(through('bitcast'))
        self.assertEqual(translated.returncode, 0, translated.stderr)
        self.assertIn('def r_f  : Zig.MemM (BitVec 32)', lean)
        self.assertIn('def mem0 (σ : Zig.Placement) (ext : ExternInit) : Zig.Mem', lean)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('binary', nargs='?')
    args = parser.parse_args()
    if not args.self_test and not args.binary:
        parser.error('a translator binary or --self-test is required')
    BINARY = args.binary
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(SourceTests)
    if not args.self_test:
        suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(CliTests))
    sys.exit(0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1)
