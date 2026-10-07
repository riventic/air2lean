#!/usr/bin/env python3
"""V03 independent export validation regressions. No Zig, Lake or Lean runs.

Positive control: every committed golden AIR file passes. Negative controls: each structural
invariant is broken once in a copy of a real golden export and must be reported.
"""
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts/validate-air.py'
spec = importlib.util.spec_from_file_location('validate_air', SCRIPT)
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)

# 0.15.2 export with a loop, nested blocks, cond_br, br/repeat targets and a slice type.
BASE = json.loads((ROOT / 'tests/golden/basic/air/basic.sum.json').read_text(encoding='utf-8'))


def find(body, ident):
    for inst in body:
        if inst['id'] == ident:
            return inst
        for key in ('body', 'then', 'else'):
            hit = find(inst.get(key, []), ident)
            if hit:
                return hit
    return None


def findings(doc):
    return v.validate_text(json.dumps(doc) if not isinstance(doc, str) else doc)


class ValidateAir(unittest.TestCase):
    def mutate(self, change):
        doc = copy.deepcopy(BASE)
        change(doc)
        return doc

    def assertFinding(self, doc, needle):
        result = findings(doc)
        self.assertTrue(any(needle in line for line in result), f'{needle!r} not in {result}')

    def test_base_is_valid(self):
        self.assertEqual(findings(BASE), [])

    def test_all_committed_golden_air_is_valid(self):
        files = v.committed_air()
        self.assertGreater(len(files), 400)
        versions = {json.loads(p.read_text(encoding='utf-8'))['zig_version'] for p in files}
        self.assertEqual(versions, {'0.14.1', '0.15.2', '0.16.0'})
        cache = {}
        bad = {str(p): r for p in files if (r := v.validate_text(p.read_text(encoding='utf-8'), cache=cache))}
        self.assertEqual(bad, {})

    def test_duplicate_instruction_id(self):
        self.assertFinding(self.mutate(lambda d: find(d['body'], 13).update(id=11)), 'duplicate instruction id 11')

    def test_unknown_operand(self):
        self.assertFinding(self.mutate(lambda d: find(d['body'], 15)['args'].__setitem__(0, {'inst': 999})),
                           'instruction ref 999 does not resolve')

    def test_forward_reference(self):
        # 13 reads 14 before 14 is defined.
        self.assertFinding(self.mutate(lambda d: find(d['body'], 13)['args'].__setitem__(0, {'inst': 14})),
                           'instruction ref 14 does not resolve')

    def test_reference_out_of_inner_scope(self):
        # 33 (main body) reads 22, defined inside the loop's cond_br then-branch.
        self.assertFinding(self.mutate(lambda d: find(d['body'], 33)['args'].__setitem__(0, {'inst': 22})),
                           'instruction ref 22 does not resolve')

    def test_instruction_ref_inside_constant(self):
        def change(d):
            find(d['body'], 3)['args'][1] = {'ty': 1, 'elems': [{'inst': 0}]}
        self.assertFinding(self.mutate(change), 'instruction ref 0 inside a constant')

    def test_br_to_non_enclosing_block(self):
        # 27 is enclosed by blocks 9 and 12; 2 is an alloc and 12 does not enclose 35.
        self.assertFinding(self.mutate(lambda d: find(d['body'], 27).update(target=2)), 'not an enclosing block')
        def sibling(d):
            d['body'][-1] = {'id': 35, 'tag': 'br', 'ty': d['body'][-1]['ty'], 'target': 12,
                             'args': [{'ty': 2, 'val': '{}'}]}
        self.assertFinding(self.mutate(sibling), 'target 12 is not an enclosing block')

    def test_repeat_must_target_loop(self):
        self.assertFinding(self.mutate(lambda d: find(d['body'], 31).update(target=9)), 'not an enclosing loop')

    def test_missing_terminator(self):
        self.assertFinding(self.mutate(lambda d: d['body'].pop()), 'does not end in a noreturn terminator')

    def test_noreturn_in_the_middle(self):
        def change(d):
            d['body'].insert(1, {'id': 900, 'tag': 'unreach', 'ty': find(d['body'], 35)['ty']})
        self.assertFinding(self.mutate(change), 'noreturn instruction before the end')

    def test_empty_body(self):
        self.assertFinding(self.mutate(lambda d: find(d['body'], 28).update(**{'else': []})), 'body is empty')

    def test_missing_cond_br_branch(self):
        self.assertFinding(self.mutate(lambda d: find(d['body'], 28).pop('then')), 'missing then body')

    def test_instruction_type_out_of_range(self):
        self.assertFinding(self.mutate(lambda d: find(d['body'], 13).update(ty=len(d['types']))),
                           'is not in the type table')

    def test_param_and_ret_type_out_of_range(self):
        self.assertFinding(self.mutate(lambda d: d.update(params=[77])), 'params[0]: type reference 77')
        self.assertFinding(self.mutate(lambda d: d.update(ret=-1)), 'ret: type reference -1')

    def test_child_type_out_of_range(self):
        self.assertFinding(self.mutate(lambda d: d['types'][0].update(child=500)), 'types[0].child')

    def test_constant_type_out_of_range(self):
        self.assertFinding(self.mutate(lambda d: find(d['body'], 3)['args'].__setitem__(1, {'ty': 99, 'val': '0'})),
                           'type reference 99')

    def test_cyclic_value_type(self):
        def change(d):
            d['types'].append({'k': 'optional', 'child': len(d['types']) + 1})
            d['types'].append({'k': 'optional', 'child': len(d['types']) - 1})
        self.assertFinding(self.mutate(change), 'cyclic value type')

    def test_pointer_recursion_is_allowed(self):
        def change(d):
            n = len(d['types'])
            d['types'].append({'k': 'ptr', 'size': 'one', 'child': n + 1})
            d['types'].append({'k': 'struct', 'name': 'Node', 'layout': 'auto', 'fields': [{'name': 'next', 'ty': n}]})
        self.assertEqual(findings(self.mutate(change)), [])

    def test_tag_outside_version_universe(self):
        # memmove is not an AIR tag in 0.14.1; it is in 0.15.2.
        def change(d, version):
            d['zig_version'] = version
            find(d['body'], 3)['tag'] = 'memmove'
        self.assertEqual(findings(self.mutate(lambda d: change(d, '0.15.2'))), [])
        self.assertFinding(self.mutate(lambda d: change(d, '0.14.1')), "tag 'memmove' is not an AIR tag")
        self.assertFinding(self.mutate(lambda d: find(d['body'], 3).update(tag='store_safe_fast')), 'not an AIR tag')

    def test_unsupported_marker_matches_inventory(self):
        # The 0.15.2 exporter decodes add_safe and writes "unsupported": true for add_optimized.
        self.assertFinding(self.mutate(lambda d: find(d['body'], 22).update(unsupported=True)),
                           'marker on a tag the exporter decodes')
        self.assertFinding(self.mutate(lambda d: find(d['body'], 22).update(tag='add_optimized')),
                           'decoded operands for a tag the exporter marks unsupported')
        self.assertEqual(findings(self.mutate(lambda d: find(d['body'], 22).update(
            tag='add_optimized', unsupported=True))), [])

    def test_global_reference(self):
        def change(d):
            find(d['body'], 3)['args'][1] = {'ty': 0, 'ptr': {'global': 0, 'off': 0}}
        self.assertFinding(self.mutate(change), 'global 0 is not in globals')

    def test_unknown_version_and_schema(self):
        self.assertFinding(self.mutate(lambda d: d.update(zig_version='0.99.0')), 'no coverage inventory')
        self.assertFinding(self.mutate(lambda d: d.update(schema=13)), 'unsupported schema 13')

    def test_malformed_shapes_are_findings_not_crashes(self):
        self.assertFinding(self.mutate(lambda d: find(d['body'], 13).update(id=[13])), 'is not a natural number')
        self.assertFinding(self.mutate(lambda d: find(d['body'], 15)['args'].__setitem__(0, {'inst': [1]})),
                           'malformed AIR shape')
        self.assertFinding(self.mutate(lambda d: d.update(types={'k': 'int'})), 'types: missing or not a list')

    def test_duplicate_json_key(self):
        text = json.dumps(BASE)
        self.assertFinding(text.replace('"ret": 1', '"ret": 1, "ret": 1', 1), "duplicate JSON key 'ret'")

    def test_cli_exit_codes(self):
        with tempfile.TemporaryDirectory() as tmp:
            good, bad = Path(tmp, 'good.json'), Path(tmp, 'bad.json')
            good.write_text(json.dumps(BASE), encoding='utf-8')
            bad.write_text(json.dumps(self.mutate(lambda d: d['body'].pop())), encoding='utf-8')
            run = lambda *a: subprocess.run([sys.executable, '-B', str(SCRIPT), *a], env=ENV,
                                            capture_output=True, text=True)
            self.assertEqual(run(str(good)).returncode, 0)
            result = run(str(good), str(bad))
            self.assertEqual(result.returncode, 1)
            self.assertIn('bad.json: body[', result.stdout)
            self.assertIn('2 files, 1 with findings', result.stdout)
            self.assertEqual(run(str(Path(tmp, 'missing.json'))).returncode, 2)


if __name__ == '__main__':
    unittest.main()
