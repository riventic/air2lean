# Execute the retained shell comparison with compiler-free translator/Lean mocks.
import hashlib
import json
import os
import runpy
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
CASE = Path(__file__).resolve().parent
BODY = b'import ZigLean\ndef fixture := 7\n'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class RetainedComparisonTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        self.case = self.repo/'tests/roadmap/try-pointers'
        air = self.case/'air/0.16.0'
        air.mkdir(parents=True)
        (self.case/'TryPointers').mkdir()
        (self.repo/'scripts').mkdir()
        for name in ['check.sh', 'check-artifacts.py']:
            shutil.copyfile(CASE/name, self.case/name)
        shutil.copyfile(ROOT/'scripts/normalize-generated.py', self.repo/'scripts/normalize-generated.py')
        (self.repo/'source.zig').write_text('fixture source')
        (self.repo/'exporter.zig').write_text('origin exporter')
        (self.case/'TryPointers/Gen.lean').write_bytes(BODY)
        for name, tag in [('hot', 'try_ptr'), ('cold', 'try_ptr_cold')]:
            (air/(name+'.json')).write_text(json.dumps(dict(schema=11, zig_version='0.16.0',
                target_endian='little', name='try_pointers.'+name, body=[dict(tag=tag)])))
        origin = dict(source='source.zig', source_sha256=digest(self.repo/'source.zig'),
                      exporter='exporter.zig', exporter_sha256=digest(self.repo/'exporter.zig'),
                      functions=['hot', 'cold'], artifacts={})
        origin['artifacts'] = {str(p.relative_to(self.case)): digest(p)
                               for p in [*sorted(air.glob('*.json')), self.case/'TryPointers/Gen.lean']}
        (self.case/'provenance.json').write_text(json.dumps(origin))
        self.origin = (self.case/'provenance.json').read_bytes()
        (self.repo/'exporter.zig').write_text('combined exporter')
        self.variant = self.case/'integration-qualification.json'
        self.variant.write_text(json.dumps(dict(format='l04-integration-inputs-v1',
            status='inputs-only-not-compilation-attestation',
            origin_provenance_sha256=digest(self.case/'provenance.json'),
            origin_exporter_sha256=origin['exporter_sha256'],
            current_exporter_sha256=digest(self.repo/'exporter.zig'))))
        translator = self.repo/'compiler-free-translator'
        translator.write_text('''#!/usr/bin/env python3
import json, os, pathlib, runpy, sys
root = pathlib.Path(__file__).parent
helper = runpy.run_path(str(root/'scripts/normalize-generated.py'))
air = root/'tests/roadmap/try-pointers/air/0.16.0'
doc = json.loads((air/'hot.json').read_text())
mode = os.environ.get('MOCK_GENERATED', 'header')
if mode == 'wrong-profile': doc['zig_version'] = '0.15.2'
metadata = dict(profile=helper['profile_for_air'](doc), float_semantics='ieee', correspondence='model')
body = b'import ZigLean\\ndef fixture := 7\\n'
if mode == 'wrong-body': body += b'def changed := 8\\n'
if mode != 'headerless': body = helper['PREFIX'] + json.dumps(metadata).encode() + b'\\n' + body
pathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(body)
''')
        translator.chmod(0o700)
        lean = self.repo/'compiler-free-lean-stop'
        lean.write_text('''#!/usr/bin/env python3
import os, pathlib, sys
pathlib.Path(os.environ['MOCK_KERNEL_INPUT']).write_bytes(pathlib.Path(sys.argv[-1]).read_bytes())
raise SystemExit(73)
''')
        lean.chmod(0o700)
        self.seen = self.repo/'kernel-input'
        self.env = dict(os.environ, AIR2LEAN_TRANSLATOR=str(translator), AIR2LEAN_LEAN=str(lean),
                        MOCK_KERNEL_INPUT=str(self.seen), TMPDIR=str(self.repo),
                        RUNNER_TEMP=str(self.repo), PYTHONDONTWRITEBYTECODE='1')

    def run_gate(self, mode='header'):
        env = dict(self.env, MOCK_GENERATED=mode)
        return subprocess.run(['bash', str(self.case/'check.sh'), '--check-artifacts'],
                              cwd=self.repo, env=env, capture_output=True, text=True, timeout=10)

    def test_variant_compares_body_and_sends_full_header_to_kernel(self):
        result = self.run_gate()
        self.assertEqual(result.returncode, 73, result.stdout+result.stderr)
        self.assertTrue(self.seen.read_bytes().startswith(b'-- air2lean-profile: '))
        self.assertTrue(self.seen.read_bytes().endswith(BODY))
        self.assertEqual((self.case/'provenance.json').read_bytes(), self.origin)

    def test_wrong_profile_or_body_never_reaches_kernel(self):
        for mode, message in [('wrong-profile', 'AIR profile differs'),
                              ('wrong-body', 'semantics changed')]:
            with self.subTest(mode=mode):
                result = self.run_gate(mode)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotEqual(result.returncode, 73)
                self.assertIn(message, result.stderr)
                self.assertFalse(self.seen.exists())

    def test_variant_requires_header(self):
        result = self.run_gate('headerless')
        self.assertNotEqual(result.returncode, 73)
        self.assertIn('no first-line profile record', result.stderr)
        self.assertFalse(self.seen.exists())

    def test_retained_raw_gen_hash_and_inventory_guards_precede_translation(self):
        gen = self.case/'TryPointers/Gen.lean'
        gen.write_bytes(BODY+b'changed')
        result = self.run_gate()
        self.assertIn('artifact inventory', result.stderr)
        self.assertFalse(self.seen.exists())
        gen.write_bytes(BODY)
        (self.case/'air/0.16.0/cold.json').unlink()
        result = self.run_gate()
        self.assertIn('function inventory', result.stderr)
        self.assertFalse(self.seen.exists())

    def test_retained_generated_raw_hash_and_receipt_are_rechecked(self):
        helper = runpy.run_path(str(self.repo/'scripts/normalize-generated.py'))
        air = self.case/'air/0.16.0'
        doc = json.loads((air/'hot.json').read_text())
        metadata = dict(profile=helper['profile_for_air'](doc),
                        float_semantics='ieee', correspondence='model')
        generated = self.repo/'generated.lean'
        raw = helper['PREFIX'] + json.dumps(metadata).encode() + b'\n' + BODY
        generated.write_bytes(raw)
        receipt = self.repo/'generated-report.json'
        helper['write_report'](generated, air, receipt)
        generated.write_bytes(raw + b'changed after report')
        with self.assertRaisesRegex(ValueError, 'validated check report'):
            helper['compare'](self.case/'TryPointers/Gen.lean', generated, receipt)
        generated.write_bytes(raw)
        report = json.loads(receipt.read_text())
        report['metadata']['profile']['zig_version'] = '0.15.2'
        receipt.write_text(json.dumps(report))
        with self.assertRaisesRegex(ValueError, 'validated check report'):
            helper['compare'](self.case/'TryPointers/Gen.lean', generated, receipt)

    def test_standalone_headerless_raw_comparison_remains_strict(self):
        self.variant.unlink()
        (self.repo/'exporter.zig').write_text('origin exporter')
        result = self.run_gate('header')
        self.assertNotEqual(result.returncode, 73)
        self.assertFalse(self.seen.exists())
        result = self.run_gate('headerless')
        self.assertEqual(result.returncode, 73, result.stdout+result.stderr)
        self.assertEqual(self.seen.read_bytes(), BODY)
        self.assertEqual((self.case/'provenance.json').read_bytes(), self.origin)


if __name__ == '__main__':
    unittest.main()
