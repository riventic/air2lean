#!/usr/bin/env python3
"""P08 on a real patched-compiler export, with the Zig side in the replay.

native/loops.zig is exported by a compiler that carries the I05 exporter change (`src`/`column`
provenance), translated by the built `air2lean`, searched with `goal-search` and replayed twice:
by the generated Lean and by the native program built with a stock zig through the production
differential harness. The reported source spans must point at the marked lines of the real file.

Needs (otherwise skipped):
  AIR2LEAN_ZIG_AIR      patched zig with the I05 exporter (zig-patch/build.sh); an older patched
                        compiler exports no `src` and fails the span checks on purpose
  AIR2LEAN_ZIG_NATIVE   stock zig of the same version (builds and runs the native harness)
  .lake/build/bin/air2lean and a built ZigLean (`lake build ZigLean air2lean`)
Usage: python3 -I -B tests/roadmap/counterexamples/test_real_export.py
"""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
FIXTURE = ROOT/'tests/roadmap/counterexamples/native'
SOURCE = FIXTURE/'loops.zig'
AIR2LEAN = ROOT/'.lake/build/bin/air2lean'
ZIG_AIR, ZIG_NATIVE = os.environ.get('AIR2LEAN_ZIG_AIR'), os.environ.get('AIR2LEAN_ZIG_NATIVE')
SUM_SPEC = 'r = .ok (BitVec.ofNat 32 (p0.toNat * (p0.toNat - 1) / 2))'
SUM_PRE = 'p0.toNat < 1000'
TOTAL_SPEC = 'r.toBool = true'   # the function returns instead of panicking


SPEC = importlib.util.spec_from_file_location('air2lean_counterexample', ROOT/'scripts/counterexample.py')
CX = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(CX)


def cli(*argv, timeout=900):
    return subprocess.run([sys.executable, '-B', str(ROOT/'scripts/counterexample.py'), *argv], cwd=ROOT,
                          capture_output=True, text=True, timeout=timeout)


def line_of(marker):
    """1-based line and text of the unique source line carrying `marker`."""
    hits = [(n, t) for n, t in enumerate(SOURCE.read_text().splitlines(), 1) if marker in t]
    assert len(hits) == 1, (marker, hits)
    return hits[0]


@unittest.skipUnless(ZIG_AIR and ZIG_NATIVE and AIR2LEAN.is_file(), 'needs AIR2LEAN_ZIG_AIR, AIR2LEAN_ZIG_NATIVE and a built air2lean')
class RealExport(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(); cls.dir = Path(cls.temp.name)
        subprocess.run(['bash', str(FIXTURE/'export.sh'), ZIG_AIR, str(cls.dir/'air')], check=True, capture_output=True, text=True, timeout=600)
        (cls.air,) = (cls.dir/'air').iterdir()
        result = subprocess.run([str(AIR2LEAN), str(cls.air), '-o', str(cls.dir/'Gen.lean'), '--namespace', 'Loops', '--prefix', 'loops.'],
                                capture_output=True, text=True, cwd=ROOT)
        assert result.returncode == 0, result.stderr

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def search(self, function, spec, *extra, pre=None):
        out = self.dir/f'{function}.json'
        argv = ['goal-search', '--example', 'loops', '--function', function, '--spec', spec, '--gen', str(self.dir/'Gen.lean'),
                '--air-dir', str(self.air), '--max-inputs', '256', '--native-zig', ZIG_NATIVE, '--output', str(out), *extra]
        if pre: argv += ['--pre', pre]
        result = cli(*argv)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.stdout = result.stdout
        return out, json.loads(out.read_text())

    def test_the_compiler_exports_source_spans(self):
        doc = json.loads((self.air/'loops.scale.json').read_text())
        self.assertEqual(doc['src']['file'], 'loops.zig', 'AIR2LEAN_ZIG_AIR lacks the I05 exporter change (src/column)')
        self.assertTrue(any(isinstance(i.get('column'), int) for i in doc['body'] if i.get('tag') == 'dbg_stmt'))

    def test_postcondition_counterexample_reports_the_declaration_span_and_the_native_run_agrees(self):
        out, data = self.search('sumUpTo', SUM_SPEC, '--zig-source', str(SOURCE), pre=SUM_PRE)
        self.assertEqual((data['classification'], data['reason'], data['input']), ('counterexample', 'replayed_failure', [1]))
        self.assertEqual((data['replay']['status'], data['replay']['zig_native']['status']), ('verified', 'verified'))
        self.assertEqual(data['replay']['zig_native']['observed']['line'], '{"ok":1}')   # Zig returns 1, the contract says 0
        decl, text = line_of('export fn sumUpTo(')
        loc = data['location']
        self.assertEqual((loc['function'], loc['source_map'], loc['localization']), ('loops.sumUpTo', 'exact_statement', 'function_only'))
        (function,) = loc['functions']
        self.assertEqual((function['source_span'], function['source_span_status']),
                         (dict(file='loops.zig', module='loops', line=decl, column=None), 'declaration'))
        # Replaying the stored bundle runs both sides again; a changed Zig file is stale, never a pass.
        result = cli('replay', '--bundle', str(out), '--native-zig', ZIG_NATIVE)
        self.assertEqual(result.returncode, 0, result.stderr); self.assertIn('zig_native=verified', result.stdout)
        edited = self.dir/'edited.json'
        data['replay']['zig_native']['request']['source_sha256'] = '0' * 64
        edited.write_text(json.dumps(data))
        self.assertEqual(cli('replay', '--bundle', str(edited), '--native-zig', ZIG_NATIVE).returncode, 3)

    def test_panicking_input_reports_the_statement_span_and_native_panic_matches(self):
        out, data = self.search('scale', TOTAL_SPEC, '--zig-source', str(SOURCE))
        self.assertEqual((data['classification'], data['observed']['kind']), ('counterexample', 'model_panic'))
        self.assertEqual(data['observed']['line'], '{"fail":"Zig.Error.overflow"}')
        native = data['replay']['zig_native']
        self.assertEqual((native['status'], native['observed']['line']), ('verified', '{"fail":"integerOverflow"}'))
        a, b = data['input']
        self.assertGreaterEqual(a * b, 2 ** 32)   # a real u32 overflow, decoded from the model input
        line, text = line_of('SPAN: checked multiply')
        (site,) = data['location']['candidate_sites']
        self.assertEqual((site['tag'], site['source_span_status'], site['zig_line']), ('mul_safe', 'statement', line))
        self.assertEqual(site['source_span'], dict(file='loops.zig', module='loops', line=line, column=text.index('*') + 1))
        self.assertIn(f'zig_lines=loops.zig:{line} ', self.stdout)   # the headline names the source line

    def test_correct_loop_has_no_counterexample_and_wrong_native_is_never_a_bug(self):
        _, data = self.search('sumUpToOk', SUM_SPEC, '--zig-source', str(SOURCE), pre=SUM_PRE)
        self.assertEqual(data['classification'], 'unsolved')
        self.assertFalse(data['is_program_bug_evidence'])
        # A native program that disagrees with the model leaves the violation unsolved (model or host difference).
        wrong = self.dir/'wrong'; shutil.copytree(FIXTURE, wrong)
        (wrong/'loops.zig').write_text(SOURCE.read_text().replace('while (i <= n)', 'while (i < n)', 1))
        _, data = self.search('sumUpTo', SUM_SPEC, '--zig-source', str(wrong/'loops.zig'), pre=SUM_PRE)
        self.assertEqual((data['classification'], data['reason']), ('unsolved', 'replay_not_reproduced'))
        self.assertEqual(data['replay']['zig_native']['status'], 'not_reproduced')
        self.assertFalse(data['is_program_bug_evidence'])


@unittest.skipUnless(ZIG_NATIVE and (ROOT/'.lake/build/lib/lean/ZigLean.olean').is_file(), 'needs AIR2LEAN_ZIG_NATIVE and a built ZigLean')
class CommittedExample(unittest.TestCase):
    def test_differential_rows_are_confirmed_by_the_model_and_the_native_program(self):
        """The sequential from-case path: `basic.scale` rows replay in Lean and in the harness of the real example."""
        zig_source = ROOT/'examples/basic/basic.zig'
        for args, line, status in [([3, 4], '{"ok":12}', 'verified'),
                                   ([4294967295, 2], '{"fail":"Zig.Error.overflow"}', 'verified'),   # native integerOverflow
                                   ([3, 4], '{"ok":13}', 'not_reproduced')]:
            with self.subTest(args=args):
                request = CX.lean_request(ROOT, 'basic', 'scale', args, line)
                info = CX.with_native(ROOT, CX.lean_block(request), zig_source, 'basic', 'scale', args)
                outcome = CX.confirm(ROOT, info, 600, ZIG_NATIVE)
                self.assertEqual(outcome['status'], status, outcome)
                if status == 'verified': self.assertEqual(outcome['zig_native']['status'], 'verified', outcome)


if __name__ == '__main__':
    unittest.main()
