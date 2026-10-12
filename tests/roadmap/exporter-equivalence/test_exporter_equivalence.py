#!/usr/bin/env python3
"""scripts/exporter-equivalence.py: manifest completeness, golden commands, and the comparisons
with a stub compiler (no Zig)."""

import ast
import contextlib
import io
import json
import os
import re
import runpy
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EQ = runpy.run_path(str(ROOT / 'scripts/exporter-equivalence.py'))

# A patched-zig stand-in: the "source" is JSON {"functions": {fqn: n}, "fail": bool}; it writes
# one schema-11 AIR file per function that passes ZIG_AIR_JSON_FILTER. `--mutate` changes every
# value (a wrong alternative exporter). Each call's argv and filter go to $STUB_LOG.
STUB = r'''#!/usr/bin/env python3
import json, os, sys
args = sys.argv[1:]
mutate = args[:1] == ['--mutate']
args = args[1:] if mutate else args
assert args[:2] == ['build-obj', '-fno-emit-bin'], args
spec = json.load(open(next(a for a in args if a.endswith('.zig'))))
with open(os.environ['STUB_LOG'], 'a') as log:
    log.write(json.dumps({'argv': args, 'filter': os.environ.get('ZIG_AIR_JSON_FILTER')}) + '\n')
if spec.get('fail'):
    print('stub: export failed', file=sys.stderr)
    sys.exit(3)
prefixes = os.environ.get('ZIG_AIR_JSON_FILTER')
for fqn, value in spec['functions'].items():
    if prefixes and not any(fqn.startswith(p) for p in prefixes.split(',')):
        continue
    doc = {'schema': 11, 'zig_version': '0.16.0', 'name': fqn, 'body': [], 'types': [], 'value': value + mutate}
    with open(os.path.join(os.environ['ZIG_AIR_JSON_DIR'], fqn + '.json'), 'w') as f:
        f.write(json.dumps(doc, indent=1) + '\n')
'''


def air(fqn, value):
    doc = {'schema': 11, 'zig_version': '0.16.0', 'name': fqn, 'body': [], 'types': [], 'value': value}
    return json.dumps(doc, indent=1) + '\n'


class Fake:
    """A repository with examples, goldens, fixtures and a stub compiler."""

    def __init__(self, tmp):
        self.root = Path(tmp) / 'repo'
        self.log = Path(tmp) / 'stub.log'
        self.stub = Path(tmp) / 'zig'
        self.stub.write_text(STUB)
        self.stub.chmod(0o755)
        os.environ['STUB_LOG'] = str(self.log)

    def write(self, path, text):
        path = self.root / path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def source(self, path, functions, fail=False):
        self.write(path, json.dumps({'functions': functions, 'fail': fail}))

    def manifest(self, body):
        self.write('tests/roadmap/exporter-equivalence/exports.toml',
                   'default_args = ["-OReleaseSafe", "-target", "x86_64-linux"]\n' + body)

    def run(self, *args):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = EQ['main'](['run', '--zig', '0.16.0=%s' % self.stub, '--version', '0.16.0', '--suite', 'fixture',
                               '--jobs', '1', *args], root=self.root)
        return code, out.getvalue()

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []


FIXTURE = '''
[[export]]
id = "fx"
versions = ["0.16.0"]
dir = "fx/air/{version}"
source = "fx/fx.zig"
filter = "fx."
compare = "exact"
'''


class ManifestTest(unittest.TestCase):
    def test_repository_manifest_is_valid_and_present(self):
        entries, excluded = EQ['load_manifest'](ROOT)
        for entry in entries:
            self.assertTrue((ROOT / entry['source']).is_file(), entry['source'])
            if 'filter_file' in entry:
                self.assertTrue((ROOT / entry['filter_file']).is_file(), entry['filter_file'])
            for version in entry['versions']:
                directory = ROOT / entry['dir'].replace('{version}', version)
                self.assertTrue(any(directory.glob('*.json')), directory)
        self.assertTrue(excluded)

    def test_every_compiler_fixture_root_is_covered(self):
        """scripts/coverage.py's reviewed compiler-export roots are each re-exported or excluded."""
        source = (ROOT / 'scripts/coverage.py').read_text()
        roots = ast.literal_eval(re.search(r'COMPILER_FIXTURE_ROOTS = (\{.*?\n\})', source, re.S).group(1))
        entries, excluded = EQ['load_manifest'](ROOT)
        dirs = {e['dir'] for e in entries}
        reasons = {e['root'] for e in excluded}
        self.assertFalse(dirs & reasons, 'a root is both exported and excluded')
        uncovered = sorted(r for r in roots if r not in dirs and r not in reasons)
        self.assertEqual(uncovered, [], 'add these to tests/roadmap/exporter-equivalence/exports.toml')

    def test_rejects_malformed_entries(self):
        with tempfile.TemporaryDirectory() as tmp:
            fake = Fake(tmp)
            for body, message in ((FIXTURE.replace('"exact"', '"bytes"'), 'compare'),
                                  (FIXTURE.replace('versions = ["0.16.0"]', 'versions = ["0.13.0"]'), 'versions'),
                                  (FIXTURE + FIXTURE, 'duplicate'),
                                  (FIXTURE.replace('compare', 'comparison'), 'unknown keys'),
                                  (FIXTURE.replace('"0.16.0"]', '"0.16.0", "0.15.2"]').replace('{version}', 'v'),
                                   '{version}')):
                fake.manifest(body)
                with self.assertRaisesRegex(EQ['Failure'], re.escape(message)):
                    EQ['load_manifest'](fake.root)


class GoldenTest(unittest.TestCase):
    def test_commands_follow_check_sh(self):
        with tempfile.TemporaryDirectory() as tmp:
            fake = Fake(tmp)
            fake.write('examples/demo/demo.zig', '')
            fake.write('examples/demo/filter', 'std.a\n\nstd.b\n')
            fake.write('examples/demo/filter-0.16.0', 'std.c\n')
            fake.write('examples/demo/zig-versions', '0.15.2\n0.16.0\n')
            fake.write('examples/asm/asm.zig', '')
            exports = EQ['golden_exports'](fake.root, ('0.14.1', '0.16.0'), host=('linux', 'aarch64'))
            self.assertEqual([(e.id, e.version) for e in exports], [('golden/demo', '0.16.0')])
            demo = exports[0]
            self.assertEqual(demo.filter, 'demo.,std.a,std.b,std.c')
            self.assertEqual(demo.args, ('-OReleaseSafe', '-fno-error-tracing', '-mcpu=baseline'))
            self.assertEqual(demo.committed, ('tests/golden/demo/air', 'tests/golden/0.16.0/demo/air',
                                              'tests/golden/0.16.0/demo/air-linux',
                                              'tests/golden/0.16.0/demo/air-linux-aarch64'))
            exports = EQ['golden_exports'](fake.root, ('0.15.2',), host=('linux', 'x86_64'))
            self.assertEqual([(e.id, e.args) for e in exports],
                             [('golden/asm', ('-OReleaseSafe', '-fno-error-tracing')),
                              ('golden/demo', ('-OReleaseSafe', '-fno-error-tracing'))])
            self.assertEqual(exports[1].filter, 'demo.,std.a,std.b')


class RunTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.fake = Fake(self.tmp.name)
        self.fake.source('fx/fx.zig', {'fx.a': 1, 'fx.b': 2, 'other.c': 3})
        self.fake.write('fx/air/0.16.0/fx.a.json', air('fx.a', 1))
        self.fake.write('fx/air/0.16.0/fx.b.json', air('fx.b', 2))
        self.fake.manifest(FIXTURE)

    def tearDown(self):
        self.tmp.cleanup()

    def test_identical_alternative_and_committed(self):
        code, out = self.fake.run('--alt', 'self')
        self.assertEqual(code, 0, out)
        self.assertIn('ok       fx@0.16.0: 2 files; alt: 2 same; committed (exact): 2 same', out)
        calls = self.fake.calls()
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0]['filter'], 'fx.')
        self.assertEqual(calls[0]['argv'][:5], ['build-obj', '-fno-emit-bin', '-OReleaseSafe', '-target', 'x86_64-linux'])
        self.assertEqual(calls[0]['argv'][5], 'fx/fx.zig')
        self.assertEqual(calls[0]['argv'][6], '--cache-dir')

    def test_alternative_that_differs_fails(self):
        code, out = self.fake.run('--alt', '{zig} --mutate')
        self.assertEqual(code, 1, out)
        self.assertIn('alt-differs fx@0.16.0', out)
        self.assertIn('alt: 0 same, 2 differ', out)

    def test_failing_export_fails(self):
        self.fake.source('fx/fx.zig', {}, fail=True)
        code, out = self.fake.run()
        self.assertEqual(code, 1, out)
        self.assertIn('export-failed fx@0.16.0', out)
        self.assertIn('stub: export failed', out)

    def test_stale_committed_file_is_reported(self):
        self.fake.write('fx/air/0.16.0/fx.b.json', air('fx.b', 7))
        self.fake.write('fx/air/0.16.0/fx.gone.json', air('fx.gone', 0))
        report = Path(self.tmp.name) / 'report.json'
        code, out = self.fake.run('--report', str(report))
        self.assertEqual(code, 0, out)
        self.assertIn('committed (exact): 1 same, 1 differ, 1 missing', out)
        row = json.loads(report.read_text())['rows'][0]
        self.assertEqual(row['status'], 'committed-differs')
        self.assertEqual(row['committed']['differ'], ['fx.b.json'])
        self.assertIn('committed_normalized', row)
        code, out = self.fake.run('--require-committed')
        self.assertEqual(code, 1, out)

    def test_subset_allows_extra_fresh_files(self):
        self.fake.manifest(FIXTURE.replace('filter = "fx."', 'filter = "fx.,other."').replace('"exact"', '"subset"'))
        code, out = self.fake.run()
        self.assertEqual(code, 0, out)
        self.assertIn('committed (subset): 2 same, 1 extra', out)
        self.fake.manifest(FIXTURE.replace('filter = "fx."', 'filter = "fx.,other."'))
        code, out = self.fake.run('--require-committed')
        self.assertEqual(code, 1, out)

    def test_filter_from_committed(self):
        self.fake.source('fx/fx.zig', {'fx.a__anon_12': 1, 'fx.a__anon_40': 5, 'fx.b': 2, 'fx.c': 3})
        self.fake.write('fx/air/0.16.0/fx.a.json', air('fx.a__anon_12', 1))
        self.fake.manifest(FIXTURE.replace('filter = "fx."', 'filter_from_committed = true').replace('"exact"', '"subset"'))
        code, out = self.fake.run()
        self.assertEqual(code, 0, out)
        self.assertEqual(self.fake.calls()[0]['filter'], 'fx.a__anon_,fx.b')

    def test_list(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            EQ['main'](['list', '--suite', 'fixture'], root=self.fake.root)
        self.assertEqual(out.getvalue(), "fx@0.16.0 [exact] ZIG_AIR_JSON_DIR=<out> ZIG_AIR_JSON_FILTER=fx. <zig> "
                                         "build-obj -fno-emit-bin -OReleaseSafe -target x86_64-linux fx/fx.zig\n")


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    unittest.main()
