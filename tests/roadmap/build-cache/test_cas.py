#!/usr/bin/env python3
"""scripts/cas.py (shared content-addressed cache) and scripts/regen.py (step table) regressions.

No Zig, Lake or Lean runs: compilers are stub scripts, the store is a temporary directory.
"""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


cas = load('cas', 'cas.py')
regen = load('regen', 'regen.py')

# A stand-in patched compiler: writes one AIR file per run and counts its runs.
STUB = '''#!/bin/sh
n=$(cat "$COUNT" 2>/dev/null || echo 0); echo $((n + 1)) > "$COUNT"
mkdir -p "$ZIG_AIR_JSON_DIR"
printf '{"name":"%s","args":"%s"}' "$ZIG_AIR_JSON_FILTER" "$*" > "$ZIG_AIR_JSON_DIR/out.json"
echo warning >&2
'''


class Env:
    """Temporarily set (value) or unset (None) environment variables."""
    def __init__(self, **values):
        self.values, self.saved = values, {}

    def __enter__(self):
        for k, v in self.values.items():
            self.saved[k] = os.environ.get(k)
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v

    def __exit__(self, *exc):
        for k, v in self.saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v


class CasTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)

    def test_unset_is_off(self):
        for value in (None, ''):
            with Env(AIR2LEAN_CAS_DIR=value):
                self.assertIsNone(cas.cas_dir())
                self.assertEqual(cas.lake_env(), {})
                self.assertEqual(cas.gc(0, 0), (0, 0))

    def test_set_enables_lake_cache_below_root(self):
        with Env(AIR2LEAN_CAS_DIR=str(self.tmp / 'c')):
            env = cas.lake_env()
        self.assertEqual(env['LAKE_ARTIFACT_CACHE'], 'true')
        self.assertEqual(env['LAKE_RESTORE_ARTIFACTS'], 'true')
        self.assertEqual(Path(env['LAKE_CACHE_DIR']), (self.tmp / 'c').resolve() / 'lake')

    def test_zig_patch_inputs_track_every_build_input(self):
        repo = self.tmp / 'repo'
        shutil.copytree(ROOT / 'zig-patch', repo / 'zig-patch')
        base = cas.digest(cas.zig_patch_inputs(repo, '0.16.0'))
        for rel in ('zig-patch/air-json/json.zig', 'zig-patch/0.16.0/hook.patch', 'zig-patch/build.sh',
                    'zig-patch/lock.sh', 'zig-patch/toml-get.sh'):
            path = repo / rel
            saved = path.read_bytes()
            path.write_bytes(saved + b'\n')
            self.assertNotEqual(cas.digest(cas.zig_patch_inputs(repo, '0.16.0')), base, rel)
            path.write_bytes(saved)
        # Another version's patch or pin is not an input of this one.
        (repo / 'zig-patch/0.15.2/hook.patch').write_text('changed')
        self.assertEqual(cas.digest(cas.zig_patch_inputs(repo, '0.16.0')), base)
        versions = repo / 'zig-patch/versions.toml'
        versions.write_text(versions.read_text().replace('hook = "0.16.0/hook.patch"',
                                                         'hook = "0.16.0/hook.patch"\nextra = "x"'))
        self.assertNotEqual(cas.digest(cas.zig_patch_inputs(repo, '0.16.0')), base)

    def store_with_compiler(self):
        store = cas.Store(self.tmp / 'store')
        staged = store.stage('zig', 'v-key')
        (staged / 'prefix/bin').mkdir(parents=True)
        zig = staged / 'prefix/bin/zig'
        zig.write_text(STUB)
        zig.chmod(0o755)
        entry = store.publish(staged, 'zig', 'v-key', {'kind': 'zig', 'key': 'k1'})
        return store, entry / 'prefix/bin/zig'

    def test_publish_is_atomic_and_first_writer_wins(self):
        store, _ = self.store_with_compiler()
        self.assertIsNotNone(store.lookup('zig', 'v-key'))
        again = store.stage('zig', 'v-key')
        (again / 'other').write_text('x')
        store.publish(again, 'zig', 'v-key', {'kind': 'zig', 'key': 'k1'})
        self.assertFalse((store.entry('zig', 'v-key') / 'other').exists())
        self.assertFalse(again.exists())
        self.assertIsNone(store.lookup('zig', 'missing'))
        half = store.entry('zig', 'half')
        half.mkdir()  # No marker: never a hit.
        self.assertIsNone(store.lookup('zig', 'half'))

    def export(self, zig, out, *args, filter_='m.'):
        source = self.tmp / 'mod/m.zig'
        source.parent.mkdir(exist_ok=True)
        if not source.exists():
            source.write_text('pub fn f() void {}\n')
        env = dict(os.environ, AIR2LEAN_CAS_DIR=str(self.tmp / 'store'), ZIG_AIR_JSON_DIR=str(out),
                   ZIG_AIR_JSON_FILTER=filter_, COUNT=str(self.tmp / 'count'))
        done = subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/cas.py'), 'air', '--', str(zig), 'build-obj',
                               '-fno-emit-bin', '-OReleaseSafe', *args, str(source)], env=env,
                              capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn('warning', done.stderr)
        return (out / 'out.json').read_text()

    def runs(self):
        return int((self.tmp / 'count').read_text())

    def test_air_export_hits_only_on_equal_inputs(self):
        _, zig = self.store_with_compiler()
        first = self.export(zig, self.tmp / 'a1')
        self.assertEqual(self.export(zig, self.tmp / 'a2'), first)
        self.assertEqual(self.runs(), 1)
        self.export(zig, self.tmp / 'a3', filter_='m.f')            # filter is part of the key
        self.export(zig, self.tmp / 'a4', '-target', 'x86_64-linux')  # so are the flags
        self.assertEqual(self.runs(), 3)
        (self.tmp / 'mod/helper.zig').write_text('// imported sibling\n')  # module directory content
        self.export(zig, self.tmp / 'a5')
        self.assertEqual(self.runs(), 4)

    def test_air_export_passes_through_what_it_cannot_key(self):
        _, zig = self.store_with_compiler()
        out = self.tmp / 'busy'
        out.mkdir()
        (out / 'existing.json').write_text('{}')  # the exporter merges into existing files
        self.export(zig, out)
        self.export(zig, self.tmp / 'b1', '-lc')    # libc: depends on host headers
        self.export(zig, self.tmp / 'b2', '-lc')
        self.assertEqual(self.runs(), 3)
        stock = self.tmp / 'stock-zig'             # not a cache entry: never cached
        shutil.copy(zig, stock)
        self.export(stock, self.tmp / 'b3')
        self.export(stock, self.tmp / 'b4')
        self.assertEqual(self.runs(), 5)

    def native(self, zig, out, *args, store=True):
        env = dict(os.environ, COUNT=str(self.tmp / 'ncount'))
        env.pop('AIR2LEAN_CAS_DIR', None)
        if store:
            env['AIR2LEAN_CAS_DIR'] = str(self.tmp / 'store')
        done = subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/cas.py'), 'native', '--', str(zig),
                               'build-exe', '-OReleaseSafe', '-mcpu=baseline', f'-femit-bin={out}', *args,
                               str(self.tmp / 'mod/m.zig')], env=env, capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        return out.read_text()

    def test_native_build_hits_only_on_equal_inputs(self):
        zig = self.tmp / 'stock/zig'
        (self.tmp / 'stock/lib').mkdir(parents=True)
        zig.write_text('#!/bin/sh\nn=$(cat "$COUNT" 2>/dev/null || echo 0); echo $((n + 1)) > "$COUNT"\n'
                       'for a; do case $a in -femit-bin=*) o=${a#-femit-bin=};; esac; done\n'
                       'echo "built $*" > "$o"; echo note >&2\n')
        zig.chmod(0o755)
        (self.tmp / 'mod').mkdir(exist_ok=True)
        (self.tmp / 'mod/m.zig').write_text('pub fn f() void {}\n')

        def runs():
            return int((self.tmp / 'ncount').read_text())
        first = self.native(zig, self.tmp / 'n1')
        self.assertEqual(self.native(zig, self.tmp / 'n2'), first)             # hit
        self.assertEqual(runs(), 1)
        self.native(zig, self.tmp / 'n3', '-target', 'x86_64-linux')            # flags are part of the key
        (self.tmp / 'mod/helper.zig').write_text('// imported sibling\n')       # so is the module directory
        self.native(zig, self.tmp / 'n4')
        self.assertEqual(runs(), 3)
        (self.tmp / 'mod/embed.zig').write_text('const x = @embedFile("data");\n')  # cannot be keyed: uncached
        self.native(zig, self.tmp / 'n5')
        self.native(zig, self.tmp / 'n6')
        self.assertEqual(runs(), 5)
        (self.tmp / 'mod/embed.zig').unlink()
        self.native(zig, self.tmp / 'n7', store=False)                          # no cache directory: plain run
        self.native(zig, self.tmp / 'n8', store=False)
        self.assertEqual(runs(), 7)

    def test_gc_evicts_least_recently_used_first(self):
        store = cas.Store(self.tmp / 'store')
        for name, age in (('old', 9000), ('new', 7200)):
            staged = store.stage('air', name)
            (staged / 'files').mkdir()
            (staged / 'files/blob').write_bytes(b'x' * 4096)
            entry = store.publish(staged, 'air', name, {'kind': 'air', 'key': name})
            stamp = time.time() - age
            for f in (cas.MARKER, cas.USED):
                os.utime(entry / f, (stamp, stamp))
        with Env(AIR2LEAN_CAS_DIR=str(self.tmp / 'store')):
            total = cas.total_size(store)
            cas.gc(total - 1, 3600)
            self.assertIsNone(store.lookup('air', 'old'))
            self.assertIsNotNone(store.lookup('air', 'new'))  # lookup refreshes its stamp
            cas.gc(0, 3600)
            self.assertIsNotNone(store.lookup('air', 'new'))  # used within --min-age


class RegenTests(unittest.TestCase):
    def test_every_step_has_a_scope_and_provenance_is_last(self):
        names = [s[0] for s in regen.STEPS]
        self.assertEqual(names[-1], 'provenance')
        self.assertEqual(names[0], 'translator')
        self.assertEqual(len(names), len(set(names)))
        for name, scope, outputs, function in regen.STEPS:
            self.assertIn(scope, ('pr', 'tree'), name)
            self.assertTrue(function is not None or name == 'provenance', name)

    def test_whole_tree_files_are_tree_scoped(self):
        scopes = {s[0]: s[1] for s in regen.STEPS}
        for name in ('coverage', 'premises', 'inventory', 'support-matrix', 'claims', 'provenance'):
            self.assertEqual(scopes[name], 'tree', name)
        for name in ('gen', 'ci-matrix', 'trust-report'):
            self.assertEqual(scopes[name], 'pr', name)

    def test_list_json(self):
        done = subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/regen.py'), '--list', '--json'],
                              capture_output=True, text=True, check=True)
        rows = json.loads(done.stdout)
        self.assertEqual([r['step'] for r in rows], [s[0] for s in regen.STEPS])


if __name__ == '__main__':
    unittest.main()
