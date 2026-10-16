#!/usr/bin/env python3
"""scripts/lean_cache.py regressions: the .olean import reader, the import-closure key and the
cached compile of standalone modules.

No Lean or Lake runs: .olean files are written in the version-2 layout by `write_olean`, and
`lake` is a stub that compiles a source into such a file. When the repository's Lake build is
present, the reader is also checked against every built module's source header.
"""
import importlib.util
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


lean_cache = load('lean_cache', 'lean_cache.py')
cas = lean_cache.cas


def write_olean(path, imports, payload=''):
    """A version-2 .olean whose ModuleData imports `imports`; `payload` changes its bytes only."""
    base, objects = 0x7f0000000000, bytearray()

    def put(data):
        address = base + 0x60 + len(objects)
        objects.extend(data + b'\0' * (-len(data) % 8))
        return address

    def head(size, fields, tag):
        return struct.pack('<iHBB', 0, size, fields, tag)

    def string(text):
        data = text.encode() + b'\0'
        return put(head(1, 0, 249) + struct.pack('<QQQ', len(data), len(data), len(text)) + data)

    def name(dotted):
        ptr = 1  # Name.anonymous
        for part in dotted.split('.'):
            component = (int(part) << 1) | 1 if part.isdigit() else string(part)
            ptr = put(head(32, 2, 2 if part.isdigit() else 1) + struct.pack('<QQQ', ptr, component, 0))
        return ptr

    entries = [put(head(24, 1, 0) + struct.pack('<QQ', name(m), 0)) for m in imports]
    array = put(head(1, 0, 246) + struct.pack('<QQ', len(entries), len(entries))
                + b''.join(struct.pack('<Q', e) for e in entries))
    root = put(head(56, 5, 0) + struct.pack('<5QQ', array, string(payload), 1, 1, 1, 0))
    header = b'olean' + bytes([2, 1]) + b'4.34.0'.ljust(33, b'\0') + b'0' * 40 + struct.pack('<QQ', base, root)
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_bytes(header + bytes(objects))


# A stand-in `lake`: `env printenv NAME` prints the variable; `env lean -R ROOT -o OUT FILE`
# writes an .olean that imports the source's header imports (and those of `--extra` lines) and
# logs FILE.
STUB = '''#!{python} -B
import os, re, sys
sys.path.insert(0, {here!r})
from test_lean_cache import write_olean
args = sys.argv[1:]
if args[:2] == ['env', 'printenv']:
    print(os.environ.get(args[2], ''))
elif args[:2] == ['env', 'lean']:
    root, out, file = args[3], args[5], args[6]
    text = open(file).read()
    imports = ['Init'] + re.findall(r'^import (\\S+)$', text, re.M) + re.findall(r'^--extra (\\S+)$', text, re.M)
    write_olean(out, imports, payload=text)
    with open(os.environ['STUB_LOG'], 'a') as log:
        log.write(os.path.relpath(os.path.realpath(file), os.path.realpath(root)) + '\\n')
else:
    sys.exit('stub lake: unexpected ' + ' '.join(args))
'''


class Env:
    def __init__(self, **values):
        self.values, self.saved = values, {}

    def __enter__(self):
        for k, v in self.values.items():
            self.saved[k] = os.environ.get(k)
            os.environ[k] = v

    def __exit__(self, *exc):
        for k, v in self.saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v


class Library(unittest.TestCase):
    """A toolchain (bin/, lib/lean/Init.olean) and a project library in a temporary directory."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.base = Path(temp.name)
        self.sysroot, self.lib = self.base / 'toolchain', self.base / 'lib'
        (self.sysroot / 'bin').mkdir(parents=True)
        (self.sysroot / 'bin/lean').write_text('lean')
        write_olean(self.sysroot / 'lib/lean/Init.olean', [])
        write_olean(self.lib / 'A.olean', ['Init'])
        write_olean(self.lib / 'B.olean', ['Init', 'A'])
        write_olean(self.lib / 'C.olean', ['Init'])

    def key(self, *roots, lean_path=None):
        search = lean_cache.SearchPath(lean_path or str(self.lib), self.sysroot)
        return search.key('olean', list(roots))


class ReaderTests(Library):
    def test_reads_the_import_names(self):
        path = self.base / 'M.olean'
        write_olean(path, ['Init', 'Lean.Elab.Command', 'Mathlib.Data.Fin.1'])
        self.assertEqual(lean_cache.olean_imports(path), ['Init', 'Lean.Elab.Command', 'Mathlib.Data.Fin.1'])

    def test_another_layout_is_unsupported(self):
        path = self.base / 'M.olean'
        write_olean(path, ['Init'])
        good = path.read_bytes()
        corruptions = {'magic': b'oleaN' + good[5:], 'version': good[:5] + b'\3' + good[6:],
                       'truncated': good[:-16], 'root pointer': good[:0x58] + struct.pack('<Q', 8) + good[0x60:]}
        for what, data in corruptions.items():
            with self.subTest(what):
                path.write_bytes(data)
                with self.assertRaises(lean_cache.Unsupported):
                    lean_cache.olean_imports(path)

    @unittest.skipUnless((ROOT / '.lake/build/lib/lean/ZigLean.olean').is_file(), 'no Lake build')
    def test_built_modules_import_what_their_source_header_says(self):
        built = ROOT / '.lake/build/lib/lean'
        checked = 0
        for olean in sorted(built.rglob('*.olean')):
            source = ROOT / olean.relative_to(built).with_suffix('.lean')
            if source.is_file():
                with self.subTest(str(source.relative_to(ROOT))):
                    self.assertLessEqual(set(lean_cache.olean_imports(olean)), set(lean_cache.source_imports(source)))
                    checked += 1
        self.assertGreater(checked, 100)


class KeyTests(Library):
    def test_key_covers_indirect_imports_only(self):
        before = self.key('B')
        write_olean(self.lib / 'C.olean', ['Init'], payload='changed')  # not in B's closure
        self.assertEqual(self.key('B'), before)
        write_olean(self.lib / 'A.olean', ['Init'], payload='changed')  # imported by B
        self.assertNotEqual(self.key('B'), before)

    def test_key_follows_the_file_lean_resolves(self):
        shadow = self.base / 'shadow'
        write_olean(shadow / 'A.olean', ['Init'], payload='shadow')
        path = '%s%s%s' % (shadow, os.pathsep, self.lib)
        before = self.key('B', lean_path=path)
        self.assertNotEqual(before, self.key('B'))
        write_olean(self.lib / 'A.olean', ['Init'], payload='changed')  # shadowed: never read
        self.assertEqual(self.key('B', lean_path=path), before)

    def test_key_covers_the_toolchain(self):
        before = self.key('B')
        (self.sysroot / 'bin/lean').write_text('another lean')
        self.assertNotEqual(self.key('B'), before)
        before = self.key('B')
        init = self.sysroot / 'lib/lean/Init.olean'
        os.utime(init, ns=(init.stat().st_atime_ns, init.stat().st_mtime_ns + 1))
        self.assertNotEqual(self.key('B'), before)

    def test_missing_module_is_unsupported(self):
        with self.assertRaises(lean_cache.Unsupported):
            self.key('Missing')


class CompileTests(Library):
    def setUp(self):
        super().setUp()
        stubs = self.base / 'bin'
        stubs.mkdir()
        (stubs / 'lake').write_text(STUB.format(python=sys.executable, here=str(HERE)))
        (stubs / 'lake').chmod(0o755)
        self.log, self.src, self.out = self.base / 'log', self.base / 'src', self.base / 'out'
        self.source('X/One.lean', 'import A\n')
        self.source('X/Two.lean', 'import C\n')
        self.source('X/Three.lean', 'import X.One\n')
        self.store = cas.Store(self.base / 'store')
        self.env = Env(PATH=str(stubs) + os.pathsep + os.environ['PATH'], STUB_LOG=str(self.log),
                       LEAN_PATH='%s%s%s' % (self.lib, os.pathsep, self.out), LEAN_SYSROOT=str(self.sysroot))

    def source(self, rel, text):
        (self.src / rel).parent.mkdir(parents=True, exist_ok=True)
        (self.src / rel).write_text(text)

    def compile(self, store=True):
        """Compile One, Two, Three; returns the files actually compiled."""
        self.log.unlink(missing_ok=True)
        files = [self.src / 'X' / f for f in ('One.lean', 'Two.lean', 'Three.lean')]
        with self.env:
            lean_cache.compile_modules(files, self.src, self.out, self.store if store else None)
        return self.log.read_text().split() if self.log.exists() else []

    def outputs(self):
        return {p.name: p.read_bytes() for p in sorted(self.out.rglob('*.olean'))}

    def test_unchanged_inputs_are_copied_byte_for_byte(self):
        self.assertEqual(self.compile(), ['X/One.lean', 'X/Two.lean', 'X/Three.lean'])
        compiled = self.outputs()
        for p in self.out.rglob('*.olean'):
            p.unlink()
        self.assertEqual(self.compile(), [])
        self.assertEqual(self.outputs(), compiled)
        self.assertEqual(self.compile(store=False), ['X/One.lean', 'X/Two.lean', 'X/Three.lean'])
        self.assertEqual(self.outputs(), compiled)

    def test_changed_import_recompiles_exactly_its_importers(self):
        self.compile()
        write_olean(self.lib / 'A.olean', ['Init'], payload='changed')
        # One imports A; Three imports One, so A is in its closure too; Two is untouched.
        self.assertEqual(self.compile(), ['X/One.lean', 'X/Three.lean'])
        self.assertEqual(self.compile(), [])
        self.source('X/Two.lean', 'import C\n-- edited\n')
        self.assertEqual(self.compile(), ['X/Two.lean'])

    def test_an_olean_importing_more_than_its_header_is_not_stored(self):
        self.source('X/Two.lean', 'import C\n--extra A\n')
        self.assertEqual(self.compile(), ['X/One.lean', 'X/Two.lean', 'X/Three.lean'])
        self.assertEqual(self.compile(), ['X/Two.lean'])

    def test_unresolved_import_compiles_uncached(self):
        self.source('X/Two.lean', 'import Missing\n')
        self.compile()
        self.assertEqual(self.compile(), ['X/Two.lean'])

    def test_failed_compile_is_not_stored(self):
        self.source('X/Two.lean', 'import C\n')
        broken = self.base / 'bin/lake'
        stub = broken.read_text()
        broken.write_text(stub.replace("elif args[:2] == ['env', 'lean']:",
                                       "elif args[:2] == ['env', 'lean'] and 'Two' in args[6]:\n"
                                       "    sys.exit(1)\nelif args[:2] == ['env', 'lean']:"))
        with self.assertRaises(subprocess.CalledProcessError):
            self.compile()
        broken.write_text(stub)
        self.assertEqual(self.compile(), ['X/Two.lean', 'X/Three.lean'])


if __name__ == '__main__':
    unittest.main()
