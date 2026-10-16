#!/usr/bin/env python3
"""Compile standalone Lean modules, reusing an .olean built from the same inputs (docs/build-cache.md).

  lean_cache.py compile --root ROOT --out LIB FILE...

compiles each FILE, in order (a later file may import an earlier one), as
`lake env lean -R ROOT -o LIB/<module>.olean FILE`. With AIR2LEAN_CAS_DIR set, the .olean is
stored in the shared cache (kind `audit`) and copied from there when its key matches: the source,
the module name, the toolchain and every file Lean reads for the import closure
(docs/build-cache.md has the key and why a hit is right). Inputs that cannot be keyed (an .olean
layout this reader does not know, an import that does not resolve) compile uncached.
"""
import argparse
import importlib.util
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cas  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location('air2lean_lean_deps', ROOT / 'scripts/lean-deps.py')
DEPS = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(DEPS)
SCHEMA = 1
KIND = 'audit'
# The .olean layout this reader knows (Lean 4 `olean_header` version 2): "olean", the version byte,
# a flags byte, the Lean version (33 bytes), the githash (40 bytes), the base address the file is
# mapped at; then the compacted object graph, whose first word points to the root ModuleData.
OLEAN_VERSION = 2
BASE_OFFSET, OBJECTS = 0x50, 0x60
MAX_CTOR_TAG, ARRAY_TAG, STRING_TAG = 244, 246, 249
# What a module-system module has next to X.olean, and Lean reads with it.
COMPANIONS = ('.olean.server', '.olean.private', '.ir', '.ir.sig')


class Unsupported(Exception):
    """The inputs cannot be keyed: compile uncached."""


def olean_imports(path):
    """The modules an .olean imports (`ModuleData.imports`), read from its object graph. Every
    object on the way is checked against the layout above, so another layout raises Unsupported
    instead of giving a wrong list."""
    try:
        fd = os.open(path, os.O_RDONLY)
        try:
            length = os.fstat(fd).st_size
            # The compactor writes the root's first field (the imports) first: near the start.
            start = os.pread(fd, min(length, 1 << 16), 0)

            def read(offset, count):
                """`count` bytes at `offset`, all inside the file."""
                if 0 <= offset and offset + count <= len(start):
                    return start[offset:offset + count]
                data = os.pread(fd, count, offset) if 0 <= offset and offset + count <= length else b''
                if len(data) != count:
                    raise ValueError('read of %d bytes at %#x outside the file' % (count, offset))
                return data
            return _imports(read)
        finally:
            os.close(fd)
    except (OSError, ValueError, struct.error, UnicodeDecodeError) as error:
        raise Unsupported('%s: unreadable .olean (%s)' % (path, error)) from None


def _imports(read):
    header = read(0, OBJECTS)
    if header[:5] != b'olean' or header[5] != OLEAN_VERSION:
        raise ValueError('not a version-%d .olean' % OLEAN_VERSION)
    base, root = struct.unpack_from('<QQ', header, BASE_OFFSET)
    word = lambda offset: struct.unpack('<Q', read(offset, 8))[0]

    def obj(ptr, tags, fields=None):
        """Offset of the object at ptr; its tag must be in tags (and its field count `fields`)."""
        offset = ptr - base
        if ptr & 7 or offset < OBJECTS:
            raise ValueError('pointer %#x outside the object graph' % ptr)
        _, size, other, tag = struct.unpack('<iHBB', read(offset, 8))
        if tag not in tags or (fields is not None and other != fields):
            raise ValueError('unexpected object (tag %d, %d fields) at %#x' % (tag, other, offset))
        if tag <= MAX_CTOR_TAG:
            if size < 8 + 8 * other:
                raise ValueError('constructor at %#x overruns its object' % offset)
            read(offset, size)  # the whole constructor lies inside the file
        return offset, tag

    def field(offset, index):
        return word(offset + 8 + 8 * index)

    def string(ptr):
        offset, _ = obj(ptr, {STRING_TAG})
        data = read(offset + 32, word(offset + 8))
        if not data or data[-1] != 0:
            raise ValueError('malformed string at %#x' % offset)
        return data[:-1].decode('utf-8')

    def name(ptr):
        parts = []
        while ptr != 1:  # lean_box(0): Name.anonymous
            offset, tag = obj(ptr, {1, 2}, fields=2)  # Name.str / Name.num: prefix, component
            component = field(offset, 1)
            if tag == 2 and not component & 1:
                raise ValueError('big numeric name component')
            parts.append(string(component) if tag == 1 else str(component >> 1))
            if len(parts) > 256:
                raise ValueError('name too long')
            ptr = field(offset, 0)
        if not parts:
            raise ValueError('anonymous import')
        return '.'.join(reversed(parts))

    module_data, _ = obj(root, {0})  # ModuleData; its first field is `imports : Array Import`
    array, _ = obj(field(module_data, 0), {ARRAY_TAG})
    size = word(array + 8)
    # Import: `module : Name`, then its Bool flags as scalars.
    return [name(field(obj(word(array + 24 + 8 * i), {0}, fields=1)[0], 0)) for i in range(size)]


def source_imports(path):
    """The modules a Lean source imports (scripts/lean-deps.py), plus `Init` unless it is a
    `prelude` module."""
    prelude = re.search(r'^\s*prelude\b', Path(path).read_text(encoding='utf-8'), re.M)
    return sorted(DEPS.imports(Path(path)) | (set() if prelude else {'Init'}))


class SearchPath:
    """Module resolution as Lean does it: the LEAN_PATH directories in order (relative to the
    repository root, where Lean runs), then the toolchain's lib/lean. Identities and imports are
    memoized, so build one per run."""

    def __init__(self, lean_path, sysroot):
        self.sysroot = Path(sysroot).resolve()
        self.lib = self.sysroot / 'lib/lean'
        self.dirs = [(ROOT / p).resolve() for p in lean_path.split(os.pathsep) if p] + [self.lib]
        libraries = sorted(f for f in self.lib.iterdir()
                           if f.is_file() and not f.name.endswith(('.olean', '.ilean', *COMPANIONS)))
        # The toolchain's executables and the shared libraries next to its modules.
        self.toolchain = {'bin': cas.tree_stat(self.sysroot / 'bin'),
                          'lib': [stat_row(f, self.lib) for f in libraries]}
        self._packages, self._modules = {}, {}

    def resolve(self, module):
        """Lean's SearchPath.findWithExt: the first directory that has the module's root package
        (a directory or an .olean of that name) is the one read, even if the module is not there."""
        package = module.split('.')[0]
        if package not in self._packages:
            self._packages[package] = next(
                (d for d in self.dirs if (d / package).is_dir() or (d / (package + '.olean')).exists()), None)
        found = self._packages[package]
        path = found / (module.replace('.', '/') + '.olean') if found else None
        if path is None or not path.is_file():
            raise Unsupported('no .olean for ' + module)
        return path

    def read(self, module):
        """(identity, imports) of `module`: what Lean reads for it (its .olean and companions)."""
        if module not in self._modules:
            path = self.resolve(module)
            stem = path.with_suffix('')
            files = [path] + [p for p in (stem.with_name(stem.name + s) for s in COMPANIONS) if p.is_file()]
            toolchain = path.is_relative_to(self.lib)
            self._modules[module] = ([stat_row(f, self.lib) if toolchain else cas.sha256_file(f) for f in files],
                                     olean_imports(path))
        return self._modules[module]

    def forget(self, module):
        """Drop what is memoized for `module` (its .olean is being written)."""
        self._modules.pop(module, None)

    def closure(self, roots):
        """module -> identity of every module that importing `roots` reads."""
        seen, todo = {}, list(roots)
        while todo:
            module = todo.pop()
            if module not in seen:
                seen[module], imports = self.read(module)
                todo.extend(imports)
        return seen

    def key(self, kind, roots, **inputs):
        """Key of a `kind` result that imports `roots` and depends on `inputs`."""
        return cas.digest({'schema': SCHEMA, 'kind': kind, 'roots': sorted(roots), 'inputs': inputs,
                           'toolchain': self.toolchain, 'modules': sorted(self.closure(roots).items())})


def stat_row(path, base):
    """An installed file as scripts/cas.py identifies installations: path, size, mtime."""
    st = path.stat()
    return [path.relative_to(base).as_posix(), st.st_size, st.st_mtime_ns]


def lake_env(name):
    return subprocess.run(['lake', 'env', 'printenv', name], cwd=ROOT, check=True, text=True,
                          capture_output=True).stdout.strip()


def compile_modules(files, root, out, store=None):
    """Compile each file into out/<module>.olean, in order; with a store (cas.Store), an unchanged
    module is copied from it. Returns the number of modules served from the store."""
    search = SearchPath(lake_env('LEAN_PATH'), lake_env('LEAN_SYSROOT')) if store else None
    root, hits = Path(root).resolve(), 0
    for file in (Path(f).resolve() for f in files):
        relative = file.relative_to(root).with_suffix('')
        module, target = '.'.join(relative.parts), Path(out).resolve() / relative.with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        key = hit = None
        if store:
            search.forget(module)  # A later file's key must see this run's .olean.
            imports = source_imports(file)
            try:
                key = search.key('olean', imports, module=module, source=cas.sha256_file(file))
                hit = store.lookup(KIND, key)
            except Unsupported as error:
                print('lean_cache: %s compiled uncached: %s' % (module, error), file=sys.stderr)
        if hit:
            staged = target.with_name('.%s.%d' % (target.name, os.getpid()))
            shutil.copyfile(hit / 'module.olean', staged)
            os.replace(staged, target)
            hits += 1
            continue
        subprocess.run(['lake', 'env', 'lean', '-R', str(root), '-o', str(target), str(file)], cwd=ROOT, check=True)
        if key:
            publish(store, key, module, target, imports)
    return hits


def publish(store, key, module, olean, imports):
    """Store a compiled module, unless it imports anything its key does not cover."""
    try:
        built = olean_imports(olean)
    except Unsupported as error:
        print('lean_cache: %s not stored: %s' % (module, error), file=sys.stderr)
        return
    if not set(built) <= set(imports):
        print('lean_cache: %s not stored: it imports %s, its source header %s' % (module, built, imports),
              file=sys.stderr)
        return
    staged = store.stage(KIND, key)
    try:
        shutil.copyfile(olean, staged / 'module.olean')
        store.publish(staged, KIND, key, {'kind': KIND, 'what': 'olean', 'module': module, 'key': key,
                                          'created': time.time()})
    finally:
        shutil.rmtree(staged, ignore_errors=True)  # Gone after a publish.


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('compile', help='compile standalone modules, in order')
    p.add_argument('--root', type=Path, required=True, help='`lean -R` root of the files')
    p.add_argument('--out', type=Path, required=True, help='library directory of the .olean files')
    p.add_argument('files', nargs='+', type=Path)
    a = parser.parse_args(argv)
    store = cas.Store(cas.cas_dir()) if cas.cas_dir() else None
    try:
        hits = compile_modules(a.files, a.root, a.out, store)
    except subprocess.CalledProcessError as error:
        print('lean_cache: %s exited %d' % (' '.join(map(str, error.cmd[:3])), error.returncode), file=sys.stderr)
        return 1
    print('lean_cache: %d modules, %d from the cache' % (len(a.files), hits), file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
