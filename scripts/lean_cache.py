#!/usr/bin/env python3
"""Compile standalone Lean modules, reusing an .olean built from the same inputs (docs/build-cache.md).

  lean_cache.py compile [--cache DIR] --root ROOT --out LIB FILE...

compiles each FILE, in order (a later file may import an earlier one), as
`lake env lean -R ROOT -o LIB/<module>.olean FILE`. With --cache DIR (a scripts/cas.py store,
normally $AIR2LEAN_CAS_DIR), the .olean is stored as an `audit/<key>` entry and copied from there
when the key matches. The key is everything the compile reads:
- the source, the module name;
- the toolchain's executables and shared libraries;
- every module of the import closure, with the file Lean resolves it to through its search path
  (the LEAN_PATH directories in order, then the toolchain's lib/lean). A toolchain file is
  identified by path, size and modification time, as scripts/cas.py identifies an installation.
  Any other file is identified by the SHA-256 of its bytes (and of its `.server`/`.private`
  parts).
A changed import, even an indirect one, gives another key. The imports come from the source
header, where a line that only looks like an import just adds a module. An .olean is stored only
after a successful compile, and only when the imports read back from the .olean are among the
keyed ones. When the inputs cannot be keyed (an .olean layout this reader does not know, an
import that does not resolve), the module is compiled uncached.
"""
import argparse
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
SCHEMA = 1
KIND = 'audit'
# The .olean layout this reader knows (Lean 4 `olean_header` version 2): "olean", the version byte,
# a flags byte, the Lean version (33 bytes), the githash (40 bytes), the base address the file is
# mapped at; then the compacted object graph, whose first word points to the root ModuleData.
OLEAN_VERSION = 2
BASE_OFFSET, OBJECTS = 0x50, 0x60
MAX_CTOR_TAG, ARRAY_TAG, STRING_TAG = 244, 246, 249
SPLIT_PARTS = ('.server', '.private')  # module-system companions: X.olean.server, X.olean.private
IMPORT = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.+?)\s*$')


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

            def read(offset, count):
                """`count` bytes at `offset`, all inside the file."""
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
        size = word(offset + 8)
        data = read(offset + 32, size) if size >= 1 else b''
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
    """The modules a Lean source imports, plus `Init` (unless it is a `prelude` module)."""
    text = Path(path).read_text(encoding='utf-8')
    modules = {m for line in text.splitlines() if (match := IMPORT.match(line)) for m in match.group(1).split()}
    return sorted(modules | (set() if re.search(r'^\s*prelude\b', text, re.M) else {'Init'}))


class SearchPath:
    """Module resolution as Lean does it: the LEAN_PATH directories in order, then the toolchain's
    lib/lean. Identities and imports are memoized, so build one per run."""

    def __init__(self, lean_path, sysroot):
        self.sysroot = Path(sysroot).resolve()
        self.lib = self.sysroot / 'lib/lean'
        self.dirs = [Path(p).resolve() for p in lean_path.split(os.pathsep) if p] + [self.lib]
        self._identity, self._imports, self._toolchain = {}, {}, None

    def resolve(self, module):
        relative = module.replace('.', '/') + '.olean'
        found = next((d / relative for d in self.dirs if (d / relative).is_file()), None)
        if found is None:
            raise Unsupported('no .olean for ' + module)
        return found

    def identity(self, module):
        """What Lean reads for `module`: its .olean and split parts."""
        if module not in self._identity:
            path = self.resolve(module)
            files = [path] + [p for p in (path.with_name(path.name + s) for s in SPLIT_PARTS) if p.is_file()]
            self._imports[module] = olean_imports(path)
            if path.is_relative_to(self.lib):
                self._identity[module] = [[f.relative_to(self.lib).as_posix(), f.stat().st_size, f.stat().st_mtime_ns]
                                          for f in files]
            else:
                self._identity[module] = [cas.sha256_file(f) for f in files]
        return self._identity[module]

    def forget(self, module):
        """Drop what is memoized for `module` (its .olean is being written)."""
        self._identity.pop(module, None)
        self._imports.pop(module, None)

    def closure(self, roots):
        """module -> identity of every module that importing `roots` reads."""
        seen, todo = {}, list(roots)
        while todo:
            module = todo.pop()
            if module not in seen:
                seen[module] = self.identity(module)
                todo.extend(self._imports[module])
        return seen

    def toolchain(self):
        """The toolchain's executables and the shared libraries next to its modules."""
        if self._toolchain is None:
            libraries = sorted(f for f in self.lib.iterdir() if f.is_file() and '.olean' not in f.name
                               and not f.name.endswith('.ilean'))
            self._toolchain = {'bin': cas.tree_stat(self.sysroot / 'bin'),
                               'lib': [[f.name, f.stat().st_size, f.stat().st_mtime_ns] for f in libraries]}
        return self._toolchain

    def key(self, kind, roots, **inputs):
        """Key of a `kind` result that imports `roots` and depends on `inputs`."""
        return cas.digest({'schema': SCHEMA, 'kind': kind, 'roots': sorted(roots), 'inputs': inputs,
                           'toolchain': self.toolchain(), 'modules': sorted(self.closure(roots).items())})


def lake_env(name):
    return subprocess.run(['lake', 'env', 'printenv', name], cwd=ROOT, check=True, text=True,
                          capture_output=True).stdout.strip()


def compile_modules(files, root, out, store=None):
    """Compile each file into out/<module>.olean, in order; with a store (cas.Store), an unchanged
    module is copied from it. Returns the number of modules served from the store."""
    search = SearchPath(lake_env('LEAN_PATH'), lake_env('LEAN_SYSROOT')) if store else None
    hits = 0
    for file in map(Path, files):
        relative = file.resolve().relative_to(Path(root).resolve()).with_suffix('')
        module, target = '.'.join(relative.parts), Path(out) / relative.with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        key = hit = None
        if store:
            imports = source_imports(file)
            try:
                key = search.key('olean', imports, module=module, source=cas.sha256_file(file))
                hit = store.lookup(KIND, key)
            except Unsupported as error:
                print('lean_cache: %s compiled uncached: %s' % (module, error), file=sys.stderr)
        if search:
            search.forget(module)  # A later file's key must see this run's .olean.
        if hit:
            staged = target.with_name('.%s.%d' % (target.name, os.getpid()))
            shutil.copyfile(hit / 'module.olean', staged)
            os.replace(staged, target)
            hits += 1
            continue
        subprocess.run(['lake', 'env', 'lean', '-R', str(root), '-o', str(target), str(file)], cwd=ROOT, check=True)
        if key:
            try:
                built = olean_imports(target)
            except Unsupported as error:
                built = [str(error)]
            if not set(built) <= set(imports):
                print('lean_cache: %s not stored: it imports %s, its source header %s'
                      % (module, built, imports), file=sys.stderr)
                continue
            staged = store.stage(KIND, key)
            try:
                shutil.copyfile(target, staged / 'module.olean')
                store.publish(staged, KIND, key, {'kind': KIND, 'what': 'olean', 'module': module, 'key': key,
                                                  'created': time.time()})
            finally:
                shutil.rmtree(staged, ignore_errors=True)  # Gone after a publish.
    return hits


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('compile', help='compile standalone modules, in order')
    p.add_argument('--cache', type=Path, help='a scripts/cas.py store (normally $AIR2LEAN_CAS_DIR)')
    p.add_argument('--root', type=Path, required=True, help='`lean -R` root of the files')
    p.add_argument('--out', type=Path, required=True, help='library directory of the .olean files')
    p.add_argument('files', nargs='+', type=Path)
    a = parser.parse_args(argv)
    store = cas.Store(a.cache.expanduser().resolve()) if a.cache else None
    try:
        hits = compile_modules(a.files, a.root, a.out, store)
    except subprocess.CalledProcessError as error:
        print('lean_cache: %s exited %d' % (' '.join(map(str, error.cmd[:3])), error.returncode), file=sys.stderr)
        return 1
    print('lean_cache: %d modules, %d from the cache' % (len(a.files), hits), file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
