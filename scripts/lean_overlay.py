"""Lean files elaborated against an overlay of other sources for some of their modules.

A second translation of a program (another Zig version, permuted struct fields: P09's
retranslation acceptance, docs/invariant-synthesis.md) has the module names of the first, so that
the hand-written files that import it are checked against it unchanged. An `Overlay` is a layer
of source directories (`roots`, relative to the repository) over the layers `below` it and, last,
the repository's Lake package: a module's source is the first `<root>/<module path>.lean` found in
that order. A module is compiled into the layer's own olean directory (`out`) when its source is
in the layer's roots or when it imports such a module, transitively: so the hand-written modules
of the Lake package that import a replaced module are compiled again, against the replacement,
and everything else is used as the layers below (finally Lake) built it. Nothing is skipped by
name: what is compiled again follows from the imports.

Lean is run with the layers' olean directories in front of Lake's own (`lake env` alone puts the
package's library first, which would hide a replaced module of the package), and with the native
code a Lake build of the file would load (scripts/lean-deps.py `native_options`). Lean runs
unguarded here: callers run under scripts/build-guard.py.
"""
import functools
import os
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
import assumptions  # noqa: E402
from theorem_universe import SORRY_WARNING  # noqa: E402

# `lake env` with the directories of its first argument in front of Lake's LEAN_PATH.
IN_FRONT = ['lake', 'env', 'sh', '-c', 'LEAN_PATH="$1:$LEAN_PATH"; export LEAN_PATH; shift; exec "$@"', 'sh']
# The Lake modules already built for an overlay in this process, and the sources read for the
# native options (scripts/lean-deps.py `library_closure`).
_BUILT, _SOURCES, _LOCK = set(), {}, threading.Lock()


@functools.cache
def deps():
    """scripts/lean-deps.py, loaded once: its Lake queries are cached in the module."""
    return assumptions.lean_deps()


@functools.cache
def precompiled_modules():
    return deps().precompiled_modules()


class Failed(Exception):
    """A file of an overlay did not elaborate (`output`: Lean's)."""

    def __init__(self, file, output):
        super().__init__(f'{file}: Lean failed')
        self.file, self.output = file, output


def in_front(lean_path, command, **options):
    """Run `command` under `lake env` with `lean_path` in front of Lake's LEAN_PATH."""
    return subprocess.run([*IN_FRONT, os.pathsep.join(str(p) for p in lean_path), *command], cwd=ROOT,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, **options)


def accepted(result, file):
    """`result` of Lean on `file`, or `Failed` if Lean rejects it or warns of a `sorry`."""
    if result.returncode or SORRY_WARNING in result.stdout:
        raise Failed(file, result.stdout)
    return result


class Overlay:
    def __init__(self, roots, out, below=None):
        self.roots, self.out, self.below = [Path(r) for r in roots], Path(out), below
        self.layers = [self] + (below.layers if below else [])
        self.lib_roots = deps().lib_roots()
        self._dirty, self._done = {}, set()

    def lean_path(self):
        return [layer.out for layer in self.layers]

    def source(self, module):
        """(layer or None for the Lake package, root, path) of the source of `module`; None for a
        module with no source here (Lean's own)."""
        rel = module.replace('.', '/') + '.lean'
        for layer in self.layers:
            for root in layer.roots:
                if (ROOT / root / rel).is_file():
                    return layer, root, ROOT / root / rel
        if module.split('.')[0] in self.lib_roots and (ROOT / rel).is_file():
            return None, Path('.'), ROOT / rel
        return None

    def dirty(self, module):
        """Whether this layer compiles `module`: its source is in the layer's roots, or it imports
        a module that the layer compiles."""
        if module not in self._dirty:
            found = self.source(module)
            self._dirty[module] = False  # (an import cycle is Lean's to report)
            self._dirty[module] = found is not None and (
                found[0] is self or any(self.dirty(m) for m in deps().imports(found[2])))
        return self._dirty[module]

    def _imports(self, path):
        """Compile the imports of the file `path` that this layer compiles and build the Lake
        modules among the others."""
        imports = sorted(deps().imports(path))
        with _LOCK:
            lake = [m for m in imports if m not in _BUILT and not self.dirty(m)
                    and (found := self.source(m)) and found[0] is None]
            if lake:
                subprocess.run(['lake', 'build', '-q', *lake], cwd=ROOT, check=True)
                _BUILT.update(lake)
        for module in imports:
            self.compile(module)

    def link(self):
        """Lean takes every module of a top-level name from the first directory of its path that
        has that name. So for each top-level name this layer has compiled a module of, the
        modules of that name that the layer does not compile are linked into its directory from
        the layers below and from Lake's library (the first that has each). Called before each
        run of Lean in the layer; a program that imports through `lean_path` calls it first."""
        if not self.out.is_dir():
            return
        lower = [layer.out for layer in self.layers[1:]] + [ROOT / '.lake/build/lib/lean']
        for top in [p for p in self.out.iterdir() if p.is_dir() and p.name != 'files']:
            for directory in lower:
                for file in (directory / top.name).rglob('*.olean*'):
                    rel = file.relative_to(directory)
                    module = '.'.join(rel.with_name(rel.name.split('.')[0]).parts)
                    if not os.path.lexists(self.out / rel) and not self.dirty(module):
                        (self.out / rel).parent.mkdir(parents=True, exist_ok=True)
                        (self.out / rel).symlink_to(file.resolve())

    def _lean(self, path, root, olean):
        with _LOCK:
            native = deps().native_options(str(path), _SOURCES, precompiled_modules())
        olean.parent.mkdir(parents=True, exist_ok=True)
        if olean.is_symlink():  # (never write through a link into a lower layer)
            olean.unlink()
        self.link()
        return in_front(self.lean_path(), [os.environ.get('LEAN') or 'lean', *native, '-R', str(ROOT / root),
                                           '-o', str(olean), str(path)])

    def compile(self, module):
        """Compile `module` into this layer if the layer compiles it (once); `Failed` if Lean
        rejects it or warns of a `sorry`."""
        if module in self._done or not self.dirty(module):
            return
        self._done.add(module)
        _, root, path = self.source(module)
        self._imports(path)
        accepted(self._lean(path, root, self.out / (module.replace('.', '/') + '.olean')),
                 path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path))

    def elaborate(self, file, root='.'):
        """Elaborate `file` (a path relative to the repository, a file of the directory `root`)
        after compiling its imports; Lean's result (not checked: a negative control expects a
        failure)."""
        path = ROOT / file
        self._imports(path)
        return self._lean(path, root, self.out / 'files' / (Path(file).with_suffix('.olean')))

    def check(self, file, root='.'):
        """`elaborate`, and `Failed` if Lean rejects the file or warns of a `sorry`."""
        return accepted(self.elaborate(file, root), file)
