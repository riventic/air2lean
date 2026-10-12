#!/usr/bin/env python3
"""Shared content-addressed build cache for worktrees on one machine (opt-in).

The cache directory is set only by the environment variable AIR2LEAN_CAS_DIR. Unset or empty:
nothing is cached and nothing outside the worktree is read or written; every command below
then behaves as the plain tool would (`zig-air` builds into <worktree>/zig-air-<version>, `env`
prints nothing, `air` runs the compiler).

  cas.py zig-air VERSION [--key]   path of the patched compiler (bin/zig) for this checkout's
                                   zig-patch/ tree, built under scripts/build-guard.py on a miss
  cas.py env                       shell exports that make Lake use the shared artifact cache
  cas.py run -- CMD...             CMD with those exports (a plain exec when caching is off)
  cas.py src VERSION --scratch D   the pinned pristine compiler source tree of VERSION
  cas.py air -- ZIG ARGS...        an AIR export (ZIG_AIR_JSON_DIR) served from the cache
  cas.py native -- ZIG ARGS...     a stock-Zig build-exe/build-lib (-femit-bin) served from the cache
  cas.py host-zig VERSION          path of the stock Zig of VERSION (as for zig-air's bootstrap)
  cas.py gc [--max-gib N]          evict least recently used entries above the size cap
  cas.py stats                     entry counts and sizes

Entries are keyed by the content of everything that determines them, so a stale entry cannot be
hit: a changed input is a different key. (See docs/build-cache.md for the argument per kind.)
  zig/<version>-<key>   key: the inputs zig-patch/build.sh reads for VERSION (exporter sources,
                        hook patch, build/lock scripts, the version's versions.toml table), the
                        host Zig that bootstraps it (binary and lib/ digest), host OS/arch and
                        the build settings.
  air/<key>             key: the compiler entry key, the export arguments and filter, the host
                        identity (a native target depends on it) and every file under the root
                        source's module directory (Zig imports stay inside it).
  native/<key>          key: the compiler binary and its lib/ (path, size, mtime of each file), the
                        build arguments, the target (the host identity when there is no -target)
                        and, for each source root, every .zig/.zon file under its directory (a
                        module imports only those; a tree using @embedFile is not cached).
  lake/                 Lake's own artifact cache (LAKE_CACHE_DIR): outputs are stored by
                        content hash under Lake's input hash (module source, the traces of its
                        imports, toolchain and options).
Entries are built in tmp/ and published by one rename; a per-key lock makes concurrent misses
build once. `gc` evicts by last use (entry stamp, or for Lake files the inode change time that a
restoring hard link updates) and never removes an entry used within --min-age.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 1
ENV = 'AIR2LEAN_CAS_DIR'
MARKER = '.cas.json'          # written into every published entry; its presence = complete
USED = '.cas-used'            # touched on every hit (LRU)
KINDS = ('zig', 'air', 'src', 'native')  # directory entries; lake/ is Lake's own layout
STAMP = '.air2lean-inputs.json'  # uncached mode: the key a worktree-local compiler was built from
DEFAULT_MAX_GIB = 60
# On macOS the build of these versions must not find Apple's SDK through `xcrun` (the
# bootstrap's SDK detection fails on current macOS); a failing `xcrun` first on PATH makes the
# host Zig use its bundled macOS libc. Part of the key: it changes the build environment.
DARWIN_NO_XCRUN = {'0.14.1', '0.15.2'}


class CasError(Exception):
    pass


def cas_dir():
    """The cache root, or None when caching is off (AIR2LEAN_CAS_DIR unset or empty)."""
    value = os.environ.get(ENV, '')
    return Path(value).expanduser().resolve() if value else None


# ------------------------------------------------------------------ hashing (shared helpers)

def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def digest(value):
    """SHA-256 of a JSON-serialisable value in canonical form."""
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def tree_files(directory, exclude=()):
    """(relative POSIX path, symlink target or None) of every file and symlink under `directory`,
    skipping excluded subtrees. A symlink (also to a directory, which os.walk does not enter) is
    recorded by its target."""
    directory = Path(directory)
    excluded = {Path(e).resolve() for e in exclude}
    files = []
    for dirpath, dirnames, filenames in os.walk(directory):
        here = Path(dirpath)
        dirnames[:] = sorted(d for d in dirnames if (here / d).resolve() not in excluded)
        for name in sorted(filenames) + [d for d in dirnames if (here / d).is_symlink()]:
            path = here / name
            rel = path.relative_to(directory).as_posix()
            if path.is_symlink():
                files.append((rel, os.readlink(path)))
            elif path.is_file():
                files.append((rel, None))
    return sorted(files)


def tree_content(directory, exclude=()):
    """Content digest of a directory: every file's path, executable bit and SHA-256."""
    directory = Path(directory)
    return digest([[rel, '->', link] if link is not None else
                   [rel, os.access(directory / rel, os.X_OK), sha256_file(directory / rel)]
                   for rel, link in tree_files(directory, exclude)])


def tree_stat(directory):
    """Cheap digest of an installation directory: every file's path, size and mtime."""
    directory = Path(directory)
    rows = []
    for rel, link in tree_files(directory):
        if link is not None:
            rows.append([rel, '->', link])
            continue
        st = (directory / rel).stat()
        rows.append([rel, st.st_size, st.st_mtime_ns])
    return digest(rows)


def toml_table(text, header):
    """The non-comment lines of one `[header]` table of versions.toml (zig-patch/toml-get.sh)."""
    lines, inside = [], False
    for line in text.splitlines():
        if line == header:
            inside = True
            continue
        if inside and line.startswith('['):
            break
        if inside and line.strip() and not line.lstrip().startswith('#'):
            lines.append(line.strip())
    if not lines:
        raise CasError('zig-patch/versions.toml has no table %s' % header)
    return lines


def zig_patch_inputs(root, version):
    """Exactly what zig-patch/build.sh reads from the checkout for VERSION: the version's
    versions.toml table and the sha256 of each file it copies or runs."""
    root = Path(root)
    table = toml_table((root / 'zig-patch/versions.toml').read_text(encoding='utf-8'), '["%s"]' % version)
    hook = next(m.group(1) for line in table if (m := re.fullmatch(r'hook\s*=\s*"(.*)"', line)))
    files = sorted(p.relative_to(root).as_posix() for p in (root / 'zig-patch/air-json').glob('*.zig'))
    files += ['zig-patch/' + hook] + ['zig-patch/' + n for n in ('build.sh', 'lock.sh', 'toml-get.sh')]
    return {'version': version, 'table': table, 'files': {f: sha256_file(root / f) for f in files}}


# ------------------------------------------------------------------ store

class Store:
    def __init__(self, path):
        self.path = Path(path)
        for sub in ('tmp', 'locks', 'logs') + KINDS + ('lake',):
            (self.path / sub).mkdir(parents=True, exist_ok=True)

    def entry(self, kind, name):
        return self.path / kind / name

    def lookup(self, kind, name):
        """The published entry, touched for LRU, or None."""
        path = self.entry(kind, name)
        if not (path / MARKER).is_file():
            return None
        try:
            (path / USED).touch()
        except OSError:
            pass
        return path

    def lock(self, kind, name):
        """An exclusive lock (context manager) serialising builders of one key."""
        return FileLock(self.path / 'locks' / ('%s-%s.lock' % (kind, name)))

    def stage(self, kind, name):
        return Path(tempfile.mkdtemp(prefix='%s-%s.' % (kind, name), dir=self.path / 'tmp'))

    def publish(self, staged, kind, name, meta):
        """Write the marker last and rename the staged directory into place (atomic)."""
        (staged / MARKER).write_text(json.dumps(dict(meta, schema=SCHEMA), indent=2, sort_keys=True) + '\n')
        (staged / USED).touch()
        target = self.entry(kind, name)
        try:
            os.rename(staged, target)
        except OSError:
            if not (target / MARKER).is_file():
                raise
            shutil.rmtree(staged, ignore_errors=True)  # A concurrent builder published first.
        return target


class FileLock:
    def __init__(self, path):
        self.path = Path(path)
        self.handle = None

    def __enter__(self):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.handle = self.path.open('a')
        fcntl.flock(self.handle, fcntl.LOCK_EX)
        return self

    def __exit__(self, *exc):
        fcntl.flock(self.handle, fcntl.LOCK_UN)
        self.handle.close()


# ------------------------------------------------------------------ patched compilers

def host_zig(version):
    """The stock Zig of VERSION that bootstraps zig-patch/build.sh: AIR2LEAN_HOST_ZIG_<v> (dots as
    underscores), else $AIR2LEAN_CACHE/host-<version>/zig, else `zig` on PATH of that version."""
    candidates = [os.environ.get('AIR2LEAN_HOST_ZIG_' + version.replace('.', '_'), ''),
                  str(Path(os.environ.get('AIR2LEAN_CACHE', '') or Path.home() / '.cache/air2lean')
                      / ('host-' + version) / 'zig'),
                  shutil.which('zig') or '']
    for candidate in filter(None, candidates):
        path = Path(candidate)
        if path.is_file() and os.access(path, os.X_OK):
            found = subprocess.run([str(path), 'version'], capture_output=True, text=True).stdout.strip()
            if found == version:
                return path.resolve()
    raise CasError('no stock Zig %s to bootstrap the patched compiler: set AIR2LEAN_HOST_ZIG_%s to its '
                   'zig binary, or install it as $AIR2LEAN_CACHE/host-%s/zig'
                   % (version, version.replace('.', '_'), version))


def zig_air_key(root, version, host):
    """Key of the patched compiler that zig-patch/build.sh builds for VERSION with this host Zig."""
    if os.environ.get('AIR2LEAN_LLVM', '0') not in ('', '0'):
        raise CasError('AIR2LEAN_LLVM=1 builds depend on the local LLVM installation and are not cached; '
                       'run zig-patch/build.sh directly')
    no_xcrun = platform.system() == 'Darwin' and version in DARWIN_NO_XCRUN
    preimage = {'schema': SCHEMA, 'inputs': zig_patch_inputs(root, version),
                'host_zig': {'sha256': sha256_file(host), 'lib': tree_stat(host.parent / 'lib')},
                'host': [platform.system(), platform.machine()],
                'optimize': os.environ.get('AIR2LEAN_OPTIMIZE') or 'Debug', 'no_xcrun': no_xcrun}
    return digest(preimage), preimage


def build_compiler(root, version, host, prefix, no_xcrun, logs):
    """zig-patch/build.sh VERSION PREFIX under scripts/build-guard.py (heavy: ~10 min, ~8 GB)."""
    env = dict(os.environ)
    path = [str(host.parent)]
    shim = None
    if no_xcrun:
        shim = Path(tempfile.mkdtemp(prefix='air2lean-xcrun.'))
        (shim / 'xcrun').write_text('#!/bin/sh\nexit 1\n')
        (shim / 'xcrun').chmod(0o755)
        path.insert(0, str(shim))
    env['PATH'] = os.pathsep.join(path + [env.get('PATH', '')])
    logs.mkdir(parents=True, exist_ok=True)
    report, log = logs / ('zig-%s.guard.json' % version), logs / ('zig-%s.guard.log' % version)
    command = [sys.executable, str(root / 'scripts/build-guard.py'), '--cwd', str(root),
               '--lock-wait', os.environ.get('AIR2LEAN_LOCK_WAIT', '21600'), '--timeout', '10800',
               '--rss-mib', '16384', '--log-bytes', str(16 << 20), '--report', str(report), '--log', str(log),
               '--', str(root / 'zig-patch/build.sh'), version, str(prefix)]
    print('building patched Zig %s -> %s (log %s)' % (version, prefix, log), file=sys.stderr)
    try:
        code = subprocess.run(command, env=env).returncode
    finally:
        if shim:
            shutil.rmtree(shim, ignore_errors=True)
    if code != 0 or not (prefix / 'bin/zig').is_file():
        raise CasError('building patched Zig %s failed (exit %d); see %s' % (version, code, log), code)


def zig_air(root, version, key_only=False):
    """Path of bin/zig of the patched compiler for VERSION, building it on a miss."""
    root = Path(root)
    host = host_zig(version)
    key, preimage = zig_air_key(root, version, host)
    if key_only:
        return key
    store_root = cas_dir()
    if store_root is None:
        # Uncached: the worktree-local compiler, as zig-patch/build.sh installs it by default.
        prefix = root / ('zig-air-' + version)
        stamp = prefix / STAMP
        if (prefix / 'bin/zig').is_file() and stamp.is_file() and json.loads(stamp.read_text()).get('key') == key:
            return prefix / 'bin/zig'
        build_compiler(root, version, host, prefix, preimage['no_xcrun'], root / '.lake/zig-air-logs')
        stamp.write_text(json.dumps({'key': key, 'preimage': preimage}, indent=2, sort_keys=True) + '\n')
        return prefix / 'bin/zig'
    store = Store(store_root)
    name = '%s-%s' % (version, key[:32])
    hit = store.lookup('zig', name)
    if hit is None:
        with store.lock('zig', name):
            hit = store.lookup('zig', name)
            if hit is None:
                staged = store.stage('zig', name)
                try:
                    build_compiler(root, version, host, staged / 'prefix', preimage['no_xcrun'],
                                   store.path / 'logs' / name)
                    hit = store.publish(staged, 'zig', name, {'kind': 'zig', 'key': key, 'preimage': preimage,
                                                              'created': time.time()})
                finally:
                    shutil.rmtree(staged, ignore_errors=True)  # Gone after a publish; a failed stage.
    return hit / 'prefix/bin/zig'


# ------------------------------------------------------------------ pristine compiler sources

def pristine_source(root, version, scratch):
    """The pinned pristine compiler source tree of VERSION (the tarball zig-patch/build.sh fetches
    into $AIR2LEAN_CACHE, sha256-checked against versions.toml). Uncached it is extracted into
    SCRATCH (a new directory); cached, once into src/zig-<version>-<sha256>."""
    table = toml_table((Path(root) / 'zig-patch/versions.toml').read_text(encoding='utf-8'), '["%s"]' % version)
    pins = dict(re.fullmatch(r'(\w+)\s*=\s*"(.*)"', line).groups() for line in table if '=' in line)
    url, sha = pins['url'], pins['sha256']
    store_root = cas_dir()
    store = Store(store_root) if store_root else None
    name = 'zig-%s-%s' % (version, sha)
    if store and (hit := store.lookup('src', name)):
        return hit / 'source'
    downloads = Path(os.environ.get('AIR2LEAN_CACHE') or Path.home() / '.cache/air2lean')
    tarball = downloads / ('zig-%s.tar.xz' % version)
    if not tarball.is_file():
        downloads.mkdir(parents=True, exist_ok=True)
        fd, part = tempfile.mkstemp(dir=downloads, prefix='zig-%s.part.' % version)
        os.close(fd)
        if subprocess.run(['curl', '-fsSL', '--output', part, url]).returncode != 0:
            os.unlink(part)
            raise CasError('download failed: ' + url)
        if sha256_file(part) != sha:
            os.unlink(part)
            raise CasError('%s: sha256 differs from zig-patch/versions.toml' % url)
        os.replace(part, tarball)
    if sha256_file(tarball) != sha:
        raise CasError('%s: sha256 differs from zig-patch/versions.toml; remove it and retry' % tarball)
    staged = store.stage('src', name) if store else Path(scratch)
    staged.mkdir(parents=True, exist_ok=True)
    (staged / 'source').mkdir()
    if subprocess.run(['tar', '-xJf', str(tarball), '-C', str(staged / 'source'), '--strip-components=1']).returncode:
        raise CasError('could not extract ' + str(tarball))
    if not store:
        return staged / 'source'
    return store.publish(staged, 'src', name, {'kind': 'src', 'sha256': sha, 'created': time.time()}) / 'source'


# ------------------------------------------------------------------ Lake artifact cache

def lake_env():
    """Lake's own artifact cache in $AIR2LEAN_CAS_DIR/lake, restoring every artifact into
    .lake/build (hard links, read-only) so that tools reading .lake/build see a normal build."""
    store_root = cas_dir()
    if store_root is None:
        return {}
    Store(store_root)
    return {'LAKE_ARTIFACT_CACHE': 'true', 'LAKE_CACHE_DIR': str(store_root / 'lake'),
            'LAKE_RESTORE_ARTIFACTS': 'true'}


# ------------------------------------------------------------------ AIR exports

# Export arguments whose effect the key captures. Anything else (modules, C sources, libc,
# include paths, response files) is passed through uncached.
FLAGS = {'-fno-emit-bin', '-fno-error-tracing', '-ferror-tracing', '-fstrip', '-fno-strip',
         '-fsingle-threaded', '-fno-single-threaded'}
VALUE_FLAGS = {'-target', '-mcpu'}


def host_identity():
    """What a native target depends on: OS, its version, architecture and CPU model/features."""
    system = platform.system()
    cpu = ''
    if system == 'Darwin':
        cpu = subprocess.run(['sysctl', '-n', 'machdep.cpu.brand_string', 'hw.optional.arm64'],
                             capture_output=True, text=True).stdout
        release = platform.mac_ver()[0]
    else:
        try:
            cpu = '\n'.join(sorted({l for l in Path('/proc/cpuinfo').read_text().splitlines()
                                    if l.split(':')[0].strip() in ('model name', 'flags', 'Features', 'CPU part')}))
        except OSError:
            cpu = ''
        release = platform.release()
    return [system, release, platform.machine(), hashlib.sha256(cpu.encode()).hexdigest()]


def air_plan(zig, argv, out_dir):
    """(key, preimage) of a cacheable export, or None to run it uncached."""
    marker = Path(zig).resolve().parent.parent.parent / MARKER
    if not marker.is_file():
        return None
    try:
        (marker.parent / USED).touch()  # A compiler in use is recently used (gc).
    except OSError:
        pass
    if not argv or argv[0] not in ('build-obj', 'build-lib', 'build-exe'):
        return None
    if os.environ.get('ZIG_LIB_DIR') or not out_dir:
        return None
    if Path(out_dir).exists() and any(Path(out_dir).iterdir()):
        return None  # The exporter merges into existing files; only an empty directory is replayed.
    roots, args, i = [], argv[1:], 0
    while i < len(args):
        arg = args[i]
        if arg in VALUE_FLAGS and i + 1 < len(args):
            i += 2
            continue
        if arg in FLAGS or re.fullmatch(r'-O(Debug|ReleaseSafe|ReleaseFast|ReleaseSmall)', arg) or arg.startswith('-mcpu='):
            i += 1
            continue
        if arg.endswith('.zig') and not arg.startswith('-'):
            roots.append(arg)
            i += 1
            continue
        return None
    if len(roots) != 1 or not Path(roots[0]).is_file():
        return None
    module_dir = Path(roots[0]).resolve().parent
    if any(link is not None for _, link in tree_files(module_dir, exclude=[out_dir])):
        return None  # The compiler reads through a symlink content that the key would not cover.
    compiler = json.loads(marker.read_text())
    preimage = {'schema': SCHEMA, 'compiler': compiler['key'], 'argv': argv,
                'filter': os.environ.get('ZIG_AIR_JSON_FILTER'), 'host': host_identity(),
                'module': tree_content(module_dir, exclude=[out_dir])}
    return digest(preimage), preimage


def air_export(zig, argv):
    """Run `ZIG ARGV` with ZIG_AIR_JSON_DIR; serve or store the written AIR in the cache."""
    out_dir = os.environ.get('ZIG_AIR_JSON_DIR', '')
    store_root = cas_dir()
    plan = air_plan(zig, argv, out_dir) if store_root else None
    if plan is None:
        return subprocess.run([zig, *argv]).returncode
    key, preimage = plan
    store = Store(store_root)
    hit = store.lookup('air', key)
    if hit is None:
        staged = store.stage('air', key)
        (staged / 'files').mkdir()
        done = subprocess.run([zig, *argv], env=dict(os.environ, ZIG_AIR_JSON_DIR=str(staged / 'files')),
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        sys.stdout.buffer.write(done.stdout)
        sys.stderr.buffer.write(done.stderr)
        if done.returncode != 0:
            shutil.rmtree(staged, ignore_errors=True)
            return done.returncode
        (staged / 'stdout').write_bytes(done.stdout)
        (staged / 'stderr').write_bytes(done.stderr)
        hit = store.publish(staged, 'air', key, {'kind': 'air', 'key': key, 'preimage': preimage, 'created': time.time()})
    else:
        sys.stdout.buffer.write((hit / 'stdout').read_bytes())
        sys.stderr.buffer.write((hit / 'stderr').read_bytes())
    Path(out_dir).mkdir(parents=True, exist_ok=True)
    for source in sorted((hit / 'files').iterdir()):
        shutil.copyfile(source, Path(out_dir) / source.name)
    return 0


# ------------------------------------------------------------------ native builds

def zig_sources(path):
    """Digest of what a source root can bring into a build: a module imports only .zig/.zon files
    under its root's directory. None when the tree uses @embedFile (any file could be embedded)."""
    directory = Path(path).resolve().parent
    rows = []
    for dirpath, dirnames, filenames in os.walk(directory):
        dirnames[:] = sorted(d for d in dirnames if d not in ('.lake', '.zig-cache', 'zig-cache', '.git'))
        for name in sorted(filenames):
            if name.endswith(('.zig', '.zon')):
                file = Path(dirpath) / name
                data = file.read_bytes()
                if b'@embedFile' in data:
                    return None
                rows.append([file.relative_to(directory).as_posix(), hashlib.sha256(data).hexdigest()])
    return digest([Path(path).name, rows])


def native_plan(zig, argv):
    """(key, preimage, output) of a cacheable stock-Zig build, or None to run it uncached."""
    lib = Path(zig).resolve().parent / 'lib'
    if not argv or argv[0] not in ('build-exe', 'build-lib') or os.environ.get('ZIG_LIB_DIR') or not lib.is_dir():
        return None
    output, args = None, []
    for arg in argv[1:]:
        module = re.fullmatch(r'-M([A-Za-z0-9_]+)=(.+)', arg)
        source = module.group(2) if module else arg
        if arg.startswith('-femit-bin='):
            output = arg.split('=', 1)[1]
            args.append(['emit', Path(output).suffix])
        elif (module or not arg.startswith('-')) and Path(source).is_file():
            content = zig_sources(source) if source.endswith('.zig') else sha256_file(source)
            if content is None:
                return None
            args.append([module.group(1) if module else None, Path(source).name, content])
        else:
            args.append(arg)
    if not output:
        return None
    preimage = {'schema': SCHEMA, 'zig': {'sha256': sha256_file(zig), 'lib': tree_stat(lib)}, 'args': args,
                'host': None if '-target' in argv else host_identity()}
    return digest(preimage), preimage, Path(output)


def native_build(zig, argv):
    """Run `ZIG ARGV`, or copy its -femit-bin output from the cache."""
    store_root = cas_dir()
    plan = native_plan(zig, argv) if store_root else None
    if plan is None:
        return subprocess.run([zig, *argv]).returncode
    key, preimage, output = plan
    store = Store(store_root)
    with store.lock('native', key):
        hit = store.lookup('native', key)
        if hit is None:
            staged = store.stage('native', key)
            done = subprocess.run([zig, *argv], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            sys.stdout.buffer.write(done.stdout)
            sys.stderr.buffer.write(done.stderr)
            if done.returncode != 0:
                shutil.rmtree(staged, ignore_errors=True)
                return done.returncode
            shutil.copy2(output, staged / 'output')
            (staged / 'stdout').write_bytes(done.stdout)
            (staged / 'stderr').write_bytes(done.stderr)
            store.publish(staged, 'native', key, {'kind': 'native', 'key': key, 'preimage': preimage,
                                                  'created': time.time()})
            return 0
    sys.stdout.buffer.write((hit / 'stdout').read_bytes())
    sys.stderr.buffer.write((hit / 'stderr').read_bytes())
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name('.%s.cas-%d' % (output.name, os.getpid()))
    shutil.copy2(hit / 'output', temporary)
    os.replace(temporary, output)
    return 0


# ------------------------------------------------------------------ eviction

def size_of(path):
    total = 0
    for dirpath, _, filenames in os.walk(path):
        for name in filenames:
            try:
                st = os.lstat(os.path.join(dirpath, name))
            except OSError:
                continue
            total += st.st_size
    return total


def published(store, kind):
    """The complete (marker-bearing) entries of one kind."""
    return [e for e in (store.path / kind).iterdir() if (e / MARKER).is_file()]


def candidates(store):
    """(items, pinned): (last_use, bytes, path, kind) of every evictable item, and the bytes of Lake
    outputs still linked from a worktree (no candidates: evicting one frees nothing)."""
    items, pinned = [], 0
    for kind in KINDS:
        for entry in published(store, kind):
            used = max((entry / f).stat().st_mtime for f in (MARKER, USED) if (entry / f).exists())
            items.append((used, size_of(entry), entry, kind))
    lake = store.path / 'lake'
    for dirpath, _, filenames in os.walk(lake / 'artifacts'):
        for name in filenames:
            path = Path(dirpath) / name
            st = os.lstat(path)
            # A restoring hard link updates the inode change time; a worktree link keeps the
            # data alive, so evicting a file with other links frees nothing (it is still used).
            if st.st_nlink == 1:
                items.append((max(st.st_atime, st.st_ctime, st.st_mtime), st.st_size, path, 'lake'))
            else:
                pinned += st.st_size
    return items, pinned


def total_size(store):
    return sum(size_of(store.path / kind) for kind in KINDS + ('lake',))


def gc(max_bytes, min_age):
    store_root = cas_dir()
    if store_root is None:
        return 0, 0
    store = Store(store_root)
    with FileLock(store.path / 'locks' / 'gc.lock'):
        for stale in (store.path / 'tmp').iterdir():  # Abandoned stages (killed builders).
            if time.time() - stale.stat().st_mtime > 2 * 86400:
                shutil.rmtree(stale, ignore_errors=True)
        items, pinned = candidates(store)
        items.sort()
        total = total_size(store)
        # The cap applies to what eviction can free; else it could be unreachable and gc would
        # evict everything.
        freed = 0
        for used, size, path, kind in items:
            if total - pinned - freed <= max_bytes:
                break
            if time.time() - used < min_age:
                break  # Everything after this is newer.
            if kind == 'lake':
                path.unlink(missing_ok=True)  # Lake rebuilds when an output is missing.
            else:
                graveyard = store.stage('gc', path.name)
                os.rename(path, graveyard / 'entry')  # Unpublish atomically, then delete.
                shutil.rmtree(graveyard, ignore_errors=True)
            freed += size
        return total, freed


def gc_if_due(interval=3600):
    """`gc` with the default cap, at most once per interval (callers: scripts/regen.sh)."""
    store_root = cas_dir()
    if store_root is None:
        return
    stamp = Store(store_root).path / 'locks' / 'last-gc'
    if stamp.exists() and time.time() - stamp.stat().st_mtime < interval:
        return
    stamp.touch()
    gc(max_bytes_default(), interval)


def stats():
    store_root = cas_dir()
    if store_root is None:
        return {'enabled': False}
    store = Store(store_root)
    out = {'enabled': True, 'path': str(store.path)}
    for kind in KINDS:
        entries = published(store, kind)
        out[kind] = {'entries': len(entries), 'bytes': sum(size_of(e) for e in entries)}
    out['lake'] = {'bytes': size_of(store.path / 'lake')}
    return out


# ------------------------------------------------------------------ CLI

def max_bytes_default():
    return int(float(os.environ.get('AIR2LEAN_CAS_MAX_GIB', DEFAULT_MAX_GIB)) * (1 << 30))


def strip_dd(args):
    """argparse.REMAINDER keeps a leading `--`."""
    return args[1:] if args[:1] == ['--'] else args


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('zig-air')
    p.add_argument('version')
    p.add_argument('--key', action='store_true', help='print the cache key only (no build)')
    sub.add_parser('env')
    p = sub.add_parser('run')
    p.add_argument('argv', nargs=argparse.REMAINDER)
    p = sub.add_parser('src')
    p.add_argument('version')
    p.add_argument('--scratch', required=True, type=Path, help='new directory for an uncached extraction')
    p = sub.add_parser('air')
    p.add_argument('zig')
    p.add_argument('args', nargs=argparse.REMAINDER)
    p = sub.add_parser('native')
    p.add_argument('zig')
    p.add_argument('args', nargs=argparse.REMAINDER)
    p = sub.add_parser('host-zig')
    p.add_argument('version')
    p = sub.add_parser('gc')
    p.add_argument('--max-gib', type=float, help='size cap (default $AIR2LEAN_CAS_MAX_GIB or %d)' % DEFAULT_MAX_GIB)
    p.add_argument('--min-age', type=float, default=3600, help='never evict what was used this many seconds ago')
    sub.add_parser('stats')
    a = parser.parse_args(argv)
    try:
        if a.command == 'zig-air':
            print(zig_air(ROOT, a.version, a.key))
        elif a.command == 'env':
            for name, value in lake_env().items():
                print('export %s=%s' % (name, shlex.quote(value)))
        elif a.command == 'run':
            argv = strip_dd(a.argv)
            if not argv:
                parser.error('run needs a command')
            os.execvpe(argv[0], argv, dict(os.environ, **lake_env()))
        elif a.command == 'src':
            print(pristine_source(ROOT, a.version, a.scratch))
        elif a.command == 'air':
            return air_export(a.zig, strip_dd(a.args))
        elif a.command == 'native':
            return native_build(a.zig, strip_dd(a.args))
        elif a.command == 'host-zig':
            print(host_zig(a.version))
        elif a.command == 'gc':
            cap = int(a.max_gib * (1 << 30)) if a.max_gib is not None else max_bytes_default()
            total, freed = gc(cap, a.min_age)
            print('cache %.1f GiB, evicted %.1f GiB (cap %.1f GiB)' % (total / 2**30, freed / 2**30, cap / 2**30))
        elif a.command == 'stats':
            print(json.dumps(stats(), indent=2))
    except CasError as error:
        print('error: %s' % error.args[0], file=sys.stderr)
        return error.args[1] if len(error.args) > 1 else 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
