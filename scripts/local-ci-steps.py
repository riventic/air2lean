#!/usr/bin/env python3
"""Run the checkout's CI shell recipes locally; reject unsupported workflow syntax."""
import fnmatch
import hashlib
import importlib.util
import io
import os
import json
from pathlib import Path
import re
import signal
import shutil
import stat
import subprocess
import sys
import tarfile
import time


def open_dir(parent, parts):
    """Open a physical directory chain, anchored to an already-open directory."""
    fd = os.dup(parent)
    try:
        for part in parts:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
        return fd
    except BaseException:
        os.close(fd)
        raise


def prune_stale_modules(root, tracked, owners):
    """Remove only absent-source module facets from this package's physical build roots."""
    root = Path(root).absolute()
    if root.resolve(strict=True) != root:
        raise ValueError('cache pruning requires a physical checkout path')
    if any(not re.fullmatch(r'[A-Za-z_]\w*(?:/[A-Za-z_]\w*)*', owner, re.ASCII) for owner in owners):
        raise ValueError('invalid owned module root')
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW

    # Lake v4.34.0 Config/Module.lean output paths and Build/Common.lean sidecars.
    facets = {
        'lib/lean': ('olean', 'olean.server', 'olean.private', 'ilean', 'ir', 'ir.sig'),
        'ir': ('c', 'c.o.export', 'c.o.noexport', 'bc', 'bc.o', 'ltar', 'setup.json'),
    }
    removed = []
    anchor = os.open('/', flags)
    try:
        root_fd = open_dir(anchor, root.parts[1:])
    finally:
        os.close(anchor)
    try:
        for directory, outputs in facets.items():
            suffixes = sorted({'.' + ext + tail for ext in outputs for tail in ('', '.hash', '.trace')} |
                              ({'.trace'} if directory == 'lib/lean' else set()), key=len, reverse=True)
            try:
                cache_fd = open_dir(root_fd, ('.lake', 'build', *directory.split('/')))
            except FileNotFoundError:
                continue
            try:
                pending = []
                for parent, dirs, files, parent_fd in os.fwalk('.', dir_fd=cache_fd, follow_symlinks=False):
                    relative = Path(parent)
                    dirs[:] = [name for name in dirs if any(
                        str(relative / name) == owner or str(relative / name).startswith(owner + '/') or
                        owner.startswith(str(relative / name) + '/') for owner in owners)]
                    for name in dirs:
                        if not stat.S_ISDIR(os.stat(name, dir_fd=parent_fd, follow_symlinks=False).st_mode):
                            raise ValueError('unsafe module cache directory')
                    for name in files:
                        suffix = next((ext for ext in suffixes if name.endswith(ext)), None)
                        if suffix is None:
                            continue
                        module = str(relative / name[:-len(suffix)])
                        if not any(module == owner or module.startswith(owner + '/') for owner in owners):
                            continue
                        if module + '.lean' in tracked:
                            continue
                        info = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
                        if not stat.S_ISREG(info.st_mode):
                            raise ValueError('unsafe module cache artifact')
                        pending.append((relative / name, info))
                # Validate the whole tree before changing it; reopen parents without following links.
                for relative, expected in pending:
                    parent_fd = open_dir(cache_fd, relative.parts[:-1])
                    try:
                        current = os.stat(relative.name, dir_fd=parent_fd, follow_symlinks=False)
                        if (current.st_dev, current.st_ino, current.st_mode, current.st_size, current.st_mtime_ns) != \
                                (expected.st_dev, expected.st_ino, expected.st_mode, expected.st_size, expected.st_mtime_ns):
                            raise ValueError('module cache artifact changed during pruning')
                        os.unlink(relative.name, dir_fd=parent_fd)
                        removed.append(str(Path('.lake/build') / directory / relative))
                    finally:
                        os.close(parent_fd)
            finally:
                os.close(cache_fd)
    finally:
        os.close(root_fd)
    return removed


def prune_current_cache(root):
    import tomllib

    root = Path(root)
    if (root / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.0':
        raise ValueError('review Lake cache suffixes before changing the pinned toolchain')
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    if any(key in config for key in ('buildDir', 'leanLibDir', 'irDir', 'srcDir')) or (root / 'lakefile.lean').exists():
        raise ValueError('unsupported custom Lake cache/source layout')
    owners = set()
    for item in config.get('lean_lib', []) + config.get('lean_exe', []):
        if 'srcDir' in item:
            raise ValueError('unsupported custom Lean source directory')
        names = item.get('roots', [item.get('root', item['name'])])
        owners.update(name.replace('.', '/') for name in names)
    tracked = subprocess.run(['git', '-C', str(root), 'ls-files', '-z'], check=True,
                             stdout=subprocess.PIPE, timeout=5).stdout
    removed = prune_stale_modules(root, set(os.fsdecode(tracked).split('\0')[:-1]), owners)
    print(f'Pruned {len(removed)} absent-source module artifacts from the local Lake cache', flush=True)
    return removed


CR = None


def load_script(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), Path(__file__).with_name(name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def reuse_helpers():
    global CR
    if CR is None:
        CR = load_script('ci-reuse')
    return CR


def remove_check_trees(root):
    """CI's Lake cache excludes source copies; never retain one across restricted rows."""
    if not shutil.rmtree.avoids_symlink_attacks:
        raise ValueError('check-tree cleanup needs directory-anchored removal')
    def unreadable(error):
        raise error

    anchor = os.open('/', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for package in (Path(root), Path(root) / 'tests/diff'):
            try:
                parent = open_dir(anchor, (package.absolute() / '.lake').parts[1:])
            except FileNotFoundError:
                continue
            try:
                try:
                    info = os.stat('check-tree', dir_fd=parent, follow_symlinks=False)
                except FileNotFoundError:
                    pass
                else:
                    if stat.S_ISLNK(info.st_mode):
                        os.unlink('check-tree', dir_fd=parent)
                    elif stat.S_ISDIR(info.st_mode):
                        shutil.rmtree('check-tree', dir_fd=parent)
                    else:
                        raise ValueError('unsupported check-tree cache entry')
                # A prior unrestricted run may have used any check-tree name. Its marker
                # is the existing family identity; cache reuse must not preserve its sources.
                marker = '.air2lean-check-tree.json'
                try:
                    os.stat(marker, dir_fd=parent, follow_symlinks=False)
                except FileNotFoundError:
                    pass
                else:
                    raise ValueError('Lake cache root is a marked source tree')
                for _path, directories, _files, directory in os.fwalk(
                        '.', dir_fd=parent, follow_symlinks=False, onerror=unreadable):
                    for name in list(directories):
                        info = os.stat(name, dir_fd=directory, follow_symlinks=False)
                        if not stat.S_ISDIR(info.st_mode):
                            continue  # Never follow a cache symlink outside its owned root.
                        child = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                                        dir_fd=directory)
                        try:
                            try:
                                marked = os.stat(marker, dir_fd=child, follow_symlinks=False)
                            except FileNotFoundError:
                                continue
                            if not stat.S_ISREG(marked.st_mode):
                                raise ValueError('unsupported source-tree marker type')
                            current = os.stat(name, dir_fd=directory, follow_symlinks=False)
                            opened = os.fstat(child)
                            if (opened.st_dev, opened.st_ino) != (current.st_dev, current.st_ino):
                                raise ValueError('marked source tree changed during cleanup')
                            shutil.rmtree(name, dir_fd=directory)
                            directories.remove(name)
                        finally:
                            os.close(child)
            finally:
                os.close(parent)
    finally:
        os.close(anchor)


def seal_snapshot(snapshot, bootstrap):
    """Remove the extracted source's alternate plaintext paths before workflow execution."""
    for name in ('source.tar', 'Dockerfile', 'files', 'bootstrap.sh'):
        (snapshot / name).unlink(missing_ok=True)
    bootstrap.unlink(missing_ok=True)
    remove_check_trees(Path.cwd())


def snapshot_path(path):
    """The existing tracked-source policy, shared by capture and immutable-tree comparison."""
    return not any(fnmatch.fnmatchcase(path, pattern) for pattern in (
        '.git', '.git/*', '.lake', '.lake/*', '*/.lake', '*/.lake/*',
        '.aws/*', '.codex/*', '.agents/*', 'zig-air-*/*', 'host-zig/*'))


def archive_regular(archive, members, member):
    """Resolve the regular data of a validated member, including direct hard links."""
    target = members.get(member.linkname) if member.islnk() else member
    if (not (member.isfile() or member.islnk()) or target is None or not target.isfile()
            or (target.mode ^ member.mode) & stat.S_IXUSR):
        raise ValueError(f'unsupported snapshot regular member: {member.name!r}')
    return archive.extractfile(target), target.size, '100755' if member.mode & stat.S_IXUSR else '100644'


def archive_tree(source, inventory, algorithm):
    """Git identities of the actual archived bytes, without consulting live file contents."""
    with tarfile.open(fileobj=io.BytesIO(source)) as archive:
        members = {}
        for member in archive.getmembers():
            name = member.name
            if name.startswith('/') or any(part in ('', '.', '..') for part in name.split('/')):
                raise ValueError(f'unsafe snapshot member: {name!r}')
            if name in members:
                raise ValueError(f'duplicate snapshot member: {name!r}')
            if name not in inventory:
                raise ValueError(f'unexpected snapshot member: {name!r}')
            members[name] = member
        if set(members) != set(inventory):
            raise ValueError(f'missing snapshot members: {sorted(set(inventory) - set(members))!r}')
        tree = {}
        for name, member in members.items():
            if member.issym():
                target = os.fsencode(member.linkname)
                stream, size, mode = io.BytesIO(target), len(target), '120000'
            elif member.isfile() or member.islnk():
                stream, size, mode = archive_regular(archive, members, member)
            else:
                raise ValueError(f'unsupported snapshot member type: {name!r}')
            digest = hashlib.new(algorithm)
            digest.update(f'blob {size}\0'.encode('ascii'))
            with stream:
                for block in iter(lambda: stream.read(1024 * 1024), b''):
                    digest.update(block)
            tree[name] = (mode, digest.hexdigest())
        return tree


def snapshot_config(snapshot):
    """Image recipe and cache keys from the same validated archive, never live files."""
    source = (snapshot / 'source.tar').read_bytes()
    stamp = dict(line.split('=', 1) for line in (snapshot / 'source-revision').read_text().splitlines())
    if hashlib.sha256(source).hexdigest() != stamp.get('snapshot_sha256'):
        raise ValueError('snapshot archive changed after capture')
    with tarfile.open(fileobj=io.BytesIO(source)) as archive:
        members = {member.name: member for member in archive.getmembers()}

        def read(name):
            if name not in members:
                raise ValueError(f'missing snapshot configuration: {name!r}')
            stream, _size, _mode = archive_regular(archive, members, members[name])
            with stream:
                return stream.read()

        recipe = read('Dockerfile.local-ci')
        bootstrap = read('scripts/local-ci.sh')
        # Preserve the original cat ordering, even when tar stored an input as a hard link.
        root_key = hashlib.sha256(read('lean-toolchain') + read('lake-manifest.json')).hexdigest()[:16]
        diff_key = hashlib.sha256(read('tests/diff/lean-toolchain') + read('tests/diff/lake-manifest.json')).hexdigest()[:16]
    (snapshot / 'Dockerfile').write_bytes(recipe)
    (snapshot / 'bootstrap.sh').write_bytes(bootstrap)
    (snapshot / 'lake-key').write_text(root_key + '\n')
    (snapshot / 'diff-key').write_text(diff_key + '\n')


def capture_snapshot(snapshot, artifacts, mode, version):
    """Capture indexed working-tree content; only the captured archive may qualify as HEAD."""
    for directory in (snapshot, artifacts):
        (directory / 'source-revision').unlink(missing_ok=True)
    if any(label.splitlines() != [label] for label in (mode, version)):
        raise ValueError('source stamp labels must be single lines')
    root, reuse = Path.cwd(), reuse_helpers()
    try:
        revision = reuse.git(root, 'rev-parse', '--verify', 'HEAD^{commit}').decode().strip()
        algorithm = reuse.git(root, 'rev-parse', '--show-object-format').decode().strip()
        expected = {path: entry for path, entry in reuse.tracked_tree(root, revision).items()
                    if snapshot_path(path)}
        if any(mode not in ('100644', '100755', '120000') for mode, _ in expected.values()):
            raise ValueError('unsupported tracked snapshot type (directory/submodule)')
        files = []
        for name in os.fsdecode(reuse.git(root, 'ls-files', '-z')).split('\0'):
            if not name or not snapshot_path(name) or not os.path.lexists(name):
                continue
            if not Path(name).is_symlink() and not Path(name).is_file():
                raise ValueError(f'unsupported tracked snapshot type: {name!r}')
            files.append(name)
        if len(set(files)) != len(files):
            raise ValueError('duplicate tracked snapshot paths (unmerged index)')
        with tarfile.open(snapshot / 'source.tar', 'w') as archive:
            for name in files:
                archive.add(name, arcname=name, recursive=False)
        source = (snapshot / 'source.tar').read_bytes()
        actual = archive_tree(source, set(files), algorithm)
        clean = (actual == expected and not reuse.git(root, 'status', '--porcelain', '--untracked-files=no')
                 and reuse.git(root, 'rev-parse', '--verify', 'HEAD^{commit}').decode().strip() == revision)
    except reuse.ReuseError as error:
        raise ValueError(f'cannot establish snapshot identity: {error}') from error
    (snapshot / 'files').write_bytes(b''.join(os.fsencode(name) + b'\0' for name in actual))
    stamp = (f'revision={revision}\ntracked_clean={"yes" if clean else "no"}\n'
             f'mode={mode}\nversion={version}\nsnapshot_sha256={hashlib.sha256(source).hexdigest()}\n')
    for directory in (artifacts, snapshot):
        (directory / 'source-revision').write_text(stamp)


if sys.argv[1:2] in (['--snapshot'], ['--snapshot-runner']):
    if len(sys.argv) != 6:
        raise SystemExit('usage: local-ci-steps.py --snapshot SNAPSHOT ARTIFACTS MODE VERSION')
    try:
        capture_snapshot(Path(sys.argv[2]), Path(sys.argv[3]), *sys.argv[4:])
        if sys.argv[1] == '--snapshot-runner':
            snapshot_config(Path(sys.argv[2]))
    except (OSError, ValueError, tarfile.TarError) as error:
        raise SystemExit(f'local-ci snapshot: {error}') from error
    raise SystemExit(0)


if sys.argv[1:2] == ['--seal-snapshot']:
    if len(sys.argv) != 4:
        raise SystemExit('usage: local-ci-steps.py --seal-snapshot SNAPSHOT BOOTSTRAP')
    try:
        seal_snapshot(Path(sys.argv[2]), Path(sys.argv[3]))
    except (OSError, ValueError) as error:
        raise SystemExit(f'local-ci isolation: {error}') from error
    raise SystemExit(0)


if sys.argv[1:2] == ['--snapshot-config']:
    if len(sys.argv) != 3:
        raise SystemExit('usage: local-ci-steps.py --snapshot-config SNAPSHOT')
    try:
        snapshot_config(Path(sys.argv[2]))
    except (OSError, ValueError, tarfile.TarError) as error:
        raise SystemExit(f'local-ci snapshot configuration: {error}') from error
    raise SystemExit(0)


if sys.argv[1:] == ['--prune-cache']:
    prune_current_cache(Path.cwd())
    raise SystemExit(0)


CR = reuse_helpers()
TM = CR.TM
GUARD = load_script('build-guard')


def render(value, context):
    return TM.interpolate(TM.expression_string(value), context)


CACHE_LOCK_FD = None
CANCELLING = False
LAUNCHING = False
PENDING_SIGNAL = None


class Cancelled(BaseException):
    def __init__(self, signum):
        self.signum = signum
        super().__init__(f'cancelled by signal {signum}')


def stop(signum, _frame):
    global PENDING_SIGNAL
    # Waiting here re-enters Popen.wait's non-reentrant lock. Unwind it first.
    if not CANCELLING:
        if LAUNCHING:
            PENDING_SIGNAL = signum
            return
        raise Cancelled(signum)


def stop_group(child, signum):
    # The child starts its own session; this exact group belongs to this invocation.
    # Reuse the guard's owned-tree/zombie handling rather than signal a zombie-only
    # group (which macOS refuses) or reap its leader before surviving descendants.
    tree = GUARD.Tree(child.pid)
    for forwarded in (signum, signal.SIGKILL):
        GUARD.signal_workload(child, tree, forwarded)
        if forwarded != signal.SIGKILL:
            time.sleep(2)
    child.wait()


def call(command, **kwargs):
    global CANCELLING, LAUNCHING, PENDING_SIGNAL
    inherited = []
    for descriptor in {9, CACHE_LOCK_FD} - {None}:
        try:
            os.fstat(descriptor)
            inherited.append(descriptor)
        except OSError:
            pass
    child = None
    LAUNCHING = True
    try:
        child = subprocess.Popen(command, start_new_session=True, pass_fds=inherited, **kwargs)
        LAUNCHING = False
        if PENDING_SIGNAL is not None:
            signum, PENDING_SIGNAL = PENDING_SIGNAL, None
            raise Cancelled(signum)
        # Keep the guard's PID anchor until cancellation can no longer enter
        # group cleanup. The final reap is short and defers signals just like
        # launch; a deferred cancellation is delivered outside the cleanup try.
        while GUARD.peek_status(child) is None:
            time.sleep(0.05)
        LAUNCHING = True
        status = child.wait()
    except Cancelled as error:
        CANCELLING = True
        PENDING_SIGNAL = None
        if child is not None:
            stop_group(child, error.signum)
        raise
    finally:
        LAUNCHING = False
        CANCELLING = False
    if PENDING_SIGNAL is not None:
        signum, PENDING_SIGNAL = PENDING_SIGNAL, None
        raise Cancelled(signum)
    if status:
        raise subprocess.CalledProcessError(status, command)


# CI-only reuse machinery (docs/ci.md): the reuse decision, the in-run artifact unpacking that
# local-ci.sh --prepare replaces (and `scripts/generated.py materialize` for the generated files), and the record
# step. Local CI never reuses or records (`part` mode restricts the checkout like CI's decision);
# scripts/release-record.py does not count these steps as gates.
# The image (Dockerfile.local-ci) provides the system packages CI installs.
# This literal set is also consumed by release-record.py's existing test-row gate planner.
ci_only = {'Reuse a recorded result', 'Unpack the patched zig', 'Unpack the Lake build', 'Install the generated files',
           'Install system packages', 'Record the result for reuse'}
REUSE_STEPS = {'Reuse a recorded result', 'Record the result for reuse'}
# Qualification of the existing Linux substitutions, not another recipe source. A changed
# body, guard or action option must be reviewed before a cached setup may supply its effects.
QUALIFIED_TEST_SUBSTITUTIONS = {
    'Install host zig': '0fdb27ffd883f4eaf6eeca83258b8582f5a2c91b7065b2f3e85a22d2eb47f4d0',
    'Install elan': '111e31954544c1b3aea1847d515663a95c6b41c4de6a85d8724b93dd77b4bde9',
    'Download the generated files': '7943ff7c8c75d5a611d0f4583e972043d60aff3036de2f521f1e09b60f8effb0',
    'Install the generated files': '81da2ec3d6d6ea00b4f047363ac485e948138387d4c0db91fce322f85002db07',
    'Install system packages': 'ac37875d21bfe8a17a2ae0aea1ef78708ff3a52f2f42deff26c2ec758271b714',
    'Download the patched zig': '4957b671e28590f152168aa8301e609d273cdff1d054d9e0ca54e1fe4b74703b',
    'Unpack the patched zig': '68561281656560f917ca291aa71243cc2fb4b713302158c00e4af6e3d6efa756',
    'Download the Lake build': '141bbcf2d0c708db55fe20bfbc9158505439303bac5d18f08d08e4abeaaddf65',
    'Unpack the Lake build': 'e0b4f2cb16708c27660c2df18394bde17040d330b9be9ecebcac6603ba6285d6',
}


def step_digest(step):
    return hashlib.sha256(json.dumps(step, sort_keys=True).encode()).hexdigest()

# Literal keys retain release-record.py's existing gate-planner interface. The commands
# have one source, ci.yml; full step dictionaries are qualified by digest above.
setup = {
    'Install host zig': None,
    'Install elan': None,
    'Build patched zig': None,
}
RUNNERS = {'ubuntu-24.04': 'linux/amd64', 'ubuntu-24.04-arm': 'linux/arm64', 'macos-14': 'host'}
HOST_SOURCE_GAP = ('macOS host checks are unrestricted: descendants can read the caller\'s Git objects, '
                   'for example git -C ../../../.. show HEAD:README.md; no files are withheld')
ALLOWED_ACTIONS = {'actions/checkout', 'actions/cache', 'actions/cache/restore',
                   'actions/upload-artifact', 'actions/download-artifact'}


def workflow_rows(workflow):
    if 'defaults' in workflow or 'env' in workflow:
        raise ValueError('unsupported workflow defaults/environment')
    rows = {}
    for name, job in workflow['jobs'].items():
        if set(job) - {'needs', 'runs-on', 'timeout-minutes', 'env', 'strategy', 'steps', 'if'}:
            raise ValueError(f'{name}: unsupported job fields')
        if job.get('runs-on') not in RUNNERS:
            raise ValueError(f'{name}: unsupported CI runner {job.get("runs-on")!r}')
        needs = reuse_helpers().needs_of(job)
        if any(dependency not in workflow['jobs'] for dependency in needs):
            raise ValueError(f'{name}: unknown job dependency')
        strategy = job.get('strategy', {})
        if set(strategy) - {'fail-fast', 'matrix'}:
            raise ValueError(f'{name}: unsupported CI matrix')
        for row in TM.matrix_include(job, f'.github/workflows/ci.yml: job {name}') or [{}]:
            if not isinstance(row, dict) or set(row) - {'zig', 'part', 'examples', 'full', 'mutate', 'shard'}:
                raise ValueError(f'{name}: unsupported matrix row fields')
            part = reuse_helpers().part_id(name, row)
            if part in rows:
                raise ValueError(f'duplicate CI part {part}')
            rows[part] = (name, row)
    return rows


def validate_step(step):
    name = step.get('name', '<unnamed>')
    if set(step) - {'name', 'id', 'if', 'env', 'run', 'uses', 'with', 'continue-on-error'}:
        raise ValueError(f'unsupported CI step fields: {name}')
    if ('run' in step) == ('uses' in step):
        raise ValueError(f'CI step needs exactly one of run/uses: {name}')
    if 'uses' in step and step['uses'].split('@')[0] not in ALLOWED_ACTIONS:
        raise ValueError(f'unsupported CI action: {name}: {step["uses"]}')
    if 'uses' in step:
        action = step['uses'].split('@')[0]
        allowed = {'actions/checkout': set(),
                   'actions/cache': {'path', 'key', 'restore-keys'},
                   'actions/cache/restore': {'path', 'key', 'restore-keys'},
                   'actions/download-artifact': {'name', 'path'},
                   'actions/upload-artifact': {'name', 'path', 'if-no-files-found', 'retention-days', 'compression-level'}}
        if set(step.get('with', {})) - allowed[action]:
            raise ValueError(f'{name}: unsupported {action} options')


def validate_job(job, optimized):
    if 'if' in job:
        raise ValueError('unsupported job-level CI condition')
    for step in job['steps']:
        validate_step(step)
        if optimized and step['name'] in setup:
            if step['name'] not in QUALIFIED_TEST_SUBSTITUTIONS:
                raise ValueError(f'unsupported optimized setup: {step["name"]}')
        if optimized and step['name'] in QUALIFIED_TEST_SUBSTITUTIONS:
            if step_digest(step) != QUALIFIED_TEST_SUBSTITUTIONS[step['name']]:
                raise ValueError(f'changed optimized CI substitution needs qualification: {step["name"]}')
        if optimized and step.get('uses', '').split('@')[0] == 'actions/download-artifact':
            if step['name'] not in QUALIFIED_TEST_SUBSTITUTIONS:
                raise ValueError(f'unsupported optimized artifact download: {step["name"]}')


def read_updates(path):
    """GitHub command files are single-line KEY=value here; reject unsupported multiline syntax."""
    result = {}
    for line in path.read_text().splitlines():
        key, sep, value = line.partition('=')
        if not sep or not re.fullmatch(r'[A-Za-z_][\w-]*', key, re.ASCII):
            raise ValueError(f'unsupported GitHub command file syntax: {path.name}: {line!r}')
        result[key] = value
    path.write_text('')
    return result


def restrict_part(part, discover=False):
    reuse = reuse_helpers()
    try:
        revision = None if discover else reuse.commit_revision(Path.cwd())
        entry = reuse.declaration(reuse.load_declarations(Path.cwd(), revision), part)
    except reuse.ReuseError as error:
        raise ValueError(str(error)) from error
    if entry.get('reuse') is not False:
        call(['python3', 'scripts/ci-reuse.py', 'restrict', '--part', part] +
             (['--discover'] if discover else ['--seal']))


def remove_entry(path):
    shutil.rmtree(path) if path.is_dir() and not path.is_symlink() else path.unlink()


def reset_checkout(snapshot, source, inventory=None):
    """Each job gets a fresh parentless snapshot, including after a producer sealed its history."""
    # CI's root Lake cache and packed artifact explicitly exclude this source checkout.
    # Keeping an earlier whole-tree copy would bypass the next row's withheld placeholders.
    remove_check_trees(Path.cwd())
    for entry in Path.cwd().iterdir():
        if entry.name == '.lake':
            continue
        if entry.name == 'tests':
            for child in entry.iterdir():
                if child.name == 'diff':
                    for item in child.iterdir():
                        if item.name != '.lake':
                            remove_entry(item)
                else:
                    remove_entry(child)
            continue
        remove_entry(entry)
    with tarfile.open(fileobj=io.BytesIO(source)) as archive:
        archive.extractall(Path.cwd(), filter='data')
    call(['git', 'init', '-q'])
    call(['git', 'config', 'user.email', 'local-ci@example.invalid'])
    call(['git', 'config', 'user.name', 'local-ci'])
    pathspec = snapshot / 'files'
    if inventory is not None:
        pathspec.write_bytes(inventory)
    try:
        call(['git', '--literal-pathspecs', 'add', '-f', '--pathspec-from-file=' + str(pathspec), '--pathspec-file-nul'])
    finally:
        if inventory is not None:
            pathspec.unlink()
    call(['git', 'commit', '-qm', 'Local tracked-source snapshot'], env=dict(os.environ, **reuse_helpers().IDENTITY))


class WorkflowRun:
    def __init__(self, workflow, artifacts, snapshot, discover=False, restricted=False):
        self.workflow = workflow
        self.rows = workflow_rows(workflow)
        self.artifacts, self.snapshot, self.discover = Path(artifacts), Path(snapshot), discover
        self.restricted = restricted
        self.source = (self.snapshot / 'source.tar').read_bytes()
        self.source_sha = hashlib.sha256(self.source).hexdigest()
        stamp = dict(line.split('=', 1) for line in (self.snapshot / 'source-revision').read_text().splitlines())
        if self.source_sha != stamp.get('snapshot_sha256'):
            raise ValueError('snapshot archive changed after capture')
        self.inventory = (self.snapshot / 'files').read_bytes()
        history = self.snapshot / 'main.bundle'
        self.history = history.read_bytes() if history.exists() else None
        if history.exists():
            history.unlink()
        # Preserve the captured bytes only in memory across producer/consumer resets.
        seal_snapshot(self.snapshot, Path(os.environ.get('AIR2LEAN_LOCAL_BOOTSTRAP', self.snapshot / 'bootstrap.sh')))
        self.completed, self.visiting, self.uploads = set(), set(), {}

    def run(self, part):
        if part in self.completed:
            return
        if part in self.visiting:
            raise ValueError(f'cyclic local CI artifact dependency: {part}')
        name, row = self.rows[part]
        if name == 'all-checks':
            raise ValueError('all-checks needs GitHub needs.*.result evidence; local receipts cannot replace it')
        self.visiting.add(part)
        # The optimized test path already supplies verified support artifacts. Other consumers
        # execute their declared producer jobs and transport the actual upload-artifact outputs.
        if name != 'test':
            needs = reuse_helpers().needs_of(self.workflow['jobs'][name])
            for dependency in needs:
                for dependency_part, (producer, _) in self.rows.items():
                    if producer == dependency:
                        if RUNNERS[self.workflow['jobs'][producer]['runs-on']] != RUNNERS[self.workflow['jobs'][name]['runs-on']]:
                            raise ValueError(f'{part}: dependency {dependency_part} needs a different local runner')
                        self.run(dependency_part)
        reset_checkout(self.snapshot, self.source, self.inventory)
        self.run_row(part, name, row)
        self.completed.add(part)
        self.visiting.remove(part)

    def action(self, step, context):
        action = step['uses'].split('@')[0]
        options = step.get('with', {})
        if action == 'actions/checkout':
            return 'tracked snapshot already checked out'
        if action in ('actions/cache', 'actions/cache/restore'):
            # Persistent Lake facets are incremental inputs, never an exact cache-hit claim.
            if step.get('id'):
                context[f'steps.{step["id"]}.outputs.cache-hit'] = 'false'
            return 'local incremental cache; exact cache-hit=false'
        artifact = render(options['name'], context)
        if artifact in ('.', '..') or not re.fullmatch(r'[\w.-]+', artifact, re.ASCII):
            raise ValueError(f'unsafe CI artifact name: {artifact}')
        if action == 'actions/download-artifact':
            source = self.uploads.get(artifact)
            if source is None:
                raise ValueError(f'{step["name"]}: artifact {artifact!r} has no successful local producer')
            target = Path(render(options.get('path', '.'), context))
            target.mkdir(parents=True, exist_ok=True)
            shutil.copytree(source, target, dirs_exist_ok=True)
        else:
            patterns = render(options['path'], context).splitlines()
            if len(patterns) != 1 or any(c in patterns[0] for c in '*?!'):
                raise ValueError(f'{step["name"]}: unsupported artifact upload path pattern')
            source = Path(patterns[0])
            if not source.exists():
                policy = options.get('if-no-files-found', 'warn')
                if policy == 'error':
                    raise ValueError(f'{step["name"]}: missing required upload {source}')
                return f'no optional upload ({policy}): {source}'
            target = self.artifacts / 'uploads' / artifact
            target.mkdir(parents=True, exist_ok=True)
            if source.is_dir():
                shutil.copytree(source, target, dirs_exist_ok=True)
            else:
                shutil.copy2(source, target / source.name)
            self.uploads[artifact] = target
        return 'local artifact transport'

    def run_row(self, part, name, row):
        job = self.workflow['jobs'][name]
        temp = self.artifacts / part.replace('/', '-')
        temp.mkdir(parents=True)
        context = {'matrix': row}
        number = list(self.workflow['jobs'][name].get('strategy', {}).get('matrix', {}).get('include', [{}])).index(row)
        where = f'.github/workflows/ci.yml: {name} row {number}'
        runner = RUNNERS[job['runs-on']]
        actual = 'host' if sys.platform == 'darwin' else 'linux/' + {'x86_64': 'amd64', 'aarch64': 'arm64'}.get(os.uname().machine, 'unknown')
        if runner != actual or (runner == 'host' and os.uname().machine != 'arm64'):
            raise ValueError(f'{part}: requires {runner}, actual platform is {actual}/{os.uname().machine}')
        context.update({'github.workspace': str(Path.cwd()), 'runner.temp': str(temp),
                        'runner.os': 'macOS' if runner == 'host' else 'Linux',
                        'runner.arch': 'ARM64' if runner in ('host', 'linux/arm64') else 'X64',
                        'env.AIR2LEAN_REUSED': '', 'env.AIR2LEAN_RECORD': '',
                        'success': True, 'failure': False, 'cancelled': False, 'always': True})
        env = dict(os.environ, RUNNER_TEMP=str(temp), TMPDIR=str(temp),
                   GITHUB_WORKSPACE=str(Path.cwd()), RUNNER_OS=context['runner.os'],
                   RUNNER_ARCH=context['runner.arch'])
        for command_file in ('GITHUB_PATH', 'GITHUB_ENV', 'GITHUB_OUTPUT'):
            path = temp / command_file.lower()
            path.touch()
            env[command_file] = str(path)
        report = {'schema': 'air2lean-local-ci-row/1', 'part': part, 'runner': runner,
                  'source': (self.artifacts / 'source-revision').read_text(),
                  'snapshot_sha256': self.source_sha,
                  'workflow_sha256': hashlib.sha256(Path('.github/workflows/ci.yml').read_bytes()).hexdigest(),
                  'restriction': {'requested': self.restricted, 'qualified': False, 'files_withheld': False},
                  'steps': [], 'success': False}
        if runner == 'host':
            report['restriction']['gap'] = HOST_SOURCE_GAP
        # Test setup is the existing verified/persistent Linux optimization, qualified against
        # the exact recipe text below. Native and support jobs execute their installers verbatim.
        optimized = name == 'test' and runner == 'linux/amd64'
        qualification_failed = False
        try:
            if runner == 'host' and self.restricted:
                raise ValueError(f'{part}: restricted host qualification is unavailable; {HOST_SOURCE_GAP}; '
                                 'use discovery or direct native scripts for unrestricted checks')
            if runner == 'host':
                print(f'Local CI: {HOST_SOURCE_GAP}', flush=True)
            if self.discover and name in CR.RESTRICTED_SUPPORT:
                raise ValueError(f'{part}: discovery is unavailable because the support workflow '
                                 'enforces its own restricted checkout; use part for its restricted execution')
            validate_job(job, optimized)
            try:
                env.update({key: render(value, context) for key, value in job.get('env', {}).items()})
                context.update({'env.' + key: value for key, value in env.items()})
            except TM.Unknown as error:
                raise ValueError(f'{where}: job environment: unsupported expression: {error}') from error
            if name == 'preflight':
                if self.history is None:
                    raise ValueError('preflight needs origin/main history; source snapshot has no main.bundle')
                bundle = temp / 'main.bundle'
                bundle.write_bytes(self.history)
                call(['git', 'remote', 'add', 'origin', str(bundle)])
                report['history_sha256'] = hashlib.sha256(self.history).hexdigest()
            if optimized:
                prune_current_cache(Path.cwd())
                call(['bash', 'scripts/local-ci.sh', '--prepare', row['zig']])
                env['PATH'] = f"{Path.cwd()}/host-zig:{env['ELAN_HOME']}/bin:" + env['PATH']
                if self.discover or self.restricted:
                    restrict_part(part, self.discover)
            elif runner != 'host' and name not in ('lake', 'zig-air', 'preflight'):
                restrict_part(part, self.discover)
            for step in job['steps']:
                record = {'name': step['name'], 'recipe_sha256': step_digest(step)}
                report['steps'].append(record)
                condition = step.get('if', '')
                status_condition = re.search(r'\b(?:success|failure|cancelled|always)\(\)',
                                             re.sub(r"'[^']*'", '', str(condition)), re.IGNORECASE)
                if not self.discover and not context['success'] and not status_condition:
                    record['status'] = 'prior-step-failed'
                    continue
                try:
                    if not TM.condition(step.get('if'), context):
                        record['status'] = 'condition-false'
                        continue
                except TM.Unknown as error:
                    raise ValueError(f'{where}: step {step["name"]!r}: unsupported expression: {error}') from error
                if step['name'] in REUSE_STEPS:
                    expected = (f'python3 scripts/ci-reuse.py decide --job {name} --row "$AIR2LEAN_ROW"'
                                if step['name'].startswith('Reuse') else
                                'python3 scripts/ci-reuse.py record --out "$RUNNER_TEMP/ci-reuse/record.json"')
                    if step.get('run', '').strip() != expected:
                        raise ValueError(f'changed CI reuse recipe: {step["name"]}')
                    record.update(status='local-only', reason='no GitHub result reuse/record locally')
                    continue
                if optimized and step['name'] in setup:
                    record.update(status='supplied', reason='verified local-ci.sh --prepare')
                    continue
                if optimized and step['name'] in QUALIFIED_TEST_SUBSTITUTIONS and 'run' in step:
                    record.update(status='supplied', reason='existing Linux setup/cache optimization')
                    continue
                if optimized and step.get('uses', '').split('@')[0] in ('actions/download-artifact', 'actions/upload-artifact'):
                    record.update(status='local-only', reason='existing test setup/artifact optimization')
                    continue
                label = row if optimized and 'run' in step else f'action {part}' if 'uses' in step else part
                print(f'== CI {label}: {step["name"]} ==', flush=True)
                started = time.monotonic()
                try:
                    if 'uses' in step:
                        record['reason'] = self.action(step, context)
                    else:
                        code = render(step['run'], context)
                        step_env = env | {key: render(value, context) for key, value in step.get('env', {}).items()}
                        call(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code], env=step_env)
                        for key, value in read_updates(Path(env['GITHUB_ENV'])).items():
                            env[key] = value
                            context['env.' + key] = value
                        outputs = read_updates(Path(env['GITHUB_OUTPUT']))
                        if outputs and not step.get('id'):
                            raise ValueError(f'{step["name"]}: GITHUB_OUTPUT needs a step id')
                        context.update({f'steps.{step.get("id")}.outputs.{key}': value for key, value in outputs.items()})
                        paths = Path(env['GITHUB_PATH']).read_text().splitlines()
                        if paths:
                            env['PATH'] = ':'.join(reversed(paths)) + ':' + env['PATH']
                            Path(env['GITHUB_PATH']).write_text('')
                    record['status'] = 'passed'
                except (subprocess.CalledProcessError, OSError, ValueError, TM.Unknown) as error:
                    detail = (f'{where}: step {step["name"]!r}: unsupported expression: {error}'
                              if isinstance(error, TM.Unknown) else str(error))
                    record.update(status='failed', error=detail)
                    qualification_failed = True
                    if not step.get('continue-on-error'):
                        context.update(success=False, failure=True)
                finally:
                    record['seconds'] = round(time.monotonic() - started, 3)
                if self.discover and runner != 'host':
                    try:
                        call(['python3', 'scripts/ci-reuse.py', 'check-restricted', '--reset'])
                    except subprocess.CalledProcessError:
                        context.update(success=False, failure=True)
                        qualification_failed = True
                        record['undeclared_reads'] = True
            if runner != 'host':
                call(['python3', 'scripts/ci-reuse.py', 'check-restricted'])
            report['success'] = context['success'] and not qualification_failed
        except BaseException as error:
            report['error'] = str(error)
            raise
        finally:
            if runner != 'host':
                try:
                    state = CR.restricted_state(Path.cwd())
                    if state is not None and (not isinstance(state, dict)
                            or not isinstance(state.get('withheld'), list)
                            or not isinstance(state.get('discover', False), bool)):
                        raise ValueError('invalid restricted checkout state')
                    withheld = state is not None and not state.get('discover')
                    report['restriction'].update(files_withheld=bool(withheld and state['withheld']),
                                                 qualified=bool(report['success'] and withheld and not self.discover))
                except (OSError, ValueError, CR.ReuseError) as error:
                    report['restriction']['error'] = f'cannot read restriction state: {error}'
                    report['success'] = False
            (temp / 'row.json').write_text(json.dumps(report, indent=2) + '\n')
        if not report['success']:
            errors = [f'{step["name"]}: {step["error"]}' for step in report['steps'] if 'error' in step]
            if report['restriction'].get('error'):
                errors.append(report['restriction']['error'])
            raise ValueError(f'{part}: workflow steps failed' + (': ' + '; '.join(errors) if errors else ''))


def run_host(workflow, mode, selected):
    import fcntl
    global CACHE_LOCK_FD
    tools = Path(os.environ['AIR2LEAN_LOCAL_HOST_TOOLS'])
    with (tools / 'local-ci.lock').open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError('another local CI host run owns the caches')
        CACHE_LOCK_FD = lock.fileno()
        # Keep the pinned workflow-installed elan in the standard host cache. The user's own
        # Lean/Zig executables never enter PATH; keep other tools from those directories.
        artifacts = Path(os.environ['AIR2LEAN_LOCAL_ARTIFACTS'])
        filtered = artifacts / 'path'
        filtered.mkdir()
        banned = {'zig', 'lake', 'lean', 'leanc', 'elan', 'air2lean'}
        seen = set()
        for directory in os.environ['PATH'].split(':'):
            if not Path(directory).is_dir():
                continue
            for entry in Path(directory).iterdir():
                if entry.name not in banned and entry.name not in seen and os.access(entry, os.X_OK) and not entry.is_dir():
                    (filtered / entry.name).symlink_to(entry.absolute())
                    seen.add(entry.name)
        home = tools / 'home'
        home.mkdir(exist_ok=True)
        # Keep only machine/cache/admission settings. Caller corpus/compiler/verification
        # switches must not change a workflow recipe or silently reduce its coverage.
        permitted = {'AIR2LEAN_CAS_DIR', 'AIR2LEAN_BUILD_LOCK', 'AIR2LEAN_BUILD_MEM_MIB',
                     'AIR2LEAN_JOBS', 'AIR2LEAN_MEM_MIB',
                     'AIR2LEAN_GUARD_MODE', 'AIR2LEAN_GUARD_PRIORITY', 'AIR2LEAN_LOCAL_ARTIFACTS',
                      'AIR2LEAN_LOCAL_SNAPSHOT', 'AIR2LEAN_LOCAL_MODE', 'AIR2LEAN_LOCAL_BOOTSTRAP',
                      'LANG', 'LC_ALL', 'TZ'}
        kept = {key: value for key, value in os.environ.items() if key in permitted}
        os.environ.clear()
        os.environ.update(kept)
        os.environ.update(HOME=str(home), ELAN_HOME=str(home / '.elan'),
                          AIR2LEAN_CACHE=str(tools / 'downloads'), ZIG_GLOBAL_CACHE_DIR=str(tools / 'zig-global'),
                          LEAN_NUM_THREADS='1', PATH=str(filtered))
        os.chdir(artifacts / 'work')
        run = WorkflowRun(workflow, artifacts, os.environ['AIR2LEAN_LOCAL_SNAPSHOT'], mode == 'discover',
                          restricted=mode == 'part')
        try:
            run.run(selected)
        finally:
            CACHE_LOCK_FD = None


def main(argv):
    try:
        workflow = TM.parse_workflow_yaml(Path('.github/workflows/ci.yml').read_text())
    except TM.Unreadable as error:
        raise ValueError(str(error)) from error
    rows = workflow_rows(workflow)
    if len(argv) == 3 and argv[0] == '--host':
        run_host(workflow, *argv[1:])
        return
    mode, selected = argv
    if mode in ('part', 'discover', '--placement'):
        if selected not in rows:
            raise ValueError(f'unknown CI job/part {selected!r}; choose: {", ".join(rows)}')
        chosen = [selected]
    else:
        chosen = [part for part, (name, row) in rows.items() if name == 'test' and (
            mode == 'matrix' or mode == 'full' and row['zig'] == selected and not row['mutate'] or
            mode == 'mutations' and row['mutate'])]
    if not chosen:
        raise ValueError('no matching CI matrix rows')
    if mode == '--placement':
        if rows[selected][0] == 'all-checks':
            raise ValueError('all-checks needs GitHub needs.*.result evidence; local receipts cannot replace it')
        print(RUNNERS[workflow['jobs'][rows[selected][0]]['runs-on']])
        return
    run = WorkflowRun(workflow, os.environ.get('AIR2LEAN_LOCAL_ARTIFACTS', '/artifacts'),
                       os.environ.get('AIR2LEAN_LOCAL_SNAPSHOT', '/snapshot'), mode == 'discover',
                       restricted=mode == 'part')
    for part in chosen:
        run.run(part)


if __name__ == '__main__':
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        main(sys.argv[1:])
    except Cancelled as error:
        raise SystemExit(128 + error.signum)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(f'local-ci: {error}')
