#!/usr/bin/env python3
"""Run the checkout's CI shell recipes locally; reject unsupported workflow syntax."""
import fnmatch
import hashlib
import importlib.util
import io
import os
from pathlib import Path
import re
import signal
import shutil
import stat
import subprocess
import sys
import tarfile
from textwrap import dedent


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


def reuse_helpers():
    spec = importlib.util.spec_from_file_location('ci_reuse', Path(__file__).with_name('ci-reuse.py'))
    reuse = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reuse)
    return reuse


def remove_check_trees(root):
    """CI's Lake cache excludes source copies; never retain one across restricted rows."""
    if not shutil.rmtree.avoids_symlink_attacks:
        raise ValueError('check-tree cleanup needs directory-anchored removal')
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
                    continue
                if stat.S_ISLNK(info.st_mode):
                    os.unlink('check-tree', dir_fd=parent)
                elif stat.S_ISDIR(info.st_mode):
                    shutil.rmtree('check-tree', dir_fd=parent)
                else:
                    raise ValueError('unsupported check-tree cache entry')
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


active = None


def stop(signum, _frame):
    if active is not None and active.poll() is None:
        os.killpg(active.pid, signum)
        try:
            active.wait(timeout=25)
        except subprocess.TimeoutExpired:
            os.killpg(active.pid, signal.SIGKILL)
            active.wait()
    raise SystemExit(128 + signum)


signal.signal(signal.SIGTERM, stop)
signal.signal(signal.SIGINT, stop)


def call(command, **kwargs):
    global active
    with subprocess.Popen(command, start_new_session=True, pass_fds=(9,), **kwargs) as active:
        status = active.wait()
    active = None
    if status:
        raise subprocess.CalledProcessError(status, command)


import yaml

workflow = yaml.safe_load(Path('.github/workflows/ci.yml').read_text())
# The Q05 `macos`, T04 `aarch64-linux`, T06 `build-modes-aarch64-linux` and L02 `bitops-native-arm` jobs need native runners;
# local CI (an x86_64 Linux container) reproduces only the test job, and
# scripts/release-record.py requires GitHub evidence for their gates. `lake` only pre-builds the
# cache that the test rows restore (local-ci.sh --prepare builds it here), `zig-air` the patched
# compilers, `preflight` repeats checks of the test rows, `generated` and `provenance` produce the
# whole-tree generated files (scripts/generated.py materialize/regen locally), and `all-checks` only
# aggregates job results.
SKIPPED_JOBS = {'macos', 'aarch64-linux', 'build-modes-aarch64-linux', 'bitops-native-arm', 'lake', 'zig-air',
                'preflight', 'generated', 'provenance', 'all-checks'}
if set(workflow['jobs']) - SKIPPED_JOBS != {'test'}:
    raise ValueError('local CI supports only the test job (and skips %s); '
                     'qualify new jobs explicitly' % ', '.join(sorted(SKIPPED_JOBS)))
job = workflow['jobs']['test']
# CI-only reuse machinery (docs/ci.md): the reuse decision, the in-run artifact unpacking that
# local-ci.sh --prepare replaces (and `scripts/generated.py materialize` for the generated files), and the record
# step. Local CI never reuses or records (`part` mode restricts the checkout like CI's decision);
# scripts/release-record.py does not count these steps as gates.
# The image (Dockerfile.local-ci) provides the system packages CI installs.
ci_only = {'Reuse a recorded result', 'Unpack the patched zig', 'Unpack the Lake build', 'Install the generated files',
           'Install system packages', 'Record the result for reuse'}
if (job['runs-on'] != 'ubuntu-24.04' or 'defaults' in workflow or 'env' in workflow or 'defaults' in job
        or set(job) - {'needs', 'runs-on', 'timeout-minutes', 'env', 'strategy', 'steps'}
        or set(job['strategy']) - {'fail-fast', 'matrix'}
        or set(job['strategy']['matrix']) != {'include'}):
    raise ValueError('unsupported CI runner, defaults or workflow environment')
mode, version = sys.argv[1:]
rows = job['strategy']['matrix']['include']
if mode == 'full':
    rows = [row for row in rows if row['zig'] == version and not row['mutate']]
elif mode in ('part', 'discover'):
    # One row in the restricted checkout CI gives it (scripts/ci-reuse.py restrict): `version` is
    # its part id, e.g. test/0.16.0/inputs. A withheld file it reads fails the row (as root here,
    # through check-restricted in "Checkout unchanged by verification").
    rows = [row for row in rows if CR.part_id('test', row) == version]
elif mode == 'mutations':
    rows = [row for row in rows if row['mutate']]
elif mode != 'matrix':
    raise ValueError(f'unsupported local CI mode: {mode}')
if not rows:
    raise ValueError('no matching CI matrix rows')
if mode in ('part', 'discover') and len(rows) != 1:
    raise ValueError('a local CI part must match exactly one matrix row')

# These three setup recipes are supplied by local-ci.sh with persistent, verified
# Linux caches. Everything else with a run: key executes from the workflow itself.
setup = {
    'Install host zig': dedent('''\
        set -euo pipefail
        url=$(zig-patch/toml-get.sh '[ci.host-zig."${{ matrix.zig }}"]' url)
        sha256=$(zig-patch/toml-get.sh '[ci.host-zig."${{ matrix.zig }}"]' sha256)
        curl -fL --output host-zig.tar.xz "$url"
        echo "$sha256  host-zig.tar.xz" | sha256sum -c -
        mkdir -p host-zig
        tar -xJf host-zig.tar.xz -C host-zig --strip-components=1
        echo "$PWD/host-zig" >> "$GITHUB_PATH"
    ''').strip(),
    'Install elan': dedent('''\
        set -euo pipefail
        url=$(zig-patch/toml-get.sh '[ci.elan]' url)
        sha256=$(zig-patch/toml-get.sh '[ci.elan]' sha256)
        curl -fL --output elan.tar.gz "$url"
        echo "$sha256  elan.tar.gz" | sha256sum -c -
        tar -xzf elan.tar.gz
        chmod +x elan-init
        ./elan-init --default-toolchain none -y
        echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
    ''').strip(),
    'Build patched zig': 'zig-patch/build.sh ${{ matrix.zig }} || zig-patch/build.sh ${{ matrix.zig }}',
}
allowed_actions = {'actions/checkout', 'actions/cache', 'actions/cache/restore', 'actions/upload-artifact',
                   'actions/download-artifact'}
for step in job['steps']:
    if set(step) - {'name', 'id', 'if', 'env', 'run', 'uses', 'with'}:
        raise ValueError(f"unsupported CI step fields: {step['name']}")
    if 'uses' in step and step['uses'].split('@')[0] not in allowed_actions:
        raise ValueError(f"unsupported CI action: {step['uses']}")
    if not ('run' in step or 'uses' in step):
        raise ValueError(f"unsupported CI step: {step['name']}")
    if step['name'] in setup and step.get('run', '').strip() != setup[step['name']]:
        raise ValueError(f"changed tool setup recipe needs qualification: {step['name']}")
    if step['name'] in setup:
        expected_if = '${{ !env.AIR2LEAN_REUSED }}'
        if step.get('env') or step.get('if') != expected_if:
            raise ValueError(f"changed tool setup environment/guard: {step['name']}")

failed = []
for number, row in enumerate(rows):
    if set(row) - {'zig', 'part', 'examples', 'full', 'mutate', 'shard'}:
        raise ValueError('unsupported matrix row fields')
    call(['python3', 'scripts/ci-reuse.py', 'unrestrict'])
    call(['git', 'restore', '.'])
    call(['git', 'clean', '-fdx', '-e', '.lake/', '-e', 'tests/diff/.lake/',
          '-e', 'host-zig/', '-e', 'zig-air-*/'])
    remove_check_trees(Path.cwd())
    prune_current_cache(Path.cwd())
    call(['bash', 'scripts/local-ci.sh', '--prepare', row['zig']])
    if mode in ('part', 'discover'):  # discover: the whole checkout, listing the undeclared files read
        call(['python3', 'scripts/ci-reuse.py', 'restrict', '--part', version] +
             (['--discover'] if mode == 'discover' else ['--seal']))
    temp = f"/artifacts/row-{number}-{row['zig']}"
    Path(temp).mkdir()
    context = {'matrix': row, 'github.workspace': '/work', 'runner.temp': temp,
               'runner.os': 'Linux', 'env.AIR2LEAN_REUSED': ''}
    env = dict(os.environ, RUNNER_TEMP=temp, GITHUB_WORKSPACE='/work', RUNNER_OS='Linux')
    env['PATH'] = f"/work/host-zig:{env['ELAN_HOME']}/bin:" + env['PATH']
    try:
        env.update({key: TM.interpolate(TM.expression_string(value), context)
                    for key, value in job.get('env', {}).items()})
    except TM.Unknown as error:
        raise ValueError(f'.github/workflows/ci.yml: test row {number}: job environment: '
                         f'unsupported expression: {error}') from error
    for step in job['steps']:
        if 'uses' in step or step['name'] in setup or step['name'] in ci_only:
            continue
        try:
            if not TM.condition(step.get('if'), context):
                continue
            code = TM.interpolate(step['run'], context)
            step_env = env | {key: TM.interpolate(TM.expression_string(value), context)
                              for key, value in step.get('env', {}).items()}
        except TM.Unknown as error:
            raise ValueError(f".github/workflows/ci.yml: test row {number}: step {step['name']!r}: "
                             f'unsupported expression: {error}') from error
        print(f"== CI {row}: {step['name']} ==", flush=True)
        try:
            call(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code], env=step_env)
        except subprocess.CalledProcessError:
            if mode != 'discover':
                raise
            failed.append(step['name'])  # discovery goes on: every undeclared read counts
        if mode == 'discover':  # attribute the reads to this step, then forget them
            try:
                call(['python3', 'scripts/ci-reuse.py', 'check-restricted', '--reset'])
            except subprocess.CalledProcessError:
                failed.append(step['name'] + ' (read undeclared files)')
if mode == 'discover':
    if failed:
        raise SystemExit('discovery: failed steps (on the whole checkout): ' + '; '.join(failed))
