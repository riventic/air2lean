#!/usr/bin/env python3
"""Run the checkout's CI shell recipes locally; reject unsupported workflow syntax."""
import os
import hashlib
import importlib.util
import io
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
import tomllib



def prune_stale_modules(root, tracked, owners):
    """Remove only absent-source module facets from this package's physical build roots."""
    root = Path(root).absolute()
    if root.resolve(strict=True) != root:
        raise ValueError('cache pruning requires a physical checkout path')
    if any(not re.fullmatch(r'[A-Za-z_]\w*(?:/[A-Za-z_]\w*)*', owner, re.ASCII) for owner in owners):
        raise ValueError('invalid owned module root')
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW

    def open_dir(parent, parts):
        fd = os.dup(parent)
        try:
            for part in parts:
                child = os.open(part, flags, dir_fd=fd)
                os.close(fd)
                fd = child
            return fd
        except BaseException:
            os.close(fd)
            raise

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


if sys.argv[1:] == ['--prune-cache']:
    prune_current_cache(Path.cwd())
    raise SystemExit(0)


def expression(source, values):
    if isinstance(source, bool):
        return source
    source = source.strip()
    if source.startswith("${{") and source.endswith("}}"):
        source = source[3:-2].strip()
    zig_air = "format('{0}/zig-air-{1}/bin/zig', github.workspace, matrix.zig)"
    if zig_air in source:
        source = source.replace(zig_air, repr(f"{values['github.workspace']}/zig-air-{values['matrix.zig']}/bin/zig"))
    tokens = []
    while source:
        match = re.match(r"\s*(&&|\|\||==|!=|!|\(|\)|'[^']*'|(?:success|failure|cancelled|always)\(\)|[a-zA-Z][\w.-]*)", source)
        if not match:
            raise ValueError(f"unsupported CI expression: {source}")
        token = match[1]
        tokens.append(token[:-2] if token.endswith('()') else token)
        source = source[match.end():]
    pos = 0

    def atom():
        nonlocal pos
        if pos == len(tokens):
            raise ValueError('incomplete CI expression')
        token = tokens[pos]
        pos += 1
        if token == "!":
            return not atom()
        if token == '(':
            result = disjunction()
            if pos == len(tokens) or tokens[pos] != ')':
                raise ValueError('unclosed CI expression group')
            pos += 1
            return result
        if token.startswith("'"):
            return token[1:-1]
        if token not in values:
            raise ValueError(f"unsupported CI expression token: {token}")
        return values[token]

    def equality():
        nonlocal pos
        result = atom()
        if pos < len(tokens) and tokens[pos] in ('==', '!='):
            operator = tokens[pos]
            pos += 1
            rhs = atom()
            result = (result == rhs) if operator == '==' else (result != rhs)
        return result

    def conjunction():
        nonlocal pos
        result = equality()
        while pos < len(tokens) and tokens[pos] == "&&":
            pos += 1
            rhs = equality()
            result = rhs if result else result
        return result

    def disjunction():
        nonlocal pos
        result = conjunction()
        while pos < len(tokens) and tokens[pos] == "||":
            pos += 1
            rhs = conjunction()
            result = result if result else rhs
        return result

    result = disjunction()
    if pos != len(tokens):
        raise ValueError(f"unsupported CI expression tokens: {tokens[pos:]}")
    return result


def render(value, context):
    return re.sub(r"\$\{\{(.*?)\}\}", lambda m: str(expression(m[1], context)), str(value))


CACHE_LOCK_FD = None
CANCELLING = False


class Cancelled(BaseException):
    def __init__(self, signum):
        self.signum = signum
        super().__init__(f'cancelled by signal {signum}')


def stop(signum, _frame):
    # Waiting here re-enters Popen.wait's non-reentrant lock. Unwind it first.
    if not CANCELLING:
        raise Cancelled(signum)


def stop_group(child, signum):
    # The child starts its own session; this exact group belongs to this invocation.
    # Do not reap its leader until the group has been killed: surviving descendants
    # may close inherited lock descriptors or ignore TERM after their parent exits.
    for forwarded in (signum, signal.SIGKILL):
        try:
            os.killpg(child.pid, forwarded)
        except ProcessLookupError:
            break
        if forwarded != signal.SIGKILL:
            time.sleep(2)
    child.wait()


def call(command, **kwargs):
    global CANCELLING
    inherited = []
    for descriptor in {9, CACHE_LOCK_FD} - {None}:
        try:
            os.fstat(descriptor)
            inherited.append(descriptor)
        except OSError:
            pass
    child = subprocess.Popen(command, start_new_session=True, pass_fds=inherited, **kwargs)
    try:
        status = child.wait()
    except Cancelled as error:
        CANCELLING = True
        stop_group(child, error.signum)
        raise
    finally:
        CANCELLING = False
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
ALLOWED_ACTIONS = {'actions/checkout', 'actions/cache', 'actions/cache/restore',
                   'actions/upload-artifact', 'actions/download-artifact'}
REUSE = None


def reuse_helpers():
    global REUSE
    if REUSE is None:
        spec = importlib.util.spec_from_file_location('air2lean_local_ci_reuse', Path(__file__).with_name('ci-reuse.py'))
        REUSE = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(REUSE)
    return REUSE


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
        if set(strategy) - {'fail-fast', 'matrix'} or set(strategy.get('matrix', {})) - {'include'}:
            raise ValueError(f'{name}: unsupported CI matrix')
        for row in strategy.get('matrix', {}).get('include', [{}]):
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
        entry = reuse.declaration(reuse.load_declarations(Path.cwd()), part)
    except reuse.ReuseError as error:
        raise ValueError(str(error)) from error
    if entry.get('reuse') is not False:
        call(['python3', 'scripts/ci-reuse.py', 'restrict', '--part', part] +
             (['--discover'] if discover else ['--seal']))


def remove_entry(path):
    shutil.rmtree(path) if path.is_dir() and not path.is_symlink() else path.unlink()


def reset_checkout(snapshot, source):
    """Each job gets a fresh parentless snapshot, including after a producer sealed its history."""
    # CI's root Lake cache and packed artifact explicitly exclude this source checkout.
    # Keeping an earlier whole-tree copy would bypass the next row's withheld placeholders.
    check_tree = Path('.lake/check-tree')
    if check_tree.exists() or check_tree.is_symlink():
        remove_entry(check_tree)
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
    call(['git', '--literal-pathspecs', 'add', '-f', '--pathspec-from-file=' + str(snapshot / 'files'), '--pathspec-file-nul'])
    call(['git', 'commit', '-qm', 'Local tracked-source snapshot'], env=dict(os.environ, **reuse_helpers().IDENTITY))


class WorkflowRun:
    def __init__(self, workflow, artifacts, snapshot, discover=False):
        self.workflow = workflow
        self.rows = workflow_rows(workflow)
        self.artifacts, self.snapshot, self.discover = Path(artifacts), Path(snapshot), discover
        self.source = (self.snapshot / 'source.tar').read_bytes()
        self.source_sha = hashlib.sha256(self.source).hexdigest()
        # Do not leave a second copy of withheld content accessible to verification steps.
        # The interpreter retains the snapshot only in memory for later producer/consumer rows.
        (self.snapshot / 'source.tar').unlink()
        history = self.snapshot / 'main.bundle'
        self.history = history.read_bytes() if history.exists() else None
        if history.exists():
            history.unlink()
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
        reset_checkout(self.snapshot, self.source)
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
        if not re.fullmatch(r'[\w.-]+', artifact, re.ASCII):
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
        context = {f'matrix.{key}': value for key, value in row.items()}
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
        env.update({key: render(value, context) for key, value in job.get('env', {}).items()})
        report = {'schema': 'air2lean-local-ci-row/1', 'part': part, 'runner': runner,
                  'source': (self.artifacts / 'source-revision').read_text(),
                  'snapshot_sha256': self.source_sha,
                  'workflow_sha256': hashlib.sha256(Path('.github/workflows/ci.yml').read_bytes()).hexdigest(),
                  'steps': [], 'success': False}
        # Test setup is the existing verified/persistent Linux optimization, qualified against
        # the exact recipe text below. Native and support jobs execute their installers verbatim.
        optimized = name == 'test'
        qualification_failed = False
        try:
            validate_job(job, optimized)
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
                if self.discover or os.environ.get('AIR2LEAN_LOCAL_MODE') == 'part':
                    restrict_part(part, self.discover)
            elif name not in ('lake', 'zig-air', 'preflight'):
                restrict_part(part, self.discover)
            for step in job['steps']:
                record = {'name': step['name'], 'recipe_sha256': step_digest(step)}
                report['steps'].append(record)
                condition = step.get('if', '')
                status_condition = re.search(r'\b(?:success|failure|cancelled|always)\(\)',
                                             re.sub(r"'[^']*'", '', str(condition)))
                if not self.discover and not context['success'] and not status_condition:
                    record['status'] = 'prior-step-failed'
                    continue
                if 'if' in step and not expression(step['if'], context):
                    record['status'] = 'condition-false'
                    continue
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
                print(f'== CI {row if optimized else part}: {step["name"]} ==', flush=True)
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
                except (subprocess.CalledProcessError, OSError, ValueError) as error:
                    record.update(status='failed', error=str(error))
                    qualification_failed = True
                    if not step.get('continue-on-error'):
                        context.update(success=False, failure=True)
                finally:
                    record['seconds'] = round(time.monotonic() - started, 3)
                if self.discover:
                    try:
                        call(['python3', 'scripts/ci-reuse.py', 'check-restricted', '--reset'])
                    except subprocess.CalledProcessError:
                        context.update(success=False, failure=True)
                        qualification_failed = True
                        record['undeclared_reads'] = True
            call(['python3', 'scripts/ci-reuse.py', 'check-restricted'])
            report['success'] = context['success'] and not qualification_failed
        except BaseException as error:
            report['error'] = str(error)
            raise
        finally:
            (temp / 'row.json').write_text(json.dumps(report, indent=2) + '\n')
        if not report['success']:
            errors = '; '.join(f'{step["name"]}: {step["error"]}' for step in report['steps'] if 'error' in step)
            raise ValueError(f'{part}: workflow steps failed' + (f': {errors}' if errors else ''))


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
                     'AIR2LEAN_LOCAL_SNAPSHOT', 'AIR2LEAN_LOCAL_MODE', 'LANG', 'LC_ALL', 'TZ'}
        kept = {key: value for key, value in os.environ.items() if key in permitted}
        os.environ.clear()
        os.environ.update(kept)
        os.environ.update(HOME=str(home), ELAN_HOME=str(home / '.elan'),
                          AIR2LEAN_CACHE=str(tools / 'downloads'), ZIG_GLOBAL_CACHE_DIR=str(tools / 'zig-global'),
                          LEAN_NUM_THREADS='1', PATH=str(filtered))
        os.chdir(artifacts / 'work')
        run = WorkflowRun(workflow, artifacts, os.environ['AIR2LEAN_LOCAL_SNAPSHOT'], mode == 'discover')
        try:
            run.run(selected)
        finally:
            CACHE_LOCK_FD = None


def main(argv):
    import yaml
    workflow = yaml.safe_load(Path('.github/workflows/ci.yml').read_text())
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
                      os.environ.get('AIR2LEAN_LOCAL_SNAPSHOT', '/snapshot'), mode == 'discover')
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
