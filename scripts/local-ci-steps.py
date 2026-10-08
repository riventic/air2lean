#!/usr/bin/env python3
"""Run the checkout's CI shell recipes locally; reject unsupported workflow syntax."""
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
from textwrap import dedent
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
    source = source.strip()
    if source.startswith("${{") and source.endswith("}}"):
        source = source[3:-2].strip()
    source = source.replace(
        "format('{0}/zig-air-{1}/bin/zig', github.workspace, matrix.zig)",
        repr(f"/work/zig-air-{values['matrix.zig']}/bin/zig"),
    )
    tokens = []
    while source:
        match = re.match(r"\s*(&&|\|\||==|!|'[^']*'|[a-zA-Z][\w.-]*)", source)
        if not match:
            raise ValueError(f"unsupported CI expression: {source}")
        tokens.append(match[1])
        source = source[match.end():]
    pos = 0

    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == "!":
            return not atom()
        if token.startswith("'"):
            return token[1:-1]
        if token not in values:
            raise ValueError(f"unsupported CI expression token: {token}")
        return values[token]

    def equality():
        nonlocal pos
        result = atom()
        if pos < len(tokens) and tokens[pos] == "==":
            pos += 1
            result = result == atom()
        return result

    def conjunction():
        nonlocal pos
        result = equality()
        while pos < len(tokens) and tokens[pos] == "&&":
            pos += 1
            rhs = equality()
            result = rhs if result else result
        return result

    result = conjunction()
    while pos < len(tokens) and tokens[pos] == "||":
        pos += 1
        rhs = conjunction()
        result = result if result else rhs
    if pos != len(tokens):
        raise ValueError(f"unsupported CI expression tokens: {tokens[pos:]}")
    return result


def render(value, context):
    return re.sub(r"\$\{\{(.*?)\}\}", lambda m: str(expression(m[1], context)), str(value))


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
# The Q05 `macos` and T04 `aarch64-linux` jobs need native runners; local CI (an x86_64 Linux
# container) reproduces only the test job, and scripts/release-record.py requires GitHub evidence
# for their gates.
if set(workflow['jobs']) - {'macos', 'aarch64-linux'} != {'test'}:
    raise ValueError('local CI supports only the test job (and skips macos, aarch64-linux); '
                     'qualify new jobs explicitly')
job = workflow['jobs']['test']
if (job['runs-on'] != 'ubuntu-24.04' or 'defaults' in workflow or 'env' in workflow
        or set(job) - {'runs-on', 'timeout-minutes', 'env', 'strategy', 'steps'}
        or set(job['strategy']) - {'fail-fast', 'matrix'}
        or set(job['strategy']['matrix']) != {'include'}):
    raise ValueError('unsupported CI runner, defaults or workflow environment')
mode, version = sys.argv[1:]
rows = job['strategy']['matrix']['include']
if mode == 'full':
    rows = [row for row in rows if row['zig'] == version and not row['mutate']]
elif mode == 'mutations':
    rows = [row for row in rows if row['mutate']]
elif mode != 'matrix':
    raise ValueError(f'unsupported local CI mode: {mode}')
if not rows:
    raise ValueError('no matching CI matrix rows')

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
allowed_actions = {'actions/checkout', 'actions/cache', 'actions/upload-artifact'}
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
        expected_if = "steps.cache-zig-air.outputs.cache-hit != 'true'" if step['name'] == 'Build patched zig' else None
        if step.get('env') or step.get('if') != expected_if:
            raise ValueError(f"changed tool setup environment/guard: {step['name']}")

for number, row in enumerate(rows):
    if set(row) - {'zig', 'examples', 'full', 'mutate', 'shard'}:
        raise ValueError('unsupported matrix row fields')
    call(['git', 'restore', '.'])
    call(['git', 'clean', '-fdx', '-e', '.lake/', '-e', 'tests/diff/.lake/',
          '-e', 'host-zig/', '-e', 'zig-air-*/'])
    prune_current_cache(Path.cwd())
    call(['bash', 'scripts/local-ci.sh', '--prepare', row['zig']])
    temp = f"/artifacts/row-{number}-{row['zig']}"
    Path(temp).mkdir()
    context = {f'matrix.{key}': value for key, value in row.items()}
    context.update({'github.workspace': '/work', 'runner.temp': temp, 'runner.os': 'Linux'})
    env = dict(os.environ, RUNNER_TEMP=temp, GITHUB_WORKSPACE='/work', RUNNER_OS='Linux')
    env['PATH'] = f"/work/host-zig:{env['ELAN_HOME']}/bin:" + env['PATH']
    env.update({key: render(value, context) for key, value in job.get('env', {}).items()})
    for step in job['steps']:
        if 'uses' in step or step['name'] in setup:
            continue
        if 'if' in step and not expression(step['if'], context):
            continue
        code = render(step['run'], context)
        step_env = env | {key: render(value, context) for key, value in step.get('env', {}).items()}
        print(f"== CI {row}: {step['name']} ==", flush=True)
        call(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code], env=step_env)
