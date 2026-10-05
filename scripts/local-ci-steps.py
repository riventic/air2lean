#!/usr/bin/env python3
"""Run the checkout's CI shell recipes locally; reject unsupported workflow syntax."""
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
from textwrap import dedent

import yaml


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


workflow = yaml.safe_load(Path('.github/workflows/ci.yml').read_text())
if set(workflow['jobs']) != {'test'}:
    raise ValueError('local CI supports only the test job; qualify new jobs explicitly')
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
