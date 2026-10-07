#!/usr/bin/env python3
"""Dependency/target doctor (scripts/doctor.sh). No downloads, builds or AIR export.

Every check yields one record: id, status (ok, note, warn, fail, skip), message and an
actionable hint. Supported versions, hosts and resource guidance come from compatibility.json.
Runs on Python 3.8+ so it works with the system Python of first-use hosts.
"""
import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True  # keep the checkout free of __pycache__
sys.path.insert(0, str(Path(__file__).resolve().parent))
import compat  # noqa: E402

DOCTOR_SCHEMA = 'air2lean-doctor/1'
TIMEOUT = 30
LABEL = {'ok': 'OK', 'note': 'note', 'warn': 'warning', 'fail': 'error', 'skip': 'skipped'}

USAGE = '''Usage: scripts/doctor.sh [--zig-version VERSION] [--zig-air PATH] [--require proofs|translate]
                        [--json] [--no-docker]

Check every prerequisite: host, compatibility metadata, elan and the pinned Lean toolchain
(lean-toolchain), stock Zig, each patched Zig and its AIR-only lock, the translator build,
bootstrap tools, Docker, disk and memory. No downloads or builds.
Defaults: Zig 0.16.0, zig-air-VERSION/bin/zig, --require translate.
  --require proofs     exit 0 once committed proofs can be checked (no Zig needed)
  --require translate  exit 0 once scripts/translate.sh can run (default)
  --json               print one machine-readable JSON report (schema air2lean-doctor/1)
  --no-docker          skip the Docker daemon probe
Environment: AIR2LEAN_ZIG_VERSION, AIR2LEAN_ZIG_AIR, AIR2LEAN_ZIG (stock Zig),
AIR2LEAN_DOCKER (docker command).
A version check cannot prove an arbitrary Zig binary includes the AIR exporter;
translate.sh checks that it actually writes fresh AIR.'''


class UsageError(Exception):
    pass


def host_name():
    machine = platform.machine().lower()
    machine = {'amd64': 'x86_64', 'arm64': 'aarch64'}.get(machine, machine)
    system = {'darwin': 'macos'}.get(platform.system().lower(), platform.system().lower())
    return machine + '-' + system


def run(cmd):
    """(exit code, stdout) of cmd; (None, reason) when it cannot run."""
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              universal_newlines=True, timeout=TIMEOUT)
    except (OSError, subprocess.SubprocessError) as exc:
        return None, str(exc)
    return proc.returncode, proc.stdout.strip() if proc.returncode == 0 else proc.stderr.strip()


def gib(n):
    return n / float(1 << 30)


def total_memory():
    try:
        return os.sysconf('SC_PAGE_SIZE') * os.sysconf('SC_PHYS_PAGES')
    except (ValueError, OSError, AttributeError):
        code, out = run(['sysctl', '-n', 'hw.memsize'])
        return int(out) if code == 0 and out.isdigit() else None


def lock_wrapper(root):
    """The exact wrapper text zig-patch/lock.sh installs as bin/zig, or None."""
    try:
        text = (root / 'zig-patch/lock.sh').read_text()
    except OSError:
        return None
    start = text.find('cat >"$bin/zig" <<\'EOF\'\n')
    if start < 0:
        return None
    body = text[start:].split('\n', 1)[1]
    end = body.find('\nEOF\n')
    return None if end < 0 else body[:end + 1]


class Doctor:
    def __init__(self, root, caller, args, env):
        self.root, self.caller, self.args, self.env = root, caller, args, env
        self.checks = []

    def add(self, cid, status, message, hint=None, **details):
        record = {'id': cid, 'status': status, 'message': message}
        if hint:
            record['hint'] = hint
        if details:
            record['details'] = details
        self.checks.append(record)
        return status

    # Individual checks -------------------------------------------------------------------
    def metadata(self):
        try:
            self.meta = compat.load(self.root)
            versions = self.meta['zig']['versions']
            self.versions = {e['version']: e for e in versions}
            self.order = [e['version'] for e in versions]
            self.budgets = self.meta['resources']
            self.args.zig_version = self.args.zig_version or self.meta['zig']['default']
        except (OSError, ValueError, KeyError, TypeError) as exc:
            self.add('metadata', 'fail', 'compatibility.json is missing or malformed: %s' % exc,
                     'restore compatibility.json from the repository (git checkout -- compatibility.json)')
            return False
        errors = compat.check(self.root)
        if errors:
            self.add('metadata', 'warn', 'compatibility.json disagrees with the repository (%d issue(s))' % len(errors),
                     'run python3 scripts/compat.py check and update compatibility.json or the drifted file',
                     errors=errors)
        else:
            self.add('metadata', 'ok', 'compatibility.json agrees with versions.toml and lean-toolchain')
        return True

    def host(self):
        self.host_id = host_name()
        supported = sorted({h for e in self.versions.values() for h in e['hosts']})
        if self.host_id not in supported:
            self.add('host', 'warn', 'host %s is not a supported host (%s)' % (self.host_id, ', '.join(supported)),
                     'use a supported host or the container recipe scripts/clean-env.sh', host=self.host_id)
        else:
            self.add('host', 'ok', 'host %s' % self.host_id, host=self.host_id)

    def zig_selection(self):
        version = self.args.zig_version
        if version not in self.versions:
            self.add('zig-version', 'fail', "unsupported Zig version '%s'" % version,
                     'choose one of ' + ', '.join(self.order))
            return False
        hosts = self.versions[version]['hosts']
        if self.host_id.endswith('-linux') or self.host_id.endswith('-macos'):
            same_os = [h for h in hosts if h.split('-')[1] == self.host_id.split('-')[1]]
            if not same_os:
                others = [v for v in self.order if any(h.split('-')[1] == self.host_id.split('-')[1]
                                                        for h in self.versions[v]['hosts'])]
                self.add('zig-version', 'fail', 'Zig %s is supported on %s only' % (version, ', '.join(hosts)),
                         'choose %s on this host' % ' or '.join(others))
                return False
        self.add('zig-version', 'ok', 'selected Zig %s (supported hosts: %s)' % (version, ', '.join(hosts)))
        return True

    def lean(self):
        toolchain_file = self.root / 'lean-toolchain'
        try:
            self.toolchain = toolchain_file.read_text().strip()
        except OSError:
            self.add('lean-toolchain', 'fail', 'lean-toolchain is missing', 'run from a complete checkout')
            return False
        if not shutil.which('elan', path=self.env.get('PATH')):
            self.add('elan', 'fail', 'elan is missing',
                     'install elan (https://github.com/leanprover/elan#installation), open a new terminal, '
                     'then run: elan toolchain install %s' % self.toolchain)
            return False
        code, out = run([shutil.which('elan', path=self.env.get('PATH')), 'toolchain', 'list'])
        if code != 0:
            self.add('elan', 'fail', 'could not list installed elan toolchains: %s' % out,
                     'repair the elan installation (elan self update)')
            return False
        self.add('elan', 'ok', 'elan is installed')
        installed = [line.split()[0] for line in out.splitlines() if line.split()]
        if self.toolchain not in installed:
            self.add('lean-toolchain', 'fail', 'pinned Lean toolchain %s is not installed' % self.toolchain,
                     'run: elan toolchain install %s' % self.toolchain, toolchain=self.toolchain)
            return False
        self.add('lean-toolchain', 'ok', 'pinned Lean %s is installed' % self.toolchain, toolchain=self.toolchain)
        built = (self.root / '.lake/build/lib/lean/Proofs/Basic/Proofs.olean').is_file()
        if built:
            self.add('proof-build', 'ok', 'Proofs.Basic.Proofs is built; tutorials and editors can import it')
        else:
            self.add('proof-build', 'note', 'Proofs.Basic.Proofs is not built yet',
                     'run: lake build Proofs.Basic.Proofs (editors report missing imports until then)')
        return True

    def stock_zig(self):
        version = self.args.zig_version
        stock = self.env.get('AIR2LEAN_ZIG') or 'zig'
        path = shutil.which(stock, path=self.env.get('PATH'))
        hint = 'only rebuilding the exporter needs stock Zig %s on PATH (zig-patch/build.sh)' % version
        if not path:
            self.add('stock-zig', 'note', 'stock Zig is missing (%s); %s' % (stock, hint.split(' (')[0]), hint)
            return
        code, out = run([path, 'version'])
        if code != 0:
            self.add('stock-zig', 'note', 'could not query stock Zig (%s); %s' % (stock, hint.split(' (')[0]), hint)
        elif out not in self.versions:
            self.add('stock-zig', 'note', 'stock Zig %s is unsupported' % out, hint, version=out)
        elif out != version:
            self.add('stock-zig', 'note', 'stock Zig %s (%s); rebuilding the Zig %s exporter needs stock Zig %s on PATH'
                     % (out, stock, version, version), hint, version=out)
        else:
            self.add('stock-zig', 'ok', 'stock Zig %s (%s)' % (out, stock), version=out)

    def patched(self, version, path, selected):
        """Check one patched compiler; return True when it is usable for translation."""
        cid = 'patched-zig-' + version
        build = 'zig-patch/build.sh %s with stock Zig %s on PATH; see zig-patch/README.md' % (version, version)
        miss = 'fail' if selected else 'skip'
        if path.name == 'zig-unlocked':
            self.add(cid, 'fail', 'use bin/zig, which preserves the AIR-only safety lock, instead of zig-unlocked',
                     'pass --zig-air %s' % path.with_name('zig'))
            return False
        if not path.is_file() or not os.access(str(path), os.X_OK):
            message = 'patched Zig is missing or not executable: %s' % path if selected else \
                'patched Zig %s is not built (optional): %s' % (version, path)
            self.add(cid, miss, message, 'from the repository, run ' + build, path=str(path))
            return False
        code, out = run([str(path), 'version'])
        if code != 0:
            self.add(cid, 'fail' if selected else 'warn', 'could not query patched Zig: %s' % path,
                     'rebuild it: ' + build, path=str(path))
            return False
        if out != version:
            self.add(cid, 'fail' if selected else 'warn',
                     "patched Zig reports '%s', expected '%s'" % (out, version),
                     'select the matching --zig-version and --zig-air, or rebuild: ' + build, path=str(path))
            return False
        lock = self.lock_state(path)
        status = {'locked': 'ok', 'llvm-or-unlocked': 'warn', 'stale-lock': 'warn', 'broken-lock': 'fail'}[lock[0]]
        if status == 'fail' and not selected:
            status = 'warn'
        self.add(cid, status, 'patched Zig %s (%s; exporter verified during translation); %s'
                 % (version, path, lock[1]), lock[2], path=str(path), lock=lock[0])
        return status != 'fail'

    def lock_state(self, path):
        """(state, description, hint) for the AIR-only lock of a patched compiler."""
        prefix = path.parent.parent
        unlocked = path.with_name('zig-unlocked')
        try:
            # The wrapper is a small script; never load a whole compiler binary.
            with open(str(path), 'rb') as f:
                head = f.read(64 * 1024 + 1)
            text = head.decode() if head.startswith(b'#!') and len(head) <= 64 * 1024 else ''
        except (OSError, UnicodeDecodeError):
            text = ''
        relock = 'run: zig-patch/lock.sh %s' % prefix
        if 'air2lean-lock' in text:
            if not os.access(str(unlocked), os.X_OK):
                return ('broken-lock', 'AIR-only lock wrapper without bin/zig-unlocked',
                        'rebuild the compiler: zig-patch/build.sh')
            expected = lock_wrapper(self.root)
            if expected is not None and text != expected:
                return ('stale-lock', 'AIR-only lock differs from zig-patch/lock.sh', relock)
            return ('locked', 'AIR-only lock active', None)
        if os.access(str(unlocked), os.X_OK):
            return ('broken-lock', 'bin/zig is not the AIR-only lock wrapper although bin/zig-unlocked exists',
                    relock)
        return ('llvm-or-unlocked', 'no AIR-only lock: valid only for an AIR2LEAN_LLVM=1 build',
                'if it was built without LLVM, ' + relock + ' (native code from a no-LLVM build can crash)')

    def translator(self):
        if os.access(str(self.root / '.lake/build/bin/air2lean'), os.X_OK):
            self.add('translator', 'ok', 'translator build exists; translate.sh refreshes it before use')
        else:
            self.add('translator', 'note', 'translator is not built yet; translate.sh builds it before exporting AIR')

    def tools(self, needed):
        path = self.env.get('PATH')
        missing = [t for t in ('curl', 'tar', 'xz', 'patch') if not shutil.which(t, path=path)]
        if not (shutil.which('sha256sum', path=path) or shutil.which('shasum', path=path)):
            missing.append('sha256sum or shasum')
        if not missing:
            self.add('bootstrap-tools', 'ok', 'curl, tar, xz, patch and a sha256 tool are available')
        else:
            self.add('bootstrap-tools', 'warn' if needed else 'note',
                     'zig-patch/build.sh needs: ' + ', '.join(missing),
                     'install them with the system package manager', missing=missing)

    def docker(self):
        if self.args.no_docker:
            self.add('docker', 'skip', 'Docker probe skipped (--no-docker)')
            return
        command = self.env.get('AIR2LEAN_DOCKER') or 'docker'
        hint = 'only scripts/local-ci.sh and scripts/clean-env.sh need Docker'
        if not shutil.which(command, path=self.env.get('PATH')):
            self.add('docker', 'note', 'Docker is not installed', hint)
            return
        code, out = run([shutil.which(command, path=self.env.get('PATH')), 'info', '--format', '{{.ServerVersion}} {{.Architecture}}'])
        if code != 0:
            self.add('docker', 'note', 'Docker is installed but the daemon is unreachable',
                     'start the Docker daemon; ' + hint, error=out[:300])
        else:
            self.add('docker', 'ok', 'Docker daemon %s' % out)

    def resources(self, profile):
        want = self.budgets[profile]
        try:
            free = shutil.disk_usage(str(self.root)).free
        except OSError:
            free = None
        if free is None:
            self.add('disk', 'warn', 'could not measure free disk space', None)
        elif gib(free) < want['min_disk_gib']:
            self.add('disk', 'warn', '%.1f GiB free at the repository; %s needs about %s GiB'
                     % (gib(free), profile, want['min_disk_gib']),
                     'free disk space (Lean toolchain, .lake build and Zig bootstrap caches)', free_gib=round(gib(free), 1))
        else:
            self.add('disk', 'ok', '%.1f GiB free at the repository' % gib(free), free_gib=round(gib(free), 1))
        memory = total_memory()
        if memory is None:
            self.add('memory', 'warn', 'could not measure physical memory', None)
        elif gib(memory) < want['min_memory_gib']:
            self.add('memory', 'warn', '%.1f GiB memory; %s needs about %s GiB'
                     % (gib(memory), profile, want['min_memory_gib']),
                     'close other programs, use LEAN_NUM_THREADS=1 and the default Debug -j1 Zig bootstrap',
                     total_gib=round(gib(memory), 1))
        else:
            self.add('memory', 'ok', '%.1f GiB memory' % gib(memory), total_gib=round(gib(memory), 1))

    # Driver ------------------------------------------------------------------------------
    def run(self):
        if not self.metadata():
            return {'proofs': False, 'translate': False}
        self.host()
        selection = self.zig_selection()
        proofs = self.lean()
        self.stock_zig()
        translate = proofs and selection
        if selection:
            selected = Path(self.args.zig_air) if self.args.zig_air else \
                self.root / ('zig-air-%s/bin/zig' % self.args.zig_version)
            if not selected.is_absolute():
                selected = self.caller / selected
            translate = self.patched(self.args.zig_version, selected, True) and translate
            for version in self.order:
                if version != self.args.zig_version and any(
                        h.split('-')[1] == self.host_id.split('-')[1] for h in self.versions[version]['hosts']):
                    self.patched(version, self.root / ('zig-air-%s/bin/zig' % version), False)
        self.translator()
        self.tools(needed=not translate)
        self.docker()
        self.resources(self.args.require)
        return {'proofs': proofs, 'translate': translate}


def parse(argv, env):
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('-h', '--help', action='store_true')
    parser.add_argument('--zig-version', default=env.get('AIR2LEAN_ZIG_VERSION') or None)
    parser.add_argument('--zig-air', default=env.get('AIR2LEAN_ZIG_AIR') or None)
    parser.add_argument('--require', choices=('proofs', 'translate'), default='translate')
    parser.add_argument('--json', action='store_true')
    parser.add_argument('--no-docker', action='store_true')
    parser.error = lambda message: (_ for _ in ()).throw(UsageError(message))
    args = parser.parse_args(argv)
    for name in ('zig_version', 'zig_air'):
        if getattr(args, name) == '':
            raise UsageError('missing value for --' + name.replace('_', '-'))
    return args


def main(argv=None, env=None, caller=None):
    env = dict(os.environ if env is None else env)
    try:
        args = parse(sys.argv[1:] if argv is None else argv, env)
    except UsageError as exc:
        print('error: %s' % exc, file=sys.stderr)
        print(USAGE, file=sys.stderr)
        return 2
    if args.help:
        print(USAGE)
        return 0
    root = Path(__file__).resolve().parents[1]
    doctor = Doctor(root, Path(caller or os.getcwd()), args, env)
    ready = doctor.run()
    code = 0 if ready[args.require] else 1
    if args.json:
        print(json.dumps({'schema': DOCTOR_SCHEMA, 'zig_version': args.zig_version, 'require': args.require,
                          'ready': ready, 'exit_code': code, 'checks': doctor.checks}, indent=2))
        return code
    for check in doctor.checks:
        if check['status'] == 'skip' and check['id'] != 'docker':
            continue
        print('%s: %s' % (LABEL[check['status']], check['message']))
        if check.get('hint') and check['status'] != 'ok':
            print('hint: %s' % check['hint'])
        for error in check.get('details', {}).get('errors', []):
            print('  - %s' % error)
        if check['id'] == 'lean-toolchain' and check['status'] == 'ok':
            print('Ready for committed proofs: lake build Proofs.Basic.Proofs')
    print('Model: x86_64-linux, baseline CPU, little-endian 64-bit pointers; ReleaseSafe AIR.')
    if ready['translate']:
        print('Ready: scripts/translate.sh INPUT.zig -o OUTPUT.lean --namespace My')
    elif ready['proofs']:
        print('Ready for proofs only: lake build Proofs.Basic.Proofs && lake env lean tutorials/first-proof/Main.lean')
    return code


if __name__ == '__main__':
    sys.exit(main())
