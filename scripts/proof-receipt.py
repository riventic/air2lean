#!/usr/bin/env python3
"""Bind a trusted local theorem audit to byte identities; never claim authenticity."""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import stat
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).absolute().parents[1]
MAX_JSON = 64 * 1024 * 1024
MAX_FILES = 30000
MAX_FILE = 512 * 1024 * 1024
MAX_TOTAL = 16 * 1024 * 1024 * 1024
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*')
OVERLAYS = ('LEAN', 'LAKE', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME', 'ELAN_TOOLCHAIN',
            'LD_PRELOAD', 'LD_LIBRARY_PATH', 'DYLD_LIBRARY_PATH', 'DYLD_INSERT_LIBRARIES')
INPUTS = ('lean-toolchain', 'lakefile.toml', 'assurance/policy.json', 'scripts/assumptions.py',
          'tools/Assurance.lean', 'scripts/proof-receipt.py', 'tests/roadmap/proof-receipts/check.sh')
OUTPUTS = ('before.json', 'audit.json', 'after.json')


def demand(ok, message):
    if not ok:
        raise ValueError(message)


def physical(path):
    path = Path(os.path.abspath(path))
    demand(path.resolve() == path, 'symlink path: ' + str(path))
    return path


def read_file(path, cap=MAX_FILE):
    path = physical(path)
    fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        demand(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), 'not a regular file: ' + str(path))
        raw = stream.read(cap + 1)
        demand(len(raw) <= cap, 'oversized file: ' + str(path))
        return raw


def fingerprint(path, allowance=None):
    path = physical(path)
    fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        initial = os.fstat(stream.fileno())
        demand(stat.S_ISREG(initial.st_mode), 'not a regular file: ' + str(path))
        cap = MAX_FILE if allowance is None else min(MAX_FILE, allowance)
        demand(cap >= 0 and initial.st_size <= cap, 'identity byte budget exhausted')
        sha, count = hashlib.sha256(), 0
        while chunk := stream.read(min(65536, cap - count + 1)):
            count += len(chunk)
            demand(count <= cap, 'identity byte budget exhausted')
            sha.update(chunk)
        final = os.fstat(stream.fileno())
        demand((initial.st_size, initial.st_mtime_ns, initial.st_ctime_ns) ==
               (final.st_size, final.st_mtime_ns, final.st_ctime_ns) and count == final.st_size,
               'file changed during hashing')
        return {'path': str(path), 'bytes': count, 'sha256': sha.hexdigest(),
                'mode': stat.S_IMODE(final.st_mode)}


def pairs(items):
    result = {}
    for key, value in items:
        demand(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def parse_json(raw):
    demand(len(raw) <= MAX_JSON, 'JSON exceeds byte bound')
    depth, quoted, escaped = 0, False, False
    for byte in raw:
        if quoted:
            if escaped:
                escaped = False
            elif byte == 92:
                escaped = True
            elif byte == 34:
                quoted = False
        elif byte == 34:
            quoted = True
        elif byte in (91, 123):
            depth += 1
            demand(depth <= 64, 'JSON exceeds nesting bound')
        elif byte in (93, 125):
            depth -= 1
    def number(value):
        demand(len(value) <= 24, 'oversized JSON number')
        return int(value)
    def decimal(value):
        demand(len(value) <= 64, 'oversized JSON decimal')
        result = float(value)
        demand(math.isfinite(result), 'nonfinite JSON decimal')
        return result
    return json.loads(raw, object_pairs_hook=pairs, parse_int=number, parse_float=decimal,
                      parse_constant=lambda _: demand(False, 'nonfinite JSON number'))


def mapping(value, label):
    demand(isinstance(value, dict), label + ' must be a JSON object')
    return value


def load(path):
    return mapping(parse_json(read_file(path, MAX_JSON)), str(path))


def write_new(path, data):
    path = physical(path)
    raw = (json.dumps(data, sort_keys=True, separators=(',', ':')) + '\n').encode()
    demand(len(raw) <= MAX_JSON, 'receipt exceeds byte bound')
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        except BaseException:
            temporary.unlink()
            raise
    try:
        os.link(temporary, path)  # Atomic no-clobber, including concurrent finalizers.
    finally:
        temporary.unlink()


def git(*args):
    return subprocess.run(['git', '-C', str(ROOT), *args], check=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=5).stdout


def revision():
    return {'head': git('rev-parse', 'HEAD').decode().strip(),
            'tracked_dirty': bool(git('status', '--porcelain', '--untracked-files=no'))}


def tracked():
    paths = git('ls-files', '-z').decode().split('\0')[:-1]
    demand(paths == sorted(set(paths)) and 0 < len(paths) <= MAX_FILES, 'invalid tracked inventory')
    return paths


def source_target(path, names):
    path = Path(os.path.abspath(path))
    physical(path.parent)
    demand(path.relative_to(ROOT).as_posix() in names, 'source is not tracked')
    if not path.is_symlink():
        return physical(path), None
    link = os.readlink(path)
    demand(not Path(link).is_absolute(), 'absolute source alias')
    target = physical(path.parent / link)  # Reject directory aliases and alias chains.
    demand(target.is_relative_to(ROOT) and target.relative_to(ROOT).as_posix() in names,
           'source alias target must be tracked inside repository')
    return target, link


def source_fingerprint(path, names, allowance):
    target, link = source_target(path, names)
    if link is None:
        return dict(fingerprint(target, allowance), kind='regular')
    initial = Path(path).lstat()
    link_bytes = len(os.fsencode(link))
    content = fingerprint(target, allowance - link_bytes)
    final = Path(path).lstat()
    demand((initial.st_mode, initial.st_size, initial.st_mtime_ns, initial.st_ctime_ns) ==
           (final.st_mode, final.st_size, final.st_mtime_ns, final.st_ctime_ns)
           and os.readlink(path) == link, 'source alias changed during hashing')
    return {'path': str(path), 'kind': 'symlink', 'link': link, 'target': content,
            'bytes': link_bytes + content['bytes']}


def inventory(paths, source_names=None):
    demand(len(paths) <= MAX_FILES, 'file inventory exceeds bound')
    rows, remaining = [], MAX_TOTAL
    for path in sorted(paths):
        row = (fingerprint(path, remaining) if source_names is None
               else source_fingerprint(path, source_names, remaining))
        remaining -= row['bytes']
        rows.append(row)
    return rows


def source_inventory(names=None):
    names = tracked() if names is None else names
    return inventory([ROOT / path for path in names], set(names))


def tree(directory):
    directory = physical(directory)
    demand(directory.is_dir(), 'missing identity directory: ' + str(directory))
    paths = []
    for parent, directories, files in os.walk(directory):
        for name in directories + files:
            physical(Path(parent) / name)
        paths.extend(Path(parent) / name for name in files)
        demand(len(paths) <= MAX_FILES, 'directory inventory exceeds bound')
    return paths


def module_file(module):
    demand(isinstance(module, str) and MODULE.fullmatch(module), 'invalid module name')
    return module.replace('.', '/') + '.lean'


def helper(name):
    spec = importlib.util.spec_from_file_location('receipt_' + name, ROOT / 'scripts' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def context(plan):
    overlays = set(OVERLAYS) | {name for name in os.environ
        if name.startswith(('LEAN_', 'LAKE_', 'DYLD_')) and name != 'LEAN_NUM_THREADS'}
    for name in overlays:
        demand(not os.environ.get(name), 'environment overlay: ' + name)
    demand(not (ROOT / 'lakefile.lean').exists(), 'lakefile.lean shadows selected configuration')
    manifest = load(ROOT / 'lake-manifest.json')
    demand(manifest.get('packages') == [] and manifest.get('packagesDir') == '.lake/packages'
           and manifest.get('lakeDir') == '.lake', 'external Lake package closure is unsupported')
    packages = ROOT / '.lake/packages'
    demand(not packages.exists() or not tree(packages), 'unrecorded Lake packages')
    names = tracked()
    for path in git('ls-files', '--others', '--exclude-standard', '-z').decode().split('\0')[:-1]:
        demand(not path.endswith(('.lean', '.json', '.toml', '.py', '.sh')), 'untracked build input: ' + path)
    demand(all(module_file(m) in names for m in plan['modules']), 'selected module source is not tracked')
    toolchain = physical(plan['toolchain'])
    tools = inventory([toolchain / 'bin/lean', toolchain / 'bin/lake', Path(sys.executable).resolve()])
    return {'revision': revision(), 'sources': source_inventory(names),
            'tools': tools, 'lean_library': inventory(tree(toolchain / 'lib/lean'))}


def compiled(plan):
    own = ROOT / '.lake/build/lib/lean'
    files = tree(own)
    names = set(tracked())
    for path in files:
        suffix = str(path.relative_to(own))
        if '.olean' in suffix:
            source = suffix.split('.olean', 1)[0] + '.lean'
            demand(source in names, 'compiled module has no tracked source: ' + suffix)
            demand(source not in ('Init.lean', 'Std.lean', 'Lean.lean')
                   and not source.startswith(('Init/', 'Std/', 'Lean/')), 'standard-library module shadow')
    for module in plan['modules'] + ['tools.Assurance']:
        base = own / module.replace('.', '/')
        demand(base.with_suffix('.olean').is_file(), 'missing selected compiled module: ' + module)
        demand(base.with_suffix('.trace').is_file(), 'missing selected Lake trace: ' + module)
    return inventory(files)


def profiles():
    split = helper('normalize-generated').split_generated
    result = {}
    names = set(tracked())
    for path in sorted(names):
        if path.endswith('/Gen.lean'):
            identity = source_fingerprint(ROOT / path, names, MAX_TOTAL)
            target, _ = source_target(ROOT / path, names)
            raw = read_file(target, MAX_JSON)
            demand(identity == source_fingerprint(ROOT / path, names, MAX_TOTAL)
                   and hashlib.sha256(raw).hexdigest() ==
                   (identity['target'] if identity['kind'] == 'symlink' else identity)['sha256'],
                   'generated source changed during profile read')
            metadata, _ = split(raw)
            result[path] = {'sha256': hashlib.sha256(raw).hexdigest(), 'metadata': metadata,
                            'scope': 'validated-header' if metadata else 'legacy-or-unannotated'}
    return result


def plan_for(attempt):
    attempt = physical(attempt)
    plan = load(attempt / 'plan.json')
    demand(set(plan) == {'schema', 'root', 'attempt', 'toolchain', 'profile', 'lock', 'modules', 'scope', 'python', 'revision', 'sources', 'guard'},
           'unknown plan fields')
    demand(type(plan['schema']) is int and plan['schema'] == 1 and plan['root'] == str(ROOT)
           and plan['attempt'] == str(attempt), 'plan root/attempt mismatch')
    demand(plan['scope'] in ('all-shipped-modules', 'explicit-modules') and plan['modules'] == sorted(set(plan['modules']))
           and bool(plan['modules']), 'invalid plan scope')
    for module in plan['modules']:
        module_file(module)
    if plan['scope'] == 'all-shipped-modules':
        demand(plan['modules'] == helper('assumptions').shipped_modules(), 'shipped inventory changed')
    demand(plan['python'] == str(Path(sys.executable).resolve()), 'planned Python identity differs')
    mapping(plan['guard'], 'planned guard')
    demand(plan['guard'] == fingerprint(plan['guard']['path']), 'reviewed guard identity changed')
    demand(isinstance(plan['profile'], str) and 0 < len(plan['profile']) <= 128, 'invalid run profile label')
    return plan


def audit_ok(plan, audit):
    mapping(audit, 'audit')
    demand(audit.get('status') == 'pass' and audit.get('scope') == plan['scope']
           and audit.get('modules') == plan['modules'] and audit.get('build_checked') is True,
           'audit status/scope/build mismatch')
    theorems = audit.get('theorems')
    demand(isinstance(theorems, list) and bool(theorems) and len(theorems) <= MAX_FILES,
           'empty/oversized theorem inventory')
    for theorem in theorems:
        mapping(theorem, 'theorem entry')
    nodes = audit.get('nodes')
    demand(isinstance(nodes, list) and len(nodes) <= MAX_FILES, 'invalid declaration graph')
    for node in nodes:
        mapping(node, 'declaration entry')
        demand(all(isinstance(node.get(key), str) for key in ('name', 'module', 'kind'))
               and isinstance(node.get('dependencies'), list)
               and all(isinstance(d, str) for d in node['dependencies']), 'invalid declaration entry')
    demand(type(audit.get('theorem_count')) is int and audit['theorem_count'] == len(theorems)
           and len({t['name'] for t in theorems}) == len(theorems)
           and all(t['module'] in plan['modules'] and t['allowed'] is True for t in theorems),
           'invalid theorem inventory')
    policy_path = ROOT / 'assurance/policy.json'
    load(policy_path)  # Enforce duplicate-key/size bounds before the existing policy loader.
    auditor = helper('assumptions')
    policy = auditor.load_policy(policy_path)
    recalculated = auditor.apply_policy(audit, policy)
    for key in recalculated:
        demand(audit.get(key) == recalculated[key], 'audit graph/policy mismatch: ' + key)
    demand(audit['policy_sha256'] == fingerprint(policy_path)['sha256']
           and audit['lean_toolchain'] == read_file(ROOT / 'lean-toolchain', 4096).decode().strip(),
           'audit policy/toolchain mismatch')
    validated_modules = set()
    for node in nodes:
        module = node['module']
        if module and module not in validated_modules:
            module_file(module)
            relative = module.replace('.', '/') + '.olean'
            own, standard = ROOT / '.lake/build/lib/lean' / relative, Path(plan['toolchain']) / 'lib/lean' / relative
            demand(own.is_file() or standard.is_file(), 'audit module artifact missing: ' + module)
            validated_modules.add(module)
    extractor = mapping(audit['extractor'], 'audit extractor')
    for key, path in [('source_sha256', ROOT / 'tools/Assurance.lean'),
                      ('olean_sha256', ROOT / '.lake/build/lib/lean/tools/Assurance.olean'),
                      ('lake_trace_sha256', ROOT / '.lake/build/lib/lean/tools/Assurance.trace'),
                      ('lean_toolchain_sha256', ROOT / 'lean-toolchain'), ('lake_config_sha256', ROOT / 'lakefile.toml')]:
        demand(extractor[key] == fingerprint(path)['sha256'], 'extractor identity mismatch: ' + key)


def worker(attempt):
    plan = plan_for(attempt)
    demand(os.environ.get('LEAN_NUM_THREADS') == '1', 'guard single-thread environment is missing')
    descriptor = os.open(physical(plan['lock']), os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    with os.fdopen(descriptor, 'rb') as lock:
        demand(stat.S_ISREG(os.fstat(lock.fileno()).st_mode), 'guard lock is not regular')
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            pass
        else:
            raise ValueError('worker requires an already-held root guard lock')
    demand(str(Path(os.environ['PATH'].split(os.pathsep)[0])) == str(Path(plan['toolchain']) / 'bin'),
           'selected toolchain must be first on PATH')
    before = context(plan)
    demand(before['revision'] == plan['revision'] and before['sources'] == plan['sources'],
           'planned source context changed before guarded audit')
    write_new(Path(attempt) / 'before.json', before)
    argv = [plan['python'], str(ROOT / 'scripts/assumptions.py'), '--output', str(Path(attempt) / 'audit.json')]
    if plan['scope'] == 'explicit-modules':
        for module in plan['modules']:
            argv += ['--module', module]
    result = subprocess.run(argv, cwd=ROOT)  # The existing outer guard owns timeout and cleanup.
    if result.returncode:
        return result.returncode if result.returncode > 0 else 128 - result.returncode
    after = context(plan)
    demand(before == after, 'source/tool/library context changed during audit')
    audit_ok(plan, load(Path(attempt) / 'audit.json'))
    write_new(Path(attempt) / 'after.json', {'context': after, 'compiled': compiled(plan), 'profiles': profiles()})
    return 0


def evidence_matches(rows, paths):
    expected = [fingerprint(path) for path in paths]
    demand(isinstance(rows, list) and len(rows) == len(expected), 'guard identity inventory mismatch')
    for row, actual in zip(rows, expected):
        demand(isinstance(row, dict), 'malformed guard identity row')
        demand(all(row.get(key) == actual[key] for key in ('path', 'sha256', 'bytes')),
               'guard identity mismatch: ' + actual['path'])


def seal(attempt):
    attempt = physical(attempt)
    plan = plan_for(attempt)
    before, after, audit, guard = [load(attempt / name) for name in ('before.json', 'after.json', 'audit.json', 'guard.json')]
    demand(type(guard.get('schema')) is int and guard['schema'] == 1 and guard.get('outcome') == 'success'
           and type(guard.get('exit_code')) is int and guard['exit_code'] == 0
           and type(guard.get('child_status')) is int and guard['child_status'] == 0
           and guard.get('log_truncated') is False and guard.get('drain_incomplete') is False,
           'guard did not complete successfully')
    overrides = mapping(guard.get('environment_overrides'), 'guard environment overrides')
    command = [plan['python'], str(ROOT / 'scripts/proof-receipt.py'), 'worker', str(attempt)]
    demand(guard.get('requested_command') == command and guard.get('command') == command
           and guard.get('cwd') == str(ROOT) and guard.get('profile') == plan['profile']
           and guard.get('phase') == 'proof' and guard.get('lock') == plan['lock']
           and guard.get('revision') == before['revision']
           and overrides.get('LEAN_NUM_THREADS') == '1', 'guard invocation mismatch')
    evidence_matches(guard['inputs'], [attempt / 'plan.json'] + [ROOT / path for path in INPUTS] + [Path(plan['guard']['path'])])
    evidence_matches(guard['outputs'], [attempt / path for path in OUTPUTS])
    evidence_matches(guard['pins'], [ROOT / 'lean-toolchain', ROOT / 'zig-patch/versions.toml'])
    evidence_matches([guard['guard']], [plan['guard']['path']])
    ps = shutil.which('ps')
    demand(ps is not None, 'guard observer tool missing')
    evidence_matches(guard['tools'], [plan['python'], plan['python'], Path(ps).resolve(),
                                    Path(plan['toolchain']) / 'bin/lean', Path(plan['toolchain']) / 'bin/lake'])
    logfile = fingerprint(attempt / 'guard.log')
    demand(guard['log'] == logfile['path'] and guard['log_sha256'] == logfile['sha256']
           and guard['log_bytes'] == logfile['bytes'], 'guard log mismatch')
    demand(before['revision'] == plan['revision'] and before['sources'] == plan['sources']
           and before == after['context'] == context(plan), 'source context stale')
    demand(after['compiled'] == compiled(plan) and after['profiles'] == profiles(), 'compiled/profile context stale')
    audit_ok(plan, audit)
    write_new(attempt / 'receipt.json', {'schema': 1, 'status': 'audited', 'authentication': 'not_attested',
              'proof_scope': 'selected compiled Lean theorem dependency policy only',
              'source_correspondence': 'not_attested', 'native_adequacy': 'not_attested',
              'attempt': str(attempt), 'theorem_count': audit['theorem_count'],
              'artifacts': inventory([attempt / n for n in ('plan.json', *OUTPUTS, 'guard.json', 'guard.log')])})


def verify(attempt):
    attempt = physical(attempt)
    receipt = load(attempt / 'receipt.json')
    demand(set(receipt) == {'schema', 'status', 'authentication', 'proof_scope', 'source_correspondence',
                          'native_adequacy', 'attempt', 'theorem_count', 'artifacts'} and
           type(receipt['schema']) is int and receipt['schema'] == 1 and receipt['status'] == 'audited' and receipt['attempt'] == str(attempt)
           and receipt['authentication'] == receipt['source_correspondence'] == receipt['native_adequacy'] == 'not_attested'
           and receipt['proof_scope'] == 'selected compiled Lean theorem dependency policy only',
           'invalid receipt')
    demand(receipt['artifacts'] == inventory([attempt / n for n in ('plan.json', *OUTPUTS, 'guard.json', 'guard.log')]),
           'receipt artifacts changed')
    plan, after, audit = plan_for(attempt), load(attempt / 'after.json'), load(attempt / 'audit.json')
    demand(type(receipt['theorem_count']) is int and receipt['theorem_count'] == audit['theorem_count'], 'receipt theorem count mismatch')
    demand(after['context'] == context(plan) and after['compiled'] == compiled(plan)
           and after['profiles'] == profiles(), 'receipt stale')
    audit_ok(plan, audit)
    return {'status': 'current', 'checking': 'not_rerun', 'authentication': 'not_attested'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('prepare', 'worker', 'seal', 'verify'))
    parser.add_argument('attempt', type=Path)
    parser.add_argument('--toolchain', type=Path)
    parser.add_argument('--profile')
    parser.add_argument('--guard', type=Path, default=ROOT / 'scripts/build-guard.py')
    parser.add_argument('--guard-sha256')
    parser.add_argument('--module', action='append', default=[])
    parser.add_argument('--lock', type=Path, default=Path(os.environ.get('AIR2LEAN_BUILD_LOCK',
                                                              str(Path.home() / '.cache/air2lean/build.lock'))))
    a = parser.parse_args()
    try:
        demand(a.attempt.is_absolute(), 'attempt path must be absolute')
        attempt = physical(a.attempt)
        if a.action == 'prepare':
            demand(a.toolchain is not None and a.profile is not None, 'prepare needs toolchain and profile label')
            demand(a.toolchain.is_absolute(), 'toolchain path must be absolute')
            guard = fingerprint(a.guard)
            if a.guard != ROOT / 'scripts/build-guard.py':
                demand(a.guard_sha256 is not None, 'external guard requires reviewed --guard-sha256')
            if a.guard_sha256 is not None:
                demand(bool(re.fullmatch('[0-9a-f]{64}', a.guard_sha256)) and a.guard_sha256 == guard['sha256'],
                       'reviewed guard SHA256 mismatch')
            modules = sorted(set(a.module)) if a.module else helper('assumptions').shipped_modules()
            for module in modules:
                module_file(module)
            plan = {'schema': 1, 'root': str(ROOT), 'attempt': str(attempt),
                    'toolchain': str(physical(a.toolchain)), 'profile': a.profile, 'lock': str(physical(a.lock)),
                    'modules': modules, 'scope': 'explicit-modules' if a.module else 'all-shipped-modules',
                    'python': str(Path(sys.executable).resolve()), 'revision': revision(),
                    'sources': source_inventory(), 'guard': guard}
            attempt.mkdir(mode=0o700)
            write_new(attempt / 'plan.json', plan)
        elif a.action == 'worker':
            return worker(attempt)
        elif a.action == 'seal':
            seal(attempt)
        else:
            print(json.dumps(verify(attempt)))
        return 0
    except (OSError, ValueError, KeyError, TypeError, RecursionError, subprocess.SubprocessError) as error:
        print('proof receipt unavailable/stale: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
