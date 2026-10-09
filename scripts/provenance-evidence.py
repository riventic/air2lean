#!/usr/bin/env python3
"""I07 provenance evidence: check the committed receipt-chained manifests, replay their receipts, or regenerate.

Two fixtures are committed (`--fixture`): `provenance` (assurance/provenance, x86_64-linux) and
`gap` (assurance/provenance-gap, aarch64-macos), each a manifest chaining source, AIR, profile,
Gen.lean, proofs, a schema-2 proof receipt and a native-build identity.

`check` is offline (no Zig, Lake or Lean): it rechecks a fixture's manifest.json against the tree
with the reviewer pins in its pins.json. Drift in the repository-wide links (compiler patch,
translator, runtime, toolchain) is reported as `aged` and only fails with `--strict`; every
example-local link (source, AIR, profile, Gen.lean, proofs, theorem names, receipt, native
record) must be current.

`replay` is also offline and needs neither the receipt's revision nor its attempt directory. The
committed plan.json records the sha256 of every tracked source, so the receipt is replayed against
the tree itself: it finds the Lean import closure of the proved module, reports which closure files
still have the bytes the receipt compiled (fixture-local drift is `stale`, shared ZigLean or
toolchain drift is `aged`, `--strict` fails on it), checks the audit (status, policy, theorem set
against the manifest) and scans the committed copy for host-local paths. `replay --rerun WORKDIR`
additionally reruns the guarded proof receipt on the current tree and requires the same compiled
theorem audit as the committed one.

`regenerate WORKDIR` reruns the pipeline on the checkout (patched 0.16.0 AIR-only export,
translation, native build with stock Zig, guarded proof receipt) and requires the fresh bytes to
match the committed fixture before it records and strictly checks a fresh manifest. It writes
only under WORKDIR. Every Zig/Lake/Lean run goes through scripts/build-guard.py and the lock in
AIR2LEAN_BUILD_LOCK. See docs/artifact-manifest.md.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parents[1]
_spec = importlib.util.spec_from_file_location('artifact_manifest', ROOT / 'scripts/artifact-manifest.py')
am = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(am)

VERSION = '0.16.0'
GLOBAL_LINKS = ('compiler_patch', 'translator', 'runtime', 'toolchain')
# Files outside the Lean import closure that the receipt's audit also depends on (check.sh inputs).
ENVIRONMENT = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'assurance/policy.json', 'tools/Assurance.lean')
FIXTURES = {
    'provenance': dict(
        dir='assurance/provenance', example='provenance', namespace='Provenance', prefix='provenance.',
        filter='provenance.add,provenance.double', source='assurance/provenance/src/provenance.zig',
        target='x86_64-linux', proof_module='Proofs.Provenance.Proofs', label='provenance-fresh'),
    'gap': dict(
        dir='assurance/provenance-gap', example='gap', namespace='ProvenanceGap', prefix='gap.',
        filter='gap.gap,gap.within', source='assurance/provenance-gap/src/gap.zig',
        target='aarch64-macos', proof_module='Proofs.ProvenanceGap.Proofs', label='provenance-gap-fresh'),
}
for _fx in FIXTURES.values():
    _fx['gen'] = 'Proofs/%s/Gen.lean' % _fx['namespace']
    _fx['proofs'] = 'Proofs/%s/Proofs.lean' % _fx['namespace']
    _fx['path'] = ROOT / _fx['dir']
    _fx['binary'] = _fx['example']


def fixture(name):
    return FIXTURES[name]


def check(fx, strict, native_binary=None, native_compiler=None):
    pins = json.loads((fx['path'] / 'pins.json').read_text())
    expect = ['zig_version=' + pins['zig_version'], 'profile=' + pins['profile_sha256'],
              'source=' + pins['source_sha256'], 'native=' + pins['native_sha256']]
    manifest = json.loads((fx['path'] / 'manifest.json').read_text())
    problems = []
    if manifest.get('manifest_sha256') != pins['manifest_sha256']:
        problems.append('manifest_sha256 differs from the reviewer pin in pins.json')
    report = am.check_manifest(ROOT, fx['path'] / 'manifest.json', expect, False, False, native_binary, native_compiler,
                               native_binary is not None)
    aged = [n for n in report['stale_links'] if n in GLOBAL_LINKS]
    local = [n for n in report['stale_links'] if n not in GLOBAL_LINKS]
    problems += report['problems']
    if report['status'] == 'invalid':
        status = 'invalid'
    elif problems or local or (strict and aged):
        status = 'stale'
    else:
        status = 'current'
    return dict(report, status=status, aged_links=aged, local_stale_links=local, problems=problems)


# ---------------------------------------------------------------- replay (offline)

IMPORT = re.compile(r'import\s+(.*)')
LOCAL_PATH = re.compile(r'(^/)|/(Users|home|private|opt|var|tmp|root)/')


def sha256_file(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_closure(root, module):
    """Repository files in the Lean import closure of `module`, and the modules found nowhere in it."""
    files, external, pending = {}, set(), [module]
    while pending:
        name = pending.pop()
        if name in files or name in external:
            continue
        relative = '/'.join(name.split('.')) + '.lean'
        path = root / relative
        if not path.is_file() or path.is_symlink():
            external.add(name)
            continue
        files[name] = relative
        for line in path.read_text().splitlines():
            stripped = line.strip()
            if stripped.startswith('import '):
                pending += IMPORT.fullmatch(stripped).group(1).split('--')[0].split()
            elif stripped and not stripped.startswith('--'):
                break
    return files, sorted(external)


def host_paths(value, found):
    """Strings that look like host-local absolute paths (placeholders `<repo>`, `~`, `<host>/x` are fine)."""
    if isinstance(value, dict):
        for key, item in value.items():
            host_paths(key, found)
            host_paths(item, found)
    elif isinstance(value, list):
        for item in value:
            host_paths(item, found)
    elif isinstance(value, str) and LOCAL_PATH.search(value):
        found.append(value[:80])
    return found


def revision_available(root, head):
    if not isinstance(head, str) or not re.fullmatch(r'[0-9a-f]{40}', head):
        return False
    done = subprocess.run(['git', '-C', str(root), 'cat-file', '-e', head + '^{commit}'], capture_output=True)
    return done.returncode == 0


def replay(fx, strict, root=ROOT):
    """Replay the committed receipt against the tree, without its revision or its attempt directory."""
    folder = Path(root) / fx['dir'] / 'receipt'
    receipt, plan, audit = (json.loads((folder / n).read_text()) for n in ('receipt.json', 'plan.json', 'audit.json'))
    manifest = json.loads((Path(root) / fx['dir'] / 'manifest.json').read_text())
    module = fx['proof_module']
    problems = []
    if not (receipt.get('schema') == 2 and receipt.get('status') == 'audited' and plan.get('schema') == 1
            and plan.get('scope') == 'explicit-modules' and plan.get('modules') == [module]):
        problems.append('receipt copy is not a schema-2 audited explicit-module receipt for ' + module)
    if audit.get('status') != 'pass' or audit.get('violations') or audit.get('build_checked') is not True:
        problems.append('audit did not pass the dependency policy with a checked build')
    toolchain_file = (Path(root) / 'lean-toolchain').read_text().strip()
    if audit.get('lean_toolchain') != toolchain_file:
        problems.append('receipt audited %s, tree pins %s' % (audit.get('lean_toolchain'), toolchain_file))
    local = host_paths([receipt, plan, audit, manifest], [])
    problems += ['host-local path in the committed receipt: ' + p for p in local[:5]]
    # The theorem set the manifest chained must be what the audit contains for this module.
    chained = manifest['links']['theorems']['value']
    selected = [t for t in audit.get('theorems', []) if t.get('module') == module]
    names = sorted(t['name'] for t in selected)
    if names != chained['compiled_audit']['names'] or not set(chained['source_scan']) <= set(names) \
            or any(t.get('allowed') is not True for t in selected):
        problems.append('audited theorems of %s differ from the manifest theorem names or violate the policy' % module)
    # Input bytes: every closure file must carry the sha256 the receipt compiled.
    recorded = {row['path'].removeprefix('<repo>/'): row.get('sha256') for row in plan.get('sources', [])
                if isinstance(row, dict) and row.get('kind') == 'regular' and isinstance(row.get('path'), str)}
    closure, external = lean_closure(Path(root), module)
    own = 'Proofs/%s/' % fx['namespace']
    changed, unrecorded = [], []
    for relative in sorted([*closure.values(), *ENVIRONMENT]):
        if relative not in recorded:
            unrecorded.append(relative)
        elif sha256_file(Path(root) / relative) != recorded[relative]:
            changed.append(relative)
    stale_local = [p for p in changed + unrecorded if p.startswith(own)]
    aged = [p for p in changed + unrecorded if not p.startswith(own)]
    head = (plan.get('revision') or {}).get('head')
    if problems or stale_local:
        status = 'stale'
    elif aged and strict:
        status = 'stale'
    else:
        status = 'aged' if aged else 'current'
    return {'fixture': fx['example'], 'status': status, 'proof_module': module, 'problems': problems,
            'revision': {'recorded': head, 'available': revision_available(root, head),
                         'needed': False, 'tracked_dirty': (plan.get('revision') or {}).get('tracked_dirty')},
            'closure': {'modules': sorted(closure), 'external_modules': external, 'files': len(closure) + len(ENVIRONMENT),
                        'receipt_sources': len(recorded), 'changed_local': stale_local, 'changed_shared': aged},
            'theorems': chained['source_scan'], 'audited_declarations': len(names), 'compiled_audit': chained['compiled_audit']['status']}


def rerun(fx, a):
    """Rerun the guarded proof receipt on the current tree; its compiled audit must equal the committed one."""
    work = Path(os.path.abspath(a.workdir))
    am.demand(not work.exists(), 'WORKDIR must not exist: ' + str(work))
    work.mkdir(parents=True)
    attempt = work / 'attempt'
    fresh = fresh_receipt(fx, attempt)
    committed = am.audit_theorems(ROOT, {'proofs': [fx['proofs']]}, fx['path'] / 'receipt/audit.json')
    return fresh, committed


# ---------------------------------------------------------------- regenerate (heavy)

def guarded(workdir, name, command, timeout, lock_wait):
    lock = os.environ.get('AIR2LEAN_BUILD_LOCK', str(Path.home() / '.cache/air2lean/build.lock'))
    cmd = [sys.executable, str(ROOT / 'scripts/build-guard.py'), '--cwd', str(ROOT), '--lock', lock,
           '--lock-wait', str(lock_wait), '--report', str(workdir / (name + '.guard.json')),
           '--log', str(workdir / (name + '.guard.log')), '--timeout', str(timeout), '--rss-mib', '16384',
           '--phase', 'build', '--', *map(str, command)]
    subprocess.run(cmd, check=True)


def lean_toolchain():
    return Path.home() / '.elan/toolchains' / (ROOT / 'lean-toolchain').read_text().strip().replace('/', '--').replace(':', '---')


def fresh_receipt(fx, attempt):
    """A guarded, sealed proof receipt over the tracked tree for the fixture's proof module."""
    toolchain = lean_toolchain()
    done = subprocess.run(['bash', str(ROOT / 'tests/roadmap/proof-receipts/check.sh'), str(attempt),
                           str(toolchain), fx['label'], fx['proof_module']])
    am.demand(done.returncode == 0, 'fresh proof receipt failed')
    am.receipt.verify(attempt)
    return am.audit_theorems(ROOT, {'proofs': [fx['proofs']]}, attempt / 'audit.json')


def record_manifest(fx, out, air_dir, receipt, binary, stock):
    """`artifact-manifest.py manifest` of the fixture's example: the fixture source, the given AIR,
    receipt and stock-Zig native build (fixture target, ReleaseSafe, baseline)."""
    code = am.manifest_main(['manifest', str(out), '--example', fx['example'], '--zig-version', VERSION,
                             '--source', fx['dir'] + '/src', '--air-dir', str(air_dir),
                             '--generated', fx['gen'], '--proof', fx['proofs'],
                             '--receipt', str(receipt), '--native-binary', str(binary),
                             '--native-compiler', str(Path(stock).absolute()),
                             '--native-compiler-version', VERSION, '--native-target', fx['target'],
                             '--native-mode', 'ReleaseSafe', '--native-cpu', 'baseline'])
    am.demand(code == 0, 'could not record the manifest ' + str(out))


def regenerate(fx, a):
    work = Path(os.path.abspath(a.workdir))
    am.demand(not work.exists(), 'WORKDIR must not exist: ' + str(work))
    work.mkdir(parents=True)
    zig_air, stock = Path(a.zig_air).absolute(), Path(a.stock_zig).absolute()
    air, native, attempt = work / 'air', work / 'native', work / 'attempt'
    air.mkdir()
    native.mkdir()
    # 1/4 build the translator, export fresh AIR, translate and build the native binary with stock Zig.
    shell = ('set -euo pipefail; cd "$1"; export PATH="$7/bin:$PATH"; lake build air2lean; '
             'ZIG_AIR_JSON_DIR="$4" ZIG_AIR_JSON_FILTER=%s "$3" build-obj -fno-emit-bin -OReleaseSafe '
             '-fno-error-tracing -target %s -mcpu=baseline %s; '
             '.lake/build/bin/air2lean "$4" -o "$2/Gen.lean" --namespace %s --prefix %s; '
             '"$5" build-exe -OReleaseSafe -fstrip -target %s -mcpu=baseline -femit-bin="$6/%s" %s'
             % (fx['filter'], fx['target'], fx['source'], fx['namespace'], fx['prefix'], fx['target'],
                fx['binary'], fx['source']))
    guarded(work, 'pipeline', ['bash', '-c', shell, 'pipeline', ROOT, work, zig_air, air, stock, native, lean_toolchain()],
            a.timeout, a.lock_wait)
    problems = []

    def same(label, fresh, committed):
        if fresh.read_bytes() != committed.read_bytes():
            problems.append('%s differs from the committed fixture: %s' % (label, committed))
    committed_air = sorted((fx['path'] / 'air').glob('*.json'))
    if sorted(p.name for p in air.glob('*.json')) != [p.name for p in committed_air]:
        problems.append('fresh AIR file set differs from the committed fixture')
    for path in committed_air:
        if (air / path.name).exists():
            same('AIR ' + path.name, air / path.name, path)
    same('Gen.lean', work / 'Gen.lean', ROOT / fx['gen'])
    # 2/4 guarded proof receipt over the tracked tree.
    fresh_audit = fresh_receipt(fx, attempt)
    # --refresh (a new fixture, or an intentional proof change): the fresh manifest is only
    # self-checked, and `install` + `record` replace the committed manifest and pins.
    refresh = a.refresh
    committed = None if refresh else json.loads((fx['path'] / 'manifest.json').read_text())
    pins = None if refresh else json.loads((fx['path'] / 'pins.json').read_text())
    if committed and fresh_audit != committed['links']['theorems']['value']['compiled_audit']:
        problems.append('fresh compiled theorem audit differs from the committed manifest')
    # 3/4 fresh manifest chaining the fresh export, receipt and native binary.
    manifest_path = work / 'manifest.json'
    record_manifest(fx, manifest_path, air, attempt, native / fx['binary'], stock)
    fresh = json.loads(manifest_path.read_text())
    if committed:
        if fresh['links']['native']['value']['compiler_sha256'] == committed['links']['native']['value']['compiler_sha256']:
            if fresh['links']['native']['value']['binary_sha256'] != pins['native_binary_sha256']:
                problems.append('native binary is not reproducible with the recorded stock compiler')
        for name in ('source', 'profile'):
            if fresh['links'][name]['sha256'] != committed['links'][name]['sha256']:
                problems.append('fresh %s link differs from the committed manifest' % name)
    # 4/4 strict check of the fresh manifest, including the supplied binary and compiler.
    pinned = pins or {'profile_sha256': fresh['links']['profile']['value']['profile_sha256'],
                      'source_sha256': fresh['links']['source']['sha256']}
    expect = ['zig_version=' + VERSION, 'profile=' + pinned['profile_sha256'], 'source=' + pinned['source_sha256']]
    report = am.check_manifest(ROOT, manifest_path, expect, a.allow_dirty, False, native / fx['binary'], stock, True)
    problems += report['problems']
    status = 'current' if report['status'] == 'current' and not problems else 'stale'
    print(json.dumps({'fixture': fx['example'], 'status': status, 'problems': problems,
                      'stale_links': report['stale_links'],
                      'manifest': str(manifest_path), 'manifest_sha256': fresh['manifest_sha256']}, indent=2))
    return 0 if status == 'current' else 2


RECEIPT_COPY = ('receipt.json', 'plan.json', 'audit.json')


def redact(value, prefixes):
    """Replace host-local absolute paths in every JSON string: known prefixes by placeholders, any
    other absolute path by `<host>/<basename>`. Keys and non-path strings are unchanged."""
    if isinstance(value, dict):
        return {k: redact(v, prefixes) for k, v in value.items()}
    if isinstance(value, list):
        return [redact(v, prefixes) for v in value]
    if isinstance(value, str) and len(value) > 1 and value.startswith('/') and not any(c.isspace() for c in value):
        for prefix, placeholder in prefixes:
            if value == prefix or value.startswith(prefix + '/'):
                return placeholder + value[len(prefix):]
        return '<host>/' + Path(value).name
    return value


def install(fx, a):
    """Copy WORKDIR's verified fresh receipt into the fixture, path-redacted (see docs)."""
    work = Path(os.path.abspath(a.workdir))
    attempt = am.physical(work / 'attempt')
    am.receipt.verify(attempt)
    prefixes = [(str(attempt), '<attempt>'), (str(am.physical(ROOT)), '<repo>'), (str(ROOT), '<repo>'),
                (str(am.physical(Path.home())), '~'), (str(Path.home()), '~')]
    target = fx['path'] / 'receipt'
    target.mkdir(exist_ok=True)
    # Read and redact everything first, so a failure leaves the committed fixture untouched.
    texts = {name: json.dumps(redact(am.load(attempt / name), prefixes), sort_keys=True, separators=(',', ':')) + '\n'
             for name in RECEIPT_COPY}
    leaked = host_paths([json.loads(t) for t in texts.values()], [])
    am.demand(not leaked, 'redaction left host-local paths: %s' % leaked[:3])
    for path in target.iterdir():
        am.demand(path.is_file() and not path.is_symlink(), 'unexpected entry in the receipt fixture: ' + str(path))
    for name, text in texts.items():
        staged = target / (name + '.partial')
        staged.write_text(text)
        os.replace(staged, target / name)
    for path in target.iterdir():
        if path.name not in texts:
            path.unlink()
    print('installed a path-redacted copy of %s into %s' % (attempt, target.relative_to(ROOT)))
    return 0


def record(fx, a):
    """Record the fixture's manifest.json from the (clean) tree and refresh its pins.json."""
    work = Path(os.path.abspath(a.workdir))
    stock = shutil.which(a.stock_zig) if os.sep not in a.stock_zig else a.stock_zig
    am.demand(stock is not None and Path(stock).is_file(), 'stock Zig not found: ' + a.stock_zig)
    # Recorded beside the run, then moved over the fixture: a failure keeps the committed manifest.
    staged = work / 'fixture-manifest.json'
    staged.unlink(missing_ok=True)
    record_manifest(fx, staged, fx['dir'] + '/air', fx['dir'] + '/receipt', work / 'native' / fx['binary'], stock)
    path = fx['path'] / 'manifest.json'
    os.replace(staged, path)
    manifest = am.load(path)
    links = manifest['links']
    pins = {'note': 'Reviewer pins for %s/manifest.json (scripts/provenance-evidence.py). '
                    'Update only with a regenerated, reviewed manifest.' % fx['dir'],
            'zig_version': links['profile']['value']['zig_version'],
            'profile_sha256': links['profile']['value']['profile_sha256'],
            'source_sha256': links['source']['sha256'], 'native_sha256': links['native']['sha256'],
            'native_binary_sha256': links['native']['value']['binary_sha256'],
            'manifest_sha256': manifest['manifest_sha256']}
    (fx['path'] / 'pins.json').write_text(json.dumps(pins, indent=2, sort_keys=True) + '\n')
    print('recorded %s and pins.json' % path.relative_to(ROOT))
    return 0


def main(argv):
    parser = argparse.ArgumentParser(prog='provenance-evidence.py', description=__doc__.split('\n\n')[0])
    parser.add_argument('--fixture', choices=(*FIXTURES, 'all'), default='provenance',
                        help='which committed fixture (all: check/replay only; default provenance)')
    sub = parser.add_subparsers(dest='action', required=True)
    c = sub.add_parser('check', help='offline recheck of the committed fixture')
    c.add_argument('--strict', action='store_true', help='also fail on drift of repository-wide links')
    c.add_argument('--native-binary', type=Path)
    c.add_argument('--native-compiler', type=Path)
    y = sub.add_parser('replay', help="offline replay of the committed receipt against the tree (no revision needed)")
    y.add_argument('--strict', action='store_true', help='also fail on drift of shared Lean/toolchain closure files')
    y.add_argument('--rerun', metavar='WORKDIR', help='also rerun the guarded proof receipt and compare audits (needs Lean, lock)')
    y.add_argument('--timeout', type=int, default=7200)
    g = sub.add_parser('regenerate', help='rerun the pipeline and compare with the fixture (needs Zig, Lean, lock)')
    g.add_argument('workdir')
    g.add_argument('--zig-air', default=os.environ.get('AIR2LEAN_ZIG_AIR', str(ROOT / 'zig-air-0.16.0/bin/zig')))
    g.add_argument('--stock-zig', default=os.environ.get('AIR2LEAN_ZIG', 'zig'))
    g.add_argument('--timeout', type=int, default=7200)
    g.add_argument('--lock-wait', type=int, default=14400)
    g.add_argument('--allow-dirty', action='store_true')
    g.add_argument('--refresh', action='store_true',
                   help='do not compare the fresh theorem audit, native binary and manifest with the committed ones')
    i = sub.add_parser('install', help="copy WORKDIR's verified receipt into the fixture, path-redacted")
    i.add_argument('workdir')
    r = sub.add_parser('record', help='record the fixture manifest from the clean tree and refresh pins.json')
    r.add_argument('workdir')
    r.add_argument('--stock-zig', default=os.environ.get('AIR2LEAN_ZIG', 'zig'))
    a = parser.parse_args(argv)
    names = list(FIXTURES) if a.fixture == 'all' else [a.fixture]
    if a.action in ('regenerate', 'install', 'record') and len(names) != 1:
        parser.error(a.action + ' needs one --fixture')
    try:
        if a.action == 'regenerate':
            return regenerate(fixture(names[0]), a)
        if a.action == 'install':
            return install(fixture(names[0]), a)
        if a.action == 'record':
            return record(fixture(names[0]), a)
        if a.action == 'replay':
            return replay_main(names, a)
        reports = {n: check(fixture(n), a.strict, a.native_binary, a.native_compiler) for n in names}
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print('provenance evidence unavailable: ' + str(error), file=sys.stderr)
        return 2
    return emit(reports, lambda r: 'provenance evidence %s: stale %s; aged %s; problems %s'
                % (r['status'], r['local_stale_links'], r['aged_links'], r['problems']), names)


def emit(reports, summary, names):
    """One report prints bare (the historical shape); several print as {fixture: report}."""
    print(json.dumps(reports[names[0]] if len(names) == 1 else reports, indent=2, sort_keys=True))
    for name, report in reports.items():
        if report['status'] != 'current':
            print(name + ': ' + summary(report), file=sys.stderr)
    return 0 if all(r['status'] == 'current' for r in reports.values()) else 2


def replay_main(names, a):
    reports = {n: replay(fixture(n), a.strict) for n in names}
    code = 0
    if a.rerun:
        am.demand(len(names) == 1, '--rerun needs one --fixture')
        fx = fixture(names[0])
        report = reports[names[0]]
        am.demand(report['status'] != 'stale', 'refusing to rerun: the receipt is stale for this tree')
        fresh, committed = rerun(fx, a)
        report['rerun'] = {'status': 'same' if fresh == committed else 'different', 'fresh': fresh, 'committed': committed}
        if fresh != committed:
            report['status'] = 'stale'
            report['problems'].append('a fresh proof receipt on the current tree has a different compiled theorem audit')
    print(json.dumps(reports[names[0]] if len(names) == 1 else reports, indent=2, sort_keys=True))
    for name, report in reports.items():
        if report['status'] != 'current':
            print('%s: provenance receipt replay %s: local drift %s; shared drift %s; problems %s'
                  % (name, report['status'], report['closure']['changed_local'], report['closure']['changed_shared'],
                     report['problems']), file=sys.stderr)
        code = max(code, 0 if report['status'] in ('current', 'aged') else 2)
    return code


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
