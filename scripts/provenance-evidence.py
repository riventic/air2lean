#!/usr/bin/env python3
"""I07 provenance evidence: check the committed receipt-chained manifest, or regenerate it fresh.

`check` is offline (no Zig, Lake or Lean): it rechecks assurance/provenance/manifest.json against
the tree with the reviewer pins in assurance/provenance/pins.json. Drift in the repository-wide
links (compiler patch, translator, runtime, toolchain) is reported as `aged` and only fails with
`--strict`; every example-local link (source, AIR, profile, Gen.lean, proofs, theorem names,
receipt, native record) must be current.

`regenerate WORKDIR` reruns the pipeline on the checkout (patched 0.16.0 AIR-only export,
translate, native build with stock Zig, guarded proof receipt) and requires the fresh bytes to
match the committed fixture before it records and strictly checks a fresh manifest. It writes
only under WORKDIR. Every Zig/Lake/Lean run goes through scripts/build-guard.py and the lock in
AIR2LEAN_BUILD_LOCK. See docs/artifact-manifest.md.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).absolute().parents[1]
_spec = importlib.util.spec_from_file_location('artifact_manifest', ROOT / 'scripts/artifact-manifest.py')
am = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(am)

FIXTURE = ROOT / 'assurance/provenance'
EXAMPLE, MODULE, VERSION = 'provenance', 'Provenance', '0.16.0'
FILTER = 'provenance.add,provenance.double'
SOURCE = 'assurance/provenance/src/provenance.zig'
GLOBAL_LINKS = ('compiler_patch', 'translator', 'runtime', 'toolchain')
PROOF_MODULE = 'Proofs.Provenance.Proofs'


def check(strict, native_binary=None, native_compiler=None):
    pins = json.loads((FIXTURE / 'pins.json').read_text())
    expect = ['zig_version=' + pins['zig_version'], 'profile=' + pins['profile_sha256'],
              'source=' + pins['source_sha256'], 'native=' + pins['native_sha256']]
    manifest = json.loads((FIXTURE / 'manifest.json').read_text())
    problems = []
    if manifest.get('manifest_sha256') != pins['manifest_sha256']:
        problems.append('manifest_sha256 differs from the reviewer pin in pins.json')
    report = am.check_manifest(ROOT, FIXTURE / 'manifest.json', expect, False, False, native_binary, native_compiler,
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


def guarded(workdir, name, command, timeout, lock_wait):
    lock = os.environ.get('AIR2LEAN_BUILD_LOCK', str(Path.home() / '.cache/air2lean/build.lock'))
    cmd = [sys.executable, str(ROOT / 'scripts/build-guard.py'), '--cwd', str(ROOT), '--lock', lock,
           '--lock-wait', str(lock_wait), '--report', str(workdir / (name + '.guard.json')),
           '--log', str(workdir / (name + '.guard.log')), '--timeout', str(timeout), '--rss-mib', '16384',
           '--phase', 'build', '--', *map(str, command)]
    subprocess.run(cmd, check=True)


def record_manifest(out, air_dir, receipt, binary, stock):
    """`artifact-manifest.py manifest` of the fixture's example: the fixture source, the given AIR,
    receipt and stock-Zig native build (x86_64-linux, ReleaseSafe, baseline)."""
    code = am.manifest_main(['manifest', str(out), '--example', EXAMPLE, '--zig-version', VERSION,
                             '--source', 'assurance/provenance/src', '--air-dir', str(air_dir),
                             '--receipt', str(receipt), '--native-binary', str(binary),
                             '--native-compiler', str(Path(stock).absolute()),
                             '--native-compiler-version', VERSION, '--native-target', 'x86_64-linux',
                             '--native-mode', 'ReleaseSafe', '--native-cpu', 'baseline'])
    am.demand(code == 0, 'could not record the manifest ' + str(out))


def regenerate(a):
    work = Path(os.path.abspath(a.workdir))
    am.demand(not work.exists(), 'WORKDIR must not exist: ' + str(work))
    work.mkdir(parents=True)
    zig_air, stock = Path(a.zig_air).absolute(), Path(a.stock_zig).absolute()
    air, native, attempt = work / 'air', work / 'native', work / 'attempt'
    air.mkdir()
    native.mkdir()
    # 1/4 fresh export, translate (translate.sh also builds the translator) and checked Gen.lean.
    shell = ('set -euo pipefail; cd "$1"; '
             'bash scripts/translate.sh %s -o "$2/Gen.lean" --namespace %s --prefix %s. --filter %s --zig-air "$3"; '
             'ZIG_AIR_JSON_DIR="$4" ZIG_AIR_JSON_FILTER=%s "$3" build-obj -fno-emit-bin -OReleaseSafe '
             '-fno-error-tracing -target x86_64-linux -mcpu=baseline %s; '
             '"$5" build-exe -OReleaseSafe -fstrip -target x86_64-linux -mcpu=baseline -femit-bin="$6/provenance" %s'
             % (SOURCE, MODULE, EXAMPLE, FILTER, FILTER, SOURCE, SOURCE))
    guarded(work, 'pipeline', ['bash', '-c', shell, 'pipeline', ROOT, work, zig_air, air, stock, native],
            a.timeout, a.lock_wait)
    problems = []

    def same(label, fresh, committed):
        if fresh.read_bytes() != committed.read_bytes():
            problems.append('%s differs from the committed fixture: %s' % (label, committed))
    committed_air = sorted((FIXTURE / 'air').glob('*.json'))
    if sorted(p.name for p in air.glob('*.json')) != [p.name for p in committed_air]:
        problems.append('fresh AIR file set differs from the committed fixture')
    for path in committed_air:
        if (air / path.name).exists():
            same('AIR ' + path.name, air / path.name, path)
    same('Gen.lean', work / 'Gen.lean', ROOT / 'Proofs' / MODULE / 'Gen.lean')
    # The committed Gen.lean must be what the translator makes (header included).
    # 2/4 guarded proof receipt over the tracked tree.
    toolchain = Path.home() / '.elan/toolchains' / (ROOT / 'lean-toolchain').read_text().strip().replace('/', '--').replace(':', '---')
    receipt = subprocess.run(['bash', str(ROOT / 'tests/roadmap/proof-receipts/check.sh'), str(attempt),
                              str(toolchain), 'provenance-fresh', PROOF_MODULE])
    am.demand(receipt.returncode == 0, 'fresh proof receipt failed')
    am.receipt.verify(attempt)
    fresh_audit = am.audit_theorems(ROOT, {'proofs': ['Proofs/%s/Proofs.lean' % MODULE]}, attempt / 'audit.json')
    committed = json.loads((FIXTURE / 'manifest.json').read_text())
    if fresh_audit != committed['links']['theorems']['value']['compiled_audit']:
        problems.append('fresh compiled theorem audit differs from the committed manifest')
    # 3/4 fresh manifest chaining the fresh export, receipt and native binary.
    pins = json.loads((FIXTURE / 'pins.json').read_text())
    manifest_path = work / 'manifest.json'
    record_manifest(manifest_path, air, attempt, native / 'provenance', stock)
    fresh = json.loads(manifest_path.read_text())
    if fresh['links']['native']['value']['compiler_sha256'] == committed['links']['native']['value']['compiler_sha256']:
        if fresh['links']['native']['value']['binary_sha256'] != pins['native_binary_sha256']:
            problems.append('native binary is not reproducible with the recorded stock compiler')
    for name in ('source', 'profile'):
        if fresh['links'][name]['sha256'] != committed['links'][name]['sha256']:
            problems.append('fresh %s link differs from the committed manifest' % name)
    # 4/4 strict check of the fresh manifest, including the supplied binary and compiler.
    report = am.check_manifest(ROOT, manifest_path, ['zig_version=' + VERSION, 'profile=' + pins['profile_sha256'],
                                                     'source=' + pins['source_sha256']], a.allow_dirty, False,
                               native / 'provenance', stock, True)
    problems += report['problems']
    status = 'current' if report['status'] == 'current' and not problems else 'stale'
    print(json.dumps({'status': status, 'problems': problems, 'stale_links': report['stale_links'],
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


def install(a):
    """Copy WORKDIR's verified fresh receipt into the fixture, path-redacted (see docs)."""
    work = Path(os.path.abspath(a.workdir))
    attempt = am.physical(work / 'attempt')
    am.receipt.verify(attempt)
    prefixes = [(str(attempt), '<attempt>'), (str(am.physical(ROOT)), '<repo>'), (str(ROOT), '<repo>'),
                (str(am.physical(Path.home())), '~'), (str(Path.home()), '~')]
    target = FIXTURE / 'receipt'
    # Read and redact everything first, so a failure leaves the committed fixture untouched.
    texts = {name: json.dumps(redact(am.load(attempt / name), prefixes), sort_keys=True, separators=(',', ':')) + '\n'
             for name in RECEIPT_COPY}
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


def record(a):
    """Record assurance/provenance/manifest.json from the (clean) tree and refresh pins.json."""
    work = Path(os.path.abspath(a.workdir))
    stock = shutil.which(a.stock_zig) if os.sep not in a.stock_zig else a.stock_zig
    am.demand(stock is not None and Path(stock).is_file(), 'stock Zig not found: ' + a.stock_zig)
    # Recorded beside the run, then moved over the fixture: a failure keeps the committed manifest.
    staged = work / 'fixture-manifest.json'
    staged.unlink(missing_ok=True)
    record_manifest(staged, 'assurance/provenance/air', 'assurance/provenance/receipt', work / 'native' / 'provenance', stock)
    path = FIXTURE / 'manifest.json'
    os.replace(staged, path)
    manifest = am.load(path)
    links = manifest['links']
    pins = {'note': 'Reviewer pins for assurance/provenance/manifest.json (scripts/provenance-evidence.py). '
                    'Update only with a regenerated, reviewed manifest.',
            'zig_version': links['profile']['value']['zig_version'],
            'profile_sha256': links['profile']['value']['profile_sha256'],
            'source_sha256': links['source']['sha256'], 'native_sha256': links['native']['sha256'],
            'native_binary_sha256': links['native']['value']['binary_sha256'],
            'manifest_sha256': manifest['manifest_sha256']}
    (FIXTURE / 'pins.json').write_text(json.dumps(pins, indent=2, sort_keys=True) + '\n')
    print('recorded %s and pins.json' % path.relative_to(ROOT))
    return 0


def main(argv):
    parser = argparse.ArgumentParser(prog='provenance-evidence.py', description=__doc__.split('\n\n')[0])
    sub = parser.add_subparsers(dest='action', required=True)
    c = sub.add_parser('check', help='offline recheck of the committed fixture')
    c.add_argument('--strict', action='store_true', help='also fail on drift of repository-wide links')
    c.add_argument('--native-binary', type=Path)
    c.add_argument('--native-compiler', type=Path)
    g = sub.add_parser('regenerate', help='rerun the pipeline and compare with the fixture (needs Zig, Lean, lock)')
    g.add_argument('workdir')
    g.add_argument('--zig-air', default=os.environ.get('AIR2LEAN_ZIG_AIR', str(ROOT / 'zig-air-0.16.0/bin/zig')))
    g.add_argument('--stock-zig', default=os.environ.get('AIR2LEAN_ZIG', 'zig'))
    g.add_argument('--timeout', type=int, default=7200)
    g.add_argument('--lock-wait', type=int, default=14400)
    g.add_argument('--allow-dirty', action='store_true')
    i = sub.add_parser('install', help="copy WORKDIR's verified receipt into the fixture, path-redacted")
    i.add_argument('workdir')
    r = sub.add_parser('record', help='record the fixture manifest from the clean tree and refresh pins.json')
    r.add_argument('workdir')
    r.add_argument('--stock-zig', default=os.environ.get('AIR2LEAN_ZIG', 'zig'))
    a = parser.parse_args(argv)
    try:
        if a.action == 'regenerate':
            return regenerate(a)
        if a.action == 'install':
            return install(a)
        if a.action == 'record':
            return record(a)
        report = check(a.strict, a.native_binary, a.native_compiler)
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print('provenance evidence unavailable: ' + str(error), file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    if report['status'] != 'current':
        print('provenance evidence %s: stale %s; aged %s; problems %s'
              % (report['status'], report['local_stale_links'], report['aged_links'], report['problems']),
              file=sys.stderr)
    return 0 if report['status'] == 'current' else 2


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
