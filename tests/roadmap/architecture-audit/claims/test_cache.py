#!/usr/bin/env python3
"""build.sh gives the same fixtures and reports with and without the shared artifact cache.

The claim fixtures are the library AuditClaims of the proof-fixture package
(tests/roadmap/lakefile.toml), so Lake's artifact cache (scripts/cas.py run) serves them. This
test runs three steps:
- build.sh with AIR2LEAN_CAS_DIR unset, with Lake compiling every fixture;
- a fill of a new temporary cache (`lake build AuditClaims`);
- build.sh from that cache, with every fixture restored and none compiled. Each run starts
  without the library's build outputs (the package's other libraries keep theirs).
Every fixture .olean, every assurance report and the exposure extraction (snapshot.py) must be
byte-identical between the two build.sh runs. The one exception is the Shadow audits' error
reports, compared up to the name of the extractor's temporary driver file, which differs from
run to run with or without the cache. Needs what check.sh needs.
"""
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REPORTS = ROOT / '.lake/architecture-audit/claims'
PACKAGE = ROOT / 'tests/roadmap'
BUILD = PACKAGE / '.lake/build'
FIXTURES = 7
DRIVER = re.compile(rb'(?<=/\.lake/assurance/)tmp[A-Za-z0-9_]+\.lean')
BUILT = re.compile(r'Built AuditClaims\.')
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('snapshot', HERE / 'snapshot.py')
snapshot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(snapshot)


def run(argv, store, cwd=ROOT):
    """argv without the library's build outputs, with the cache at `store` (None: off); returns
    how many fixtures Lake compiled."""
    for outputs in ('lib/lean/AuditClaims', 'ir/AuditClaims'):
        shutil.rmtree(BUILD / outputs, ignore_errors=True)
    env = {k: v for k, v in os.environ.items() if k != 'AIR2LEAN_CAS_DIR' and not k.startswith('LAKE_')}
    if store:
        env['AIR2LEAN_CAS_DIR'] = str(store)
    done = subprocess.run(argv, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    sys.stdout.write(done.stdout)
    if done.returncode:
        raise SystemExit('%s exited %d' % (' '.join(map(str, argv[:4])), done.returncode))
    return len(BUILT.findall(done.stdout))


def outputs():
    files = [*BUILD.glob('lib/lean/AuditClaims/*.olean'), *REPORTS.glob('*.json')]
    return {p.name: DRIVER.sub(b'<driver>.lean', p.read_bytes()) for p in sorted(files)}


def main():
    build = ['bash', str(HERE / 'build.sh')]
    fill = [sys.executable, '-B', str(ROOT / 'scripts/cas.py'), 'run', '--', 'lake', 'build', 'AuditClaims']
    # The extractor records whether its tool olean was reused; a first audit in a new checkout
    # has no record yet. Make both build.sh runs see the same state.
    import assumptions
    with assumptions.prepared_tool():
        pass
    with tempfile.TemporaryDirectory(prefix='air2lean-audit-cache.') as store:
        compiled = {'uncached build.sh': run(build, None)}
        plain, extraction = outputs(), json.dumps(snapshot.extract())
        compiled['filling the cache'] = run(fill, store, cwd=PACKAGE)
        compiled['build.sh from the cache'] = run(build, store)
        cached = outputs()
    failures = ['%s: Lake compiled %d fixtures, expected %d' % (name, count, expected)
                for (name, count), expected in zip(compiled.items(), (FIXTURES, FIXTURES, 0)) if count != expected]
    changed = sorted(f for f in cached.keys() | plain.keys() if cached.get(f) != plain.get(f))
    if changed or len(plain) != FIXTURES + 5:  # the oleans, 4 reports and the replay cache
        failures.append('build.sh from the cache differs from the uncached run: ' + ', '.join(changed or plain))
    if json.dumps(snapshot.extract()) != extraction:
        failures.append('build.sh from the cache: the exposure extraction differs from the uncached run')
    for failure in failures:
        print('FAIL ' + failure, file=sys.stderr)
    if not failures:
        print('audit cache: %d outputs byte-identical with and without the cache; the cached run compiled nothing'
              % len(plain))
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
