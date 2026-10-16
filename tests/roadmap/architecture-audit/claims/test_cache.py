#!/usr/bin/env python3
"""build.sh gives the same fixtures and reports with and without the shared cache.

Runs build.sh with AIR2LEAN_CAS_DIR unset, fills a new temporary store with the fixtures
(scripts/lean_cache.py compile: every one compiled, each byte-identical to the uncached run), then
runs build.sh from that store (every fixture copied, none compiled). Every compiled fixture, every
assurance report and the exposure extraction (snapshot.py) must be byte-identical across the two
build.sh runs; the Shadow audits' error reports up to the name of the extractor's temporary driver
file, which differs from run to run with or without the cache. Needs what check.sh needs.
"""
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = ROOT / '.lake/architecture-audit/claims'
SRC = HERE.relative_to(ROOT)
FIXTURES = [SRC / 'AuditClaims' / (m + '.lean')
            for m in ('Gen', 'Vacuous', 'Shadow', 'Unchecked', 'AsmTotal', 'ShadowWithin', 'Universal')]
DRIVER = re.compile(rb'(?<=/\.lake/assurance/)tmp[A-Za-z0-9_]+\.lean')
SUMMARY = re.compile(r'lean_cache: (\d+) modules, (\d+) from the cache')
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('snapshot', HERE / 'snapshot.py')
snapshot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(snapshot)


def run(argv, store, **env):
    """argv with the cache at `store` (None: off); returns (modules, modules from the cache)."""
    env = {**{k: v for k, v in os.environ.items() if k != 'AIR2LEAN_CAS_DIR'}, **env}
    if store:
        env['AIR2LEAN_CAS_DIR'] = str(store)
    done = subprocess.run(argv, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    sys.stdout.write(done.stdout)
    served = SUMMARY.search(done.stderr)
    if done.returncode or not served:
        raise SystemExit('%s exited %d:\n%s' % (' '.join(argv[:4]), done.returncode, done.stderr[-4000:]))
    return int(served[1]), int(served[2])


def outputs():
    return {p.relative_to(OUT).as_posix(): DRIVER.sub(b'<driver>.lean', p.read_bytes())
            for p in sorted(OUT.rglob('*')) if p.is_file() and p.suffix in ('.olean', '.json')}


def main():
    build = ['bash', str(HERE / 'build.sh')]
    compile_ = [sys.executable, '-B', 'scripts/lean_cache.py', 'compile', '--root', str(SRC),
                '--out', str(OUT / 'lib'), *map(str, FIXTURES)]
    # The extractor records whether its tool olean was reused; a first audit in a new checkout
    # has no record yet. Make both build.sh runs see the same state.
    if not (ROOT / '.lake/assurance/tool-trace.json').is_file():
        import assumptions
        assumptions.prepare_tool()
    failures = []
    with tempfile.TemporaryDirectory(prefix='air2lean-audit-cache.') as store:
        served = {'uncached build.sh': run(build, None)}
        plain, extraction = outputs(), json.dumps(snapshot.extract())
        served['filling the store'] = run(compile_, store, LEAN_PATH=str(OUT / 'lib'))
        changed = sorted(f for f, data in outputs().items() if f.endswith('.olean') and data != plain[f])
        if changed:
            failures.append('a fixture compiled with the store differs from the uncached run: ' + ', '.join(changed))
        served['build.sh from the store'] = run(build, store)
        cached = outputs()
    expected = {'uncached build.sh': 0, 'filling the store': 0, 'build.sh from the store': len(FIXTURES)}
    for name, (modules, hits) in served.items():
        if (modules, hits) != (len(FIXTURES), expected[name]):
            failures.append('%s: %d of %d fixtures from the cache, expected %d' % (name, hits, modules, expected[name]))
    changed = sorted(f for f in cached.keys() | plain.keys() if cached.get(f) != plain.get(f))
    if changed:
        failures.append('build.sh from the store differs from the uncached run: ' + ', '.join(changed))
    if json.dumps(snapshot.extract()) != extraction:
        failures.append('build.sh from the store: the exposure extraction differs from the uncached run')
    for failure in failures:
        print('FAIL ' + failure, file=sys.stderr)
    if not failures:
        print('audit cache: %d outputs byte-identical with and without the cache; the cached run compiled nothing'
              % len(plain))
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
