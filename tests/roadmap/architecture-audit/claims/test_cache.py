#!/usr/bin/env python3
"""build.sh gives the same fixtures and reports with and without the shared cache.

Runs build.sh three times: with AIR2LEAN_CAS_DIR unset, then twice with a new temporary store
(cold, then warm). Every compiled fixture, every assurance report and the exposure extraction
(snapshot.py) must be byte-identical across the three runs (the Shadow audits' error reports up
to the name of the extractor's temporary driver file). The cold run must compile every
fixture, the warm run none (scripts/lean_cache.py). Needs what check.sh needs and takes about
three times as long as build.sh.
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
DRIVER = re.compile(rb'(?<=/\.lake/assurance/)tmp[A-Za-z0-9_]+\.lean')
sys.dont_write_bytecode = True


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


snapshot = load('snapshot', HERE / 'snapshot.py')


def build(store):
    """Run build.sh; return (fixtures served from the cache, {output: bytes}, exposure extraction)."""
    env = {k: v for k, v in os.environ.items() if k != 'AIR2LEAN_CAS_DIR'}
    if store:
        env['AIR2LEAN_CAS_DIR'] = str(store)
    done = subprocess.run(['bash', str(HERE / 'build.sh')], cwd=ROOT, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    sys.stdout.write(done.stdout)
    if done.returncode:
        raise SystemExit('build.sh exited %d:\n%s' % (done.returncode, done.stderr[-4000:]))
    served = re.search(r'lean_cache: (\d+) modules, (\d+) from the cache', done.stderr)
    if not served:
        raise SystemExit('build.sh printed no lean_cache summary:\n' + done.stderr[-4000:])
    # The Shadow audits' error reports name the extractor's temporary driver file, which differs
    # from run to run, with or without the cache.
    outputs = {p.relative_to(OUT).as_posix(): DRIVER.sub(b'<driver>.lean', p.read_bytes())
               for p in sorted(OUT.rglob('*')) if p.is_file() and p.suffix in ('.olean', '.json')}
    return (int(served[1]), int(served[2])), outputs, json.dumps(snapshot.extract(), indent=1)


def main():
    # The extractor records whether its tool olean was reused; a first audit in a new checkout
    # has no record yet. Make every run below see the same state.
    if not (ROOT / '.lake/assurance/tool-trace.json').is_file():
        load('assumptions', ROOT / 'scripts/assumptions.py').prepare_tool()
    failures = []
    with tempfile.TemporaryDirectory(prefix='air2lean-audit-cache.') as store:
        runs = {'uncached': build(None), 'cold': build(Path(store)), 'warm': build(Path(store))}
    (modules, _), plain, extraction = runs['uncached']
    expected = {'uncached': (modules, 0), 'cold': (modules, 0), 'warm': (modules, modules)}
    for name, (served, outputs, extracted) in runs.items():
        if served != expected[name]:
            failures.append('%s run: %d of %d fixtures from the cache, expected %d'
                            % (name, served[1], served[0], expected[name][1]))
        changed = sorted(f for f in outputs.keys() | plain.keys() if outputs.get(f) != plain.get(f))
        if changed:
            failures.append('%s run differs from the uncached run: %s' % (name, ', '.join(changed)))
        if extracted != extraction:
            failures.append('%s run: the exposure extraction differs from the uncached run' % name)
    for failure in failures:
        print('FAIL ' + failure, file=sys.stderr)
    if not failures:
        print('audit cache: %d outputs byte-identical with and without the cache; warm run compiled nothing'
              % len(plain))
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
