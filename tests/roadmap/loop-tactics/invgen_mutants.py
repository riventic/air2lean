#!/usr/bin/env python3
"""Negative controls of the generated loop invariants (P09, docs/invariant-synthesis.md).

    python3 -B tests/roadmap/loop-tactics/invgen_mutants.py FIXTURE NAMESPACE WORK

The generator is untrusted: only the kernel check of the proof accepts its output. Each seeded
mutant in FIXTURE/mutants.json (`old` replaced by `new` in the committed NAMESPACE/Inv.lean, where
`old` occurs exactly once) must still elaborate, and FIXTURE/Proof.lean must then fail with an
error inside one of the theorems listed in `in` (from its `theorem` line to the next declaration),
so that an import error or a failure elsewhere does not count. WORK/olean holds the compiled
NAMESPACE/Gen.olean and LEAN_PATH reaches the library. AIR2LEAN_MUTANT_JOBS mutants run at a
time (default 1: each one elaborates the whole proof).
"""
import json
import os
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


def spans(proof):
    """Each theorem's lines in `proof`, 1-based and half-open: from its `theorem` line up to the
    next unindented line. A name declared twice is an error (a mutant names one theorem)."""
    lines = proof.read_text().splitlines()
    out = {}
    for i, line in enumerate(lines):
        m = re.match(r'theorem (\S+)', line)
        if m:
            if m.group(1) in out:
                sys.exit(f'{proof}: two theorems named {m.group(1)}')
            end = next((j for j in range(i + 1, len(lines)) if lines[j][:1] not in ('', ' ')), len(lines))
            out[m.group(1)] = (i + 1, end + 1)
    return out


def run(fixture, ns, work, mutant, theorems):
    """Why `mutant` was not rejected inside its theorems, or None."""
    name = mutant['name']
    mdir = work / f'mutant-{name}'
    (mdir / 'olean' / ns).mkdir(parents=True)
    (mdir / 'src' / ns).mkdir(parents=True)
    shutil.copy(work / 'olean' / ns / 'Gen.olean', mdir / 'olean' / ns)
    text = (fixture / ns / 'Inv.lean').read_text()
    if text.count(mutant['old']) != 1:
        return f"{mutant['old']!r} does not occur exactly once in the generated file"
    (mdir / 'src' / ns / 'Inv.lean').write_text(text.replace(mutant['old'], mutant['new']))
    env = dict(os.environ, LEAN_PATH=f"{mdir / 'olean'}:{os.environ.get('LEAN_PATH', '')}")
    subprocess.run(['lake', 'env', 'lean', '-R', str(mdir / 'src'), '-o', str(mdir / 'olean' / ns / 'Inv.olean'),
                    str(mdir / 'src' / ns / 'Inv.lean')], env=env, check=True)
    proof = subprocess.run(['lake', 'env', 'lean', '-R', str(fixture), str(fixture / 'Proof.lean')],
                           env=env, capture_output=True, text=True)
    if proof.returncode == 0:
        return 'accepted'
    lines = [int(n) for n in re.findall(r'Proof\.lean:(\d+):\d+: error', proof.stdout + proof.stderr)]
    if not any(a <= n < b for t in mutant['in'] for a, b in [theorems[t]] for n in lines):
        return f"no error in {', '.join(mutant['in'])}: {(proof.stdout + proof.stderr)[-600:]}"
    return None


def main():
    fixture, ns, work = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3])
    if not os.environ.get('LEAN_PATH'):
        sys.exit('LEAN_PATH must reach WORK/olean and the library (invgen-fixture.sh sets it)')
    mutants = json.loads((fixture / 'mutants.json').read_text())
    names = [m['name'] for m in mutants]
    if not mutants or len(set(names)) != len(names):
        sys.exit(f'{fixture}/mutants.json: no mutants, or two with one name')
    theorems = spans(fixture / 'Proof.lean')
    missing = [t for m in mutants for t in m['in'] if t not in theorems]
    if missing:
        sys.exit(f"Proof.lean has no theorem {', '.join(missing)}")
    with ThreadPoolExecutor(max_workers=int(os.environ.get('AIR2LEAN_MUTANT_JOBS', '1'))) as pool:
        results = list(pool.map(lambda m: run(fixture, ns, work, m, theorems), mutants))
    failed = [f"mutant {m['name']}: {why}" for m, why in zip(mutants, results) if why]
    for m, why in zip(mutants, results):
        if not why:
            print(f"mutant {m['name']} of the generated invariant rejected")
    if failed:
        sys.exit('\n'.join(failed))


if __name__ == '__main__':
    main()
