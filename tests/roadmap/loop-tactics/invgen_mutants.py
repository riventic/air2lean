#!/usr/bin/env python3
"""Negative controls of the generated loop invariants (P09, docs/invariant-synthesis.md).

    python3 -B tests/roadmap/loop-tactics/invgen_mutants.py FIXTURE NAMESPACE WORK

The generator is untrusted: only the kernel check of the proof accepts its output. Each seeded
mutant in FIXTURE/mutants.json (`old` replaced by `new` in the committed NAMESPACE/Inv.lean, where
`old` occurs exactly once; with `def`, exactly once in that definition, and the mutant changes
only it: a loop's plain-mode and credit-mode invariants repeat their facts) must still elaborate, and FIXTURE/Proof.lean must then fail with an
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

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
from mutation_kill_log import killed as log_kill  # noqa: E402


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


def scope(text, name):
    """The definition `name` in the generated file, as (start, end): from its `def` up to and
    including the newline before the next blank line. None unless it is defined exactly once."""
    head = f'def {name} '
    start = text.find(head)
    if start < 0 or text.find(head, start + 1) >= 0:
        return None
    end = text.find('\n\n', start)
    return start, len(text) if end < 0 else end + 1


def mutated(text, mutant):
    """`(the generated file `text` with `mutant` applied, None)`, or `(None, why it does not
    apply)`: `old` must occur exactly once (in the definition `def`, if the mutant names one)."""
    lo, hi, where = 0, len(text), 'the generated file'
    if 'def' in mutant:
        span = scope(text, mutant['def'])
        if span is None:
            return None, f"the generated file does not have exactly one definition {mutant['def']}"
        lo, hi, where = *span, mutant['def']
    if text.count(mutant['old'], lo, hi) != 1:
        return None, f"{mutant['old']!r} does not occur exactly once in {where}"
    return text[:lo] + text[lo:hi].replace(mutant['old'], mutant['new']) + text[hi:], None


def errors_in(output, file, names, theorems):
    """The theorems of `names` (spans `theorems`) inside which Lean's `output` reports an error of
    the file named `file`."""
    lines = [int(n) for n in re.findall(re.escape(file) + r':(\d+):\d+: error', output)]
    return [t for t in names if any(theorems[t][0] <= n < theorems[t][1] for n in lines)]


def survived(returncode, output, file, mutant, theorems):
    """Why Lean's run on the proof `file` did not reject `mutant` inside its theorems, or None."""
    if returncode == 0:
        return 'accepted'
    if not errors_in(output, file, mutant['in'], theorems):
        return f"no error in {', '.join(mutant['in'])}: {output[-600:]}"
    return None


def run(fixture, ns, work, mutant, theorems):
    """Why `mutant` was not rejected inside its theorems, or None."""
    name = mutant['name']
    mdir = work / f'mutant-{name}'
    (mdir / 'olean' / ns).mkdir(parents=True)
    (mdir / 'src' / ns).mkdir(parents=True)
    shutil.copy(work / 'olean' / ns / 'Gen.olean', mdir / 'olean' / ns)
    text, why = mutated((fixture / ns / 'Inv.lean').read_text(), mutant)
    if why:
        return why
    (mdir / 'src' / ns / 'Inv.lean').write_text(text)
    env = dict(os.environ, LEAN_PATH=f"{mdir / 'olean'}:{os.environ.get('LEAN_PATH', '')}")
    subprocess.run(['lake', 'env', 'lean', '-R', str(mdir / 'src'), '-o', str(mdir / 'olean' / ns / 'Inv.olean'),
                    str(mdir / 'src' / ns / 'Inv.lean')], env=env, check=True)
    proof = subprocess.run(['lake', 'env', 'lean', '-R', str(fixture), str(fixture / 'Proof.lean')],
                           env=env, capture_output=True, text=True)
    return survived(proof.returncode, proof.stdout + proof.stderr, 'Proof.lean', mutant, theorems)


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
    failed = []
    for m, why in zip(mutants, results):
        if why:
            failed.append(f"mutant {m['name']}: {why}")
        else:
            print(f"mutant {m['name']} of the generated invariant rejected")
    rejected = [m['name'] for m, why in zip(mutants, results) if not why]
    # Q02: each rejected mutant is a kill by the fixture's CI check (assurance/mutation-map.json, P09).
    rel = fixture.resolve().relative_to(ROOT).as_posix()
    log_kill(f'{rel}/mutants.json', rejected, f'{rel}/check.sh')
    if failed:
        sys.exit('\n'.join(failed))


if __name__ == '__main__':
    main()
