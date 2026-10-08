#!/usr/bin/env python3
"""C04 semantic mutants of ZigLean/Conc/TimedBudget.lean, killed by its own soundness proofs.

Each mutant changes one decision of the solver budget path in a temporary copy of the module
and elaborates the copy against the built, unmutated dependencies (`lake env lean`; nothing
in the repository is written). A mutant is killed only when Lean exits 1 and every error is
located inside one of the named soundness theorems of the copy: a parse error, an unknown
name, an error in a definition or an error anywhere else is not a kill. Needs the
dependencies of ZigLean.Conc.TimedBudget built (`lake build ZigLean.Conc.TimedBudget`).
"""
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
MODULE = 'ZigLean/Conc/TimedBudget.lean'
HEADER = re.compile(r'^(.+?\.lean):(\d+):(\d+): (error|warning)(?:\([^)]*\))?: (.*)$')
DECL = re.compile(r'^(?:private |protected |noncomputable )*(theorem|def|abbrev|inductive|structure|instance)\s+(\S+)')
NOT_A_KILL = re.compile(r'unexpected token|unknown (?:identifier|constant|namespace)|expected term|'
                        r'unsolved universe|Killed|out of memory', re.IGNORECASE)

LOOP_DECIDE = ('    if deadline.nanoseconds ≤ now.nanoseconds then .done (.expired s now)\n'
               '    else match advance s with\n'
               '      | .ok answer => .done (.solved answer now)\n'
               '      | .error s\' => loop advance deadline n s\'\n')
PAUSED_WAIT = ('      | .error s\' => .wait word 0 (.deadline deadline) fun _ => '
               'pausedLoop advance deadline word n s\'\n')

# name -> (anchor, replacement, theorems whose proof must fail)
MUTANTS = {
    # Deadline boundary: now = deadline must expire; the mutant still solves at the boundary.
    'boundary-solves-at-deadline': (
        LOOP_DECIDE, LOOP_DECIDE.replace('deadline.nanoseconds ≤ now', 'deadline.nanoseconds < now'),
        {'loopInv_step', 'loop_sound', 'loop_decides_from', 'loop_decides'}),
    # Wake/timeout return: the paused loop must recheck the clock; the mutant reports expiry
    # from the stale pre-wait observation (before the deadline).
    'paused-expires-without-recheck': (
        PAUSED_WAIT, PAUSED_WAIT.replace('fun _ => pausedLoop advance deadline word n s\'',
                                         'fun _ => .done (.expired s\' now)'),
        {'pausedInv_step', 'pausedLoop_sound'}),
}


def mutated(source, name):
    anchor, replacement, _ = MUTANTS[name]
    if source.count(anchor) != 1:
        raise AssertionError(f'{name}: mutation anchor must occur exactly once')
    return source.replace(anchor, replacement)


def enclosing(lines, line_no):
    """The declaration (kind, name) that contains 1-based line `line_no`."""
    for text in reversed(lines[:line_no]):
        match = DECL.match(text)
        if match:
            return match.group(1), match.group(2)
    return None, None


def killed_by(source, output, killers):
    """The theorems that reject the mutant, or None when the failure is not a proof kill."""
    lines = source.splitlines()
    found = set()
    for line in output.splitlines():
        header = HEADER.match(line)
        if header is None:
            if re.search(r'(?:^|\s)error(?:\([^)]*\))?:', line) or NOT_A_KILL.search(line):
                return None
            continue
        path, row, _, severity, text = header.groups()
        if severity != 'error':
            continue
        if not path.endswith('TimedBudget.lean') or NOT_A_KILL.search(text):
            return None
        kind, decl = enclosing(lines, int(row))
        if kind != 'theorem' or decl not in killers:
            return None
        found.add(decl)
    return found or None


def main():
    source = (ROOT / MODULE).read_text()
    survivors = 0
    for name, (_, _, killers) in MUTANTS.items():
        text = mutated(source, name)
        with tempfile.TemporaryDirectory(prefix='deadline-cases-mutant-') as temp:
            path = Path(temp) / 'TimedBudget.lean'
            path.write_text(text)
            result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                                    capture_output=True, text=True, timeout=900)
        output = result.stdout + result.stderr
        found = killed_by(text, output, killers) if result.returncode == 1 else None
        if found:
            print(f'{name}: killed by {", ".join(sorted(found))}')
        else:
            survivors += 1
            print(f'SURVIVED {name} (exit {result.returncode}):\n{output[-4000:]}', file=sys.stderr)
    return 1 if survivors else 0


if __name__ == '__main__':
    sys.exit(main())
