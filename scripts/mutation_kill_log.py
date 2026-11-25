#!/usr/bin/env python3
"""Report a fixture-local mutant's kill to AIR2LEAN_MUTATION_KILL_LOG (Q02, docs/mutation-map.md).

A designated mutant outside scripts/mutate.sh and tests/roadmap/mutation-map/mutants.py lives in a
fixture file (a `mutations.py`, a Lean file whose build rejects the mutant, a check script) and is
killed by the CI check that runs it. The runner that observed the kill calls `killed` (Python) or
this script (shell, or a check after the Lean build that rejects the mutant):

    python3 -B scripts/mutation_kill_log.py --check CHECK MUTANT_FILE NAME...

With AIR2LEAN_MUTATION_KILL_LOG set, each NAME becomes one `<MUTANT_FILE>#<NAME> killed check
<CHECK>` line, the format scripts/mutate.sh writes for its own mutations; unset (an ordinary CI
run), nothing is written. `scripts/mutation-map.py kills record --log LOG` then binds the kill to
the mutant file's sha256 in assurance/mutation-kills.json, and `check` fails once the file changes.
Call it only after the mutant was evaluated and rejected: a line is the run's evidence of the kill.
"""
import argparse
import os
from pathlib import Path
import sys

ENV = 'AIR2LEAN_MUTATION_KILL_LOG'
ROOT = Path(__file__).resolve().parents[1]


def key(path, name):
    """The kill-ledger name of mutant NAME of the repository file PATH."""
    return f'{path}#{name}'


def killed(path, names, check):
    """Record that the mutants NAMES of PATH were killed by the CI check CHECK (both repo-relative)."""
    for what in (path, check):
        if Path(what).is_absolute() or not (ROOT / what).is_file():
            raise ValueError(f'mutation kill log: {what!r} is not a repository file')
    target = os.environ.get(ENV)
    if not target:
        return
    with open(target, 'a', encoding='utf-8') as log:
        for name in [names] if isinstance(names, str) else names:
            if not name or any(c.isspace() or c == '#' for c in name):
                raise ValueError(f'mutation kill log: bad mutant name {name!r}')
            log.write(f'{key(path, name)} killed check {check}\n')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    parser.add_argument('--check', required=True, help='the CI check that killed the mutants')
    parser.add_argument('path', help='the repository file that defines the mutants')
    parser.add_argument('names', nargs='+')
    args = parser.parse_args(argv)
    try:
        killed(args.path, args.names, args.check)
    except ValueError as error:
        print(f'error: {error}', file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
