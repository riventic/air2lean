#!/usr/bin/env python3
"""The CI job matrices of .github/workflows/ci.yml, derived from compatibility.json.

  ci-matrix.py check [--root DIR]    fail when a generated matrix region is stale
  ci-matrix.py write [--root DIR]    rewrite the generated regions

Each Zig version that compatibility.json declares for x86_64-linux gets `golden` and `lean` rows in the `test`
job; the default version also gets the parts that run once (`inputs`, `native`, `audit`,
`receipt`, one row per T06 build mode) and one mutation row per line of
scripts/mutation-shards.txt. A version in RESTRICTED runs the examples that
scripts/example-selection.sh selects for it, without the diff harness. The `macos` job has one
row per version whose hosts include aarch64-macos. Every step of the test job names its part
in its `if`; the rows only say which parts exist. Offline: no Zig, Lake or Lean process.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
WORKFLOW = '.github/workflows/ci.yml'
# Its std cannot build the diff harness: translation and proofs only (README, support matrix).
RESTRICTED = {'0.14.1'}
ONCE = ('inputs', 'native', 'audit', 'receipt', 'Debug', 'ReleaseFast', 'ReleaseSmall')

_spec = importlib.util.spec_from_file_location('air2lean_support_matrix', ROOT / 'scripts/support-matrix.py')
MATRIX = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(MATRIX)


def region(job):
    return (f'          # BEGIN {job} rows (scripts/ci-matrix.py write)\n', f'          # END {job} rows\n')


def rows(root):
    compat = json.loads((root/'compatibility.json').read_text(encoding='utf-8'))
    default = compat['zig']['default']
    versions = [v['version'] for v in compat['zig']['versions'] if 'x86_64-linux' in v['hosts']]
    shards = len([l for l in (root/'scripts/mutation-shards.txt').read_text().splitlines() if l.strip()])

    def row(version, part, **shard):
        restricted, mutate = version in RESTRICTED, part == 'mutation'
        examples = ' '.join(MATRIX.default_selection(root, version)) if restricted else ''
        return {'zig': version, 'part': part, 'examples': examples,
                'full': not restricted and not mutate, 'mutate': mutate, **shard}

    ordered = [default] + [v for v in versions if v != default]
    test = [row(v, part) for v in ordered
            for part in ('golden', 'lean') + (ONCE if v == default else ())]
    test += [row(default, 'mutation', shard=n) for n in range(1, shards + 1)]
    macos = [{'zig': v['version']} for v in compat['zig']['versions'] if 'aarch64-macos' in v['hosts']]
    return {'test': test, 'macos': macos}


def render(items):
    return ''.join(f'          {"- " if i == 0 else "  "}{key}: {json.dumps(value)}\n'
                   for item in items for i, (key, value) in enumerate(item.items()))


def regenerate(root, text):
    for job, items in rows(root).items():
        begin, end = region(job)
        if text.count(begin) != 1 or text.count(end) != 1:
            raise ValueError(f'{WORKFLOW}: the {job} job needs one generated matrix region')
        start, stop = text.index(begin) + len(begin), text.index(end)
        text = text[:start] + render(items) + text[stop:]
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('mode', choices=('check', 'write'))
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    path = args.root/WORKFLOW
    text = path.read_text(encoding='utf-8')
    try:
        fresh = regenerate(args.root, text)
    except ValueError as error:
        print(f'error: {error}', file=sys.stderr)
        return 2
    if args.mode == 'write':
        if fresh != text:
            path.write_text(fresh, encoding='utf-8')
        return 0
    if fresh != text:
        print(f'error: {WORKFLOW} matrix rows are stale; run python3 scripts/ci-matrix.py write',
              file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
