#!/usr/bin/env python3
"""The CI job matrices of .github/workflows/ci.yml, derived from compatibility.json.

  ci-matrix.py check [--root DIR]    fail when a generated matrix region is stale
  ci-matrix.py write [--root DIR]    rewrite the generated regions

Each Zig version that compatibility.json declares for x86_64-linux gets `golden` and `lean` rows in the `test`
job; the `zig.ci_once` version (not necessarily the default: the T06 build-mode records exist
for it) also gets the parts that run once (`inputs`, `native`, `audit`, `receipt`, one row per
T06 build mode) and one mutation row per line of scripts/mutation-shards.txt. Each row carries
`once`, true on those rows: a step qualified on the ci_once version gates on `matrix.once`.
A step whose fixtures are not yet qualified there gates on `matrix.zig == '<version>'` and runs
on a version of `zig.ci_once_pinned`, which gets the `inputs`, `native`, `audit` and `receipt`
rows too (`check` fails when a step condition names a part and version that no row has, so a
step never goes silently dead). A version in RESTRICTED runs the examples that
scripts/example-selection.sh selects for it, without the diff harness. The `macos` job has one
row per version whose hosts include aarch64-macos, the `zig-air` job (the patched compiler of
each x86_64-linux version, built once per run) one per x86_64-linux version. Every step of the test job names its part
in its `if`; the rows only say which parts exist. Offline: no Zig, Lake or Lean process.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
WORKFLOW = '.github/workflows/ci.yml'
# Its std cannot build the diff harness: translation and proofs only (README, support matrix).
RESTRICTED = {'0.14.1'}
PINNED = ('inputs', 'native', 'audit', 'receipt')
ONCE = PINNED + ('Debug', 'ReleaseFast', 'ReleaseSmall')

_spec = importlib.util.spec_from_file_location('air2lean_support_matrix', ROOT / 'scripts/support-matrix.py')
MATRIX = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(MATRIX)


def region(job):
    return (f'          # BEGIN {job} rows (scripts/ci-matrix.py write)\n', f'          # END {job} rows\n')


def rows(root):
    compat = json.loads((root/'compatibility.json').read_text(encoding='utf-8'))
    once = compat['zig']['ci_once']
    pinned = compat['zig']['ci_once_pinned']
    versions = [v['version'] for v in compat['zig']['versions'] if 'x86_64-linux' in v['hosts']]
    shards = len([l for l in (root/'scripts/mutation-shards.txt').read_text().splitlines() if l.strip()])

    def row(version, part, **shard):
        restricted, mutate = version in RESTRICTED, part == 'mutation'
        examples = ' '.join(MATRIX.default_selection(root, version)) if restricted else ''
        return {'zig': version, 'part': part, 'examples': examples,
                'full': not restricted and not mutate, 'mutate': mutate, 'once': version == once, **shard}

    ordered = [once] + [v for v in pinned if v != once] + [v for v in versions if v != once and v not in pinned]
    extra = {once: ONCE, **{v: PINNED for v in pinned if v != once}}
    test = [row(v, part) for v in ordered for part in ('golden', 'lean') + extra.get(v, ())]
    test += [row(once, 'mutation', shard=n) for n in range(1, shards + 1)]
    macos = [{'zig': v['version']} for v in compat['zig']['versions'] if 'aarch64-macos' in v['hosts']]
    return {'test': test, 'macos': macos, 'zig-air': [{'zig': v} for v in ordered]}


def dead_conditions(text, test_rows):
    """The conditions of the test job's steps that no matrix row can satisfy: a step gated on a part and
    a version (`matrix.zig == 'V'`) or on `matrix.once` that no row carries would never run."""
    job = re.search(r'^  test:\n(.*?)^  [\w-]+:\n', text, re.M | re.S)
    errors = []
    for number, line in enumerate((job.group(1) if job else '').splitlines(), 1):
        match = re.match(r"\s+if: \$\{\{ (.*) \}\}$", line)
        if not match:
            continue
        for clause in match.group(1).split('||'):
            want = {'part': set(re.findall(r"matrix\.part == '(\w+)'", clause)),
                    'zig': set(re.findall(r"matrix\.zig == '([\d.]+)'", clause))}
            once = re.search(r'(?<![!\w.])matrix\.once\b', clause) is not None
            if not want['zig'] and not want['part'] and not once:
                continue
            if not any((not want['part'] or row['part'] in want['part'])
                       and (not want['zig'] or row['zig'] in want['zig'])
                       and (not once or row['once']) for row in test_rows):
                errors.append(f'{WORKFLOW}: the test job step condition `{clause.strip()}` matches no matrix row '
                              f'(near line {number} of the job)')
    return errors


def missing_records(root, test_rows):
    """Each build-mode row verifies a committed x86_64-linux run record of its version."""
    return [f'assurance/build-mode-runs/{r["zig"]}--x86_64-linux--{r["part"]}--llvm.json: the {r["part"]} row of '
            f'{r["zig"]} needs this run record (docs/build-modes.md)'
            for r in test_rows if r['part'] in ONCE[len(PINNED):]
            and not (root/f'assurance/build-mode-runs/{r["zig"]}--x86_64-linux--{r["part"]}--llvm.json').is_file()]


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
    test_rows = rows(args.root)['test']
    problems = dead_conditions(fresh, test_rows) + missing_records(args.root, test_rows)
    if problems:
        print('\n'.join(problems), file=sys.stderr)
        return 1
    if fresh != text:
        print(f'error: {WORKFLOW} matrix rows are stale; run python3 scripts/ci-matrix.py write',
              file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
