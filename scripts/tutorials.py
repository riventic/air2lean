#!/usr/bin/env python3
"""Tutorial runner: lint, list the modules to build, and check every tutorial.

  tutorials.py lint     [--root DIR]                 layout, README sections and premise IDs
  tutorials.py modules  [--root DIR]                 the modules the tutorials import (lake build)
  tutorials.py check    [--root DIR] [--results D]   elaborate Main and Solution; Negative must fail

A checked tutorial is a directory tutorials/<name>/ with Main.lean (the worked proof),
Solution.lean (the exercise, solved), Negative.lean (a false variant Lean must reject, with a
`-- expect-error: <text>` line naming the expected diagnostic) and README.md. The README's
"Assumptions and remaining obligations" section lists exactly the file premises that
docs/premise-index.md derives for Main.lean. A directory in DOCUMENTED has only a README: its
workflow is not yet runnable from a clean environment. `check` needs the modules from
`modules` built (`lake build $(python3 scripts/tutorials.py modules)`).
"""
import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FILES = ('README.md', 'Main.lean', 'Solution.lean', 'Negative.lean')
# Documentation-only tutorials and why they have no checked proof yet.
DOCUMENTED = {
    'cross-target': 'only the reference profiles are qualified; no second target is runnable',
}
SECTIONS = ('## Steps', '## Exercise', '## Negative control', '## Assumptions and remaining obligations')
PREMISE = re.compile(r'\b[A-Z]{3}-\d{2}\b')
EXPECT = re.compile(r'^-- expect-error: (.+)$', re.M)


def tutorials(root):
    return sorted(p for p in (root / 'tutorials').iterdir() if p.is_dir())


def checked(root):
    return [p for p in tutorials(root) if p.name not in DOCUMENTED]


def section(text, heading):
    """The body of a `## ` section, up to the next `## ` heading."""
    start = text.find(heading + '\n')
    if start < 0:
        return ''
    body = text[start + len(heading) + 1:]
    end = body.find('\n## ')
    return body if end < 0 else body[:end]


def file_premises(root, rel):
    """The `File premises:` IDs that docs/premise-index.md records for `rel`."""
    text = (root / 'docs/premise-index.md').read_text()
    match = re.search(rf'^## `{re.escape(rel)}`\n\nFile premises: (.*)$', text, re.M)
    return set(PREMISE.findall(match.group(1))) if match else None


def lint(root):
    errors = []
    names = {p.name for p in tutorials(root)}
    for name in sorted(set(DOCUMENTED) - names):
        errors.append(f'tutorials/{name}: listed as documented but missing')
    for path in tutorials(root):
        rel = f'tutorials/{path.name}'
        if path.name in DOCUMENTED:
            present = sorted(f.name for f in path.iterdir())
            if present != ['README.md']:
                errors.append(f'{rel}: a documented tutorial has only README.md, found {present}')
            elif '## Status' not in (path / 'README.md').read_text():
                errors.append(f'{rel}/README.md: missing ## Status')
            continue
        missing = [f for f in FILES if not (path / f).is_file()]
        if missing:
            errors.append(f'{rel}: missing {", ".join(missing)}')
            continue
        readme = (path / 'README.md').read_text()
        for heading in SECTIONS:
            if heading not in readme:
                errors.append(f'{rel}/README.md: missing {heading}')
        negative = (path / 'Negative.lean').read_text()
        if not EXPECT.search(negative):
            errors.append(f'{rel}/Negative.lean: missing "-- expect-error: <text>"')
        if not re.search(r'^theorem ', negative, re.M):
            errors.append(f'{rel}/Negative.lean: no theorem to reject')
        derived = file_premises(root, f'{rel}/Main.lean')
        listed = set(PREMISE.findall(section(readme, SECTIONS[-1])))
        if derived is None:
            errors.append(f'{rel}/Main.lean: not in docs/premise-index.md (run scripts/premises.py write)')
        elif listed != derived:
            errors.append(f'{rel}/README.md: assumptions list {sorted(listed)}, '
                          f'docs/premise-index.md derives {sorted(derived)}')
    return errors


def modules(root):
    found = set()
    for path in checked(root):
        for lean in sorted(path.glob('*.lean')):
            found.update(re.findall(r'^import (\S+)$', lean.read_text(), re.M))
    return sorted(found)


def lean(root, rel, log):
    with open(log, 'w') as out:
        result = subprocess.run(['lake', 'env', 'lean', rel], cwd=root, stdout=out, stderr=subprocess.STDOUT)
    return result.returncode, Path(log).read_text()


def check(root, results):
    results.mkdir(parents=True, exist_ok=True)
    failures = 0
    for path in checked(root):
        rel, before = f'tutorials/{path.name}', failures
        for name in ('Main.lean', 'Solution.lean'):
            code, text = lean(root, f'{rel}/{name}', results / f'{path.name}-{name}.log')
            if code != 0:
                failures += 1
                print(f'FAIL: {rel}/{name} (exit {code})\n{text}', file=sys.stderr)
        source = (path / 'Negative.lean').read_text()
        expect = EXPECT.search(source).group(1).strip()
        # The expected error must come from the last theorem (the false claim), not from a
        # broken helper above it.
        last = max(i for i, line in enumerate(source.splitlines(), 1) if line.startswith('theorem '))
        code, text = lean(root, f'{rel}/Negative.lean', results / f'{path.name}-Negative.lean.log')
        lines = [int(n) for n in re.findall(rf'Negative\.lean:(\d+):\d+: error: {re.escape(expect)}', text)]
        if code == 0:
            failures += 1
            print(f'FAIL: Lean accepted the negative control {rel}/Negative.lean', file=sys.stderr)
        elif not any(n >= last for n in lines):
            failures += 1
            print(f'FAIL: {rel}/Negative.lean failed without "error: {expect}" in its last theorem '
                  f'(line {last} on)\n{text}', file=sys.stderr)
        if failures == before:
            print(f'OK: {rel}: proof, exercise and negative control')
    return failures


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('command', choices=('lint', 'modules', 'check'))
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--results', type=Path, default=None, help='log directory (default .lake/tutorials)')
    args = parser.parse_args(argv)
    root = args.root.resolve()
    if args.command == 'modules':
        print('\n'.join(modules(root)))
        return 0
    errors = lint(root)
    for error in errors:
        print(f'error: {error}', file=sys.stderr)
    if errors or args.command == 'lint':
        return 1 if errors else 0
    return 1 if check(root, args.results or root / '.lake/tutorials') else 0


if __name__ == '__main__':
    sys.exit(main())
