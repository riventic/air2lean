#!/usr/bin/env python3
"""Check the Q02 register-to-mutation map (assurance/mutation-map.json, docs/mutation-map.md).

The map names, for every ROADMAP.md register ID, its negative tests and designated semantic
mutants, each mutant with one category. `check` fails when
  * the map's IDs differ from the register, or an entry is malformed;
  * a referenced test file or anchor, or a referenced mutant, does not exist;
  * a `complete` register row lacks a negative test, a designated mutant, or a mutant for one
    of the categories it declares;
  * a mutation of scripts/mutate.sh or tests/roadmap/mutation-map/mutants.py is mapped nowhere;
  * a mutant category has no mutant anywhere in the map.
Gaps of incomplete rows (declared category without a mutant, no negative test, no mutant) are
reported, not failed: a partial row may still lack evidence.

Reads committed text only; never runs a test, a mutant or a toolchain.
"""

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MAP = 'assurance/mutation-map.json'
SCHEMA = 'air2lean-mutation-map/1'
CATEGORIES = ('forwarding', 'layout', 'operand-order', 'failure-cleanup',
              'profile-selection', 'invariant-transfer')
MUTANT_CATEGORIES = CATEGORIES + ('other',)
MUTATE_SH = 'scripts/mutate.sh'
SHARDS = 'scripts/mutation-shards.txt'
PY_MUTANTS = 'tests/roadmap/mutation-map/mutants.py'
REGISTER_ROW = re.compile(r'\| ([A-Z]\d\d) \| [^|]+ \| (\w+) \|')


def register(root):
    """Ordered (id, status) rows of the ROADMAP.md requirement register."""
    rows = [m.groups() for m in map(REGISTER_ROW.match, (root / 'ROADMAP.md').read_text().splitlines()) if m]
    if not rows:
        raise ValueError('ROADMAP.md: requirement register not found')
    return rows


def mutate_sh_labels(root):
    return set(re.findall(r'^echo "== mutation \(([a-z]+)\)', (root / MUTATE_SH).read_text(), re.M))


def shard_labels(root):
    return set((root / SHARDS).read_text().split())


def py_mutant_names(root):
    return set(re.findall(r"^    '([a-z0-9-]+)': \($", (root / PY_MUTANTS).read_text(), re.M))


def repo_file(root, rel, where, problems):
    """Text of a repository-relative file, or None after recording a problem."""
    if not isinstance(rel, str) or not rel or rel.startswith('/') or '..' in Path(rel).parts:
        problems.append(f'{where}: path must be repository-relative: {rel!r}')
        return None
    path = root / rel
    if not path.is_file():
        problems.append(f'{where}: missing file {rel}')
        return None
    return path.read_text(encoding='utf-8', errors='replace')


def check_entry(root, rid, entry, problems, labels):
    """Validate one requirement entry; return its mutant category set."""
    if not isinstance(entry, dict) or set(entry) - {'categories', 'negative_tests', 'mutants', 'note'}:
        problems.append(f'{rid}: entry must be an object with categories/negative_tests/mutants/note')
        return set()
    declared = entry.get('categories', [])
    if not isinstance(declared, list) or any(c not in CATEGORIES for c in declared) or len(set(declared)) != len(declared):
        problems.append(f'{rid}: categories must be distinct names from {", ".join(CATEGORIES)}')
    for i, test in enumerate(entry.get('negative_tests', [])):
        where = f'{rid}: negative_tests[{i}]'
        if not isinstance(test, dict) or set(test) != {'path', 'anchor'} or not isinstance(test['anchor'], str) or not test['anchor']:
            problems.append(f'{where}: needs exactly a path and a nonempty anchor')
            continue
        text = repo_file(root, test['path'], where, problems)
        if text is not None and test['anchor'] not in text:
            problems.append(f'{where}: anchor {test["anchor"]!r} not in {test["path"]}')
    found, seen = set(), set()
    for i, mutant in enumerate(entry.get('mutants', [])):
        where = f'{rid}: mutants[{i}]'
        if (not isinstance(mutant, dict) or not {'name', 'path', 'category'} <= set(mutant) <= {'name', 'path', 'category', 'anchor'}
                or not isinstance(mutant['name'], str) or not mutant['name']):
            problems.append(f'{where}: needs name, path, category and optional anchor')
            continue
        key = (mutant['path'], mutant['name'])
        if key in seen:
            problems.append(f'{where}: duplicate mutant {mutant["name"]}')
        seen.add(key)
        if mutant['category'] not in MUTANT_CATEGORIES:
            problems.append(f'{where}: unknown category {mutant["category"]!r}')
        else:
            found.add(mutant['category'])
        text = repo_file(root, mutant['path'], where, problems)
        if text is None:
            continue
        name = mutant['name']
        if mutant['path'] == MUTATE_SH:
            if name not in labels['mutate.sh'] or name not in labels['shards']:
                problems.append(f'{where}: {MUTATE_SH} has no sharded mutation ({name})')
        elif mutant['path'] == PY_MUTANTS:
            if name not in labels['python']:
                problems.append(f'{where}: {PY_MUTANTS} has no mutant {name}')
        elif 'anchor' in mutant:
            if not isinstance(mutant['anchor'], str) or not mutant['anchor'] or mutant['anchor'] not in text:
                problems.append(f'{where}: anchor {mutant.get("anchor")!r} not in {mutant["path"]}')
        elif f"'{name}'" not in text and f'"{name}"' not in text:
            problems.append(f'{where}: no mutant named {name!r} in {mutant["path"]}')
    return found


def analyze(root=ROOT, data=None):
    """Return the coverage report; report['problems'] is empty iff the map passes."""
    root = Path(root)
    if data is None:
        data = json.loads((root / MAP).read_text())
    problems = []
    if not isinstance(data, dict) or data.get('schema') != SCHEMA or not isinstance(data.get('requirements'), dict):
        return {'problems': [f'{MAP}: expected schema {SCHEMA!r} with a requirements object']}
    rows = register(root)
    status = dict(rows)
    entries = data['requirements']
    for rid in [r for r, _ in rows if r not in entries]:
        problems.append(f'{rid}: register ID missing from {MAP}')
    for rid in [r for r in entries if r not in status]:
        problems.append(f'{rid}: not a ROADMAP.md register ID')
    labels = {'mutate.sh': mutate_sh_labels(root), 'shards': shard_labels(root), 'python': py_mutant_names(root)}
    by_category = {c: [] for c in MUTANT_CATEGORIES}
    mapped = {MUTATE_SH: set(), PY_MUTANTS: set()}
    gaps = []
    for rid, _ in rows:
        entry = entries.get(rid)
        if entry is None:
            continue
        found = check_entry(root, rid, entry, problems, labels)
        if not isinstance(entry, dict):
            continue
        tests, mutants = entry.get('negative_tests', []), entry.get('mutants', [])
        for m in mutants:
            if isinstance(m, dict) and m.get('category') in by_category:
                by_category[m['category']].append(f'{rid}:{m.get("name")}')
                if m.get('path') in mapped:
                    mapped[m['path']].add(m.get('name'))
        missing = [c for c in entry.get('categories', []) if c not in found]
        lacks = [what for what, items in (('negative tests', tests), ('designated mutants', mutants)) if not items]
        if missing:
            lacks.append('mutants for ' + ', '.join(missing))
        if not lacks:
            continue
        if status[rid] == 'complete':
            problems.append(f'{rid}: complete row lacks ' + '; '.join(lacks))
        else:
            gaps.append({'id': rid, 'status': status[rid], 'lacks': lacks})
    for path, names in ((MUTATE_SH, labels['mutate.sh']), (PY_MUTANTS, labels['python'])):
        for name in sorted(names - mapped[path]):
            problems.append(f'{path}: mutation {name} is mapped to no register ID')
    for category in CATEGORIES:
        if not by_category[category]:
            problems.append(f'category {category}: no designated mutant in the map')
    return {'problems': problems, 'categories': by_category, 'gaps': gaps,
            'complete': [r for r, s in rows if s == 'complete'], 'requirements': len(rows)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    sub = parser.add_subparsers(dest='command', required=True)
    check = sub.add_parser('check', help='validate the map and report per-category coverage gaps')
    check.add_argument('--root', type=Path, default=ROOT)
    check.add_argument('--json', action='store_true', help='print the report as JSON')
    args = parser.parse_args(argv)
    try:
        report = analyze(args.root)
    except (OSError, ValueError) as error:
        print(f'error: {error}', file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        for category, mutants in report.get('categories', {}).items():
            ids = sorted({m.split(':', 1)[0] for m in mutants})
            print(f'{category}: {len(mutants)} mutants' + (f' ({", ".join(ids)})' if ids else ''))
        for gap in report.get('gaps', []):
            print(f'gap {gap["id"]} ({gap["status"]}): ' + '; '.join(gap['lacks']))
        for problem in report['problems']:
            print(f'error: {problem}', file=sys.stderr)
        if not report['problems']:
            print(f'mutation map ok: {report["requirements"]} register IDs; '
                  f'{len(report["complete"])} complete rows have negative tests and designated mutants')
    return 1 if report['problems'] else 0


if __name__ == '__main__':
    sys.exit(main())
