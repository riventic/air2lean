#!/usr/bin/env python3
"""Check the Q02 register-to-mutation map (assurance/mutation-map.json, docs/mutation-map.md).

The map names, for every ROADMAP.md register ID, its negative tests and designated semantic
mutants, each mutant with one category. `check` fails when
  * the map's IDs differ from the register, or an entry is malformed;
  * a referenced test file or anchor, or a referenced mutant, does not exist;
  * a `complete` register row lacks a negative test, a designated mutant, or a mutant for one
    of the categories it declares;
  * a mutation of scripts/mutate.sh or tests/roadmap/mutation-map/mutants.py is mapped nowhere;
  * a mutant category has no mutant anywhere in the map;
  * a designated scripts/mutate.sh mutant has no recorded kill in assurance/mutation-kills.json
    (which regression killed it: a differential example or a proof module), the record names a
    regression that does not exist, was recorded for another version of the mutation's block in
    scripts/mutate.sh (stale), was recorded against other committed inputs of its regression
    (`target_sha256`: the proof module and the `Proofs` modules it imports, or the example's
    program and its tests/diff/<ex>/ harness, inputs and allow-lists; stale), or the ledger names
    a mutation that is gone. A mutation that cannot
    run on the recording host (asm is x86_64 only) may carry `{"unrecorded": reason, block_sha256}`:
    `check` lists it as a kill gap, and only `kills record` from a host that runs it clears it.
Gaps of incomplete rows (declared category without a mutant, no negative test, no mutant) are
reported, not failed: a partial row may still lack evidence.

`check` reads committed text only; it never runs a test, a mutant or a toolchain. The kills come
from `scripts/mutate.sh` runs with AIR2LEAN_MUTATION_KILL_LOG set:
  kills record --log LOG   merge the killed mutations of LOG into the ledger (fails on a survivor)
  kills verify --log LOG   fail unless LOG's mutations were killed by the regression the ledger names
"""

import argparse
import ast
import hashlib
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
KILLS = 'assurance/mutation-kills.json'
KILLS_SCHEMA = 'air2lean-mutation-kills/1'
KILL_KINDS = ('diff', 'proof')
MUTATION_MARK = re.compile(r'^echo "== mutation \(([a-z]+)\)', re.M)
BLOCK_END = '[ "$mutations_run" -gt 0 ]'
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


def mutation_blocks(root):
    """label -> sha256 of the text of that mutation in scripts/mutate.sh (marker to the next)."""
    text = (root / MUTATE_SH).read_text()
    marks = list(MUTATION_MARK.finditer(text))
    end = text.find(BLOCK_END)
    blocks = {}
    for i, mark in enumerate(marks):
        stop = marks[i + 1].start() if i + 1 < len(marks) else (end if end > mark.start() else len(text))
        blocks[mark.group(1)] = hashlib.sha256(text[mark.start():stop].encode()).hexdigest()
    return blocks


def kill_target_exists(root, kind, target):
    if kind == 'diff':
        return bool(re.fullmatch(r'[a-zA-Z0-9_-]+', target)) and (root / 'examples' / target / f'{target}.zig').is_file()
    return bool(re.fullmatch(r'\w+(\.\w+)+', target)) and (root / (target.replace('.', '/') + '.lean')).is_file()


def target_files(root, kind, target):
    """The committed inputs of a killing regression, repository-relative and sorted: a proof
    module and the hand-written `Proofs` modules it imports (transitively; mutate.sh regenerates
    each `Gen` module with the mutated translator, so the committed one is not an input), or an
    example's program and its tests/diff/<ex>/ harness, inputs and allow-lists."""
    if kind == 'diff':
        files = {p for d in (root / 'examples' / target, root / 'tests/diff' / target) if d.is_dir()
                 for p in d.rglob('*') if p.is_file()}
    else:
        files, pending = set(), [target]
        while pending:
            module = pending.pop()
            path = root / (module.replace('.', '/') + '.lean')
            if module.rsplit('.', 1)[-1] != 'Gen' and path not in files and path.is_file():
                files.add(path)
                pending += re.findall(r'^import\s+(Proofs\.\S+)', path.read_text(), re.M)
    return sorted(p.relative_to(root).as_posix() for p in files)


def target_sha256(root, kind, target):
    """One digest over the paths and contents of `target_files`."""
    digest = hashlib.sha256()
    for rel in target_files(root, kind, target):
        digest.update(f'{rel}\0{hashlib.sha256((root / rel).read_bytes()).hexdigest()}\n'.encode())
    return digest.hexdigest()


def check_kills(root, kills, designated, blocks, problems, gaps):
    """Every designated mutate.sh mutant needs a current recorded kill by an existing regression."""
    if not isinstance(kills, dict) or kills.get('schema') != KILLS_SCHEMA or not isinstance(kills.get('mutants'), dict):
        problems.append(f'{KILLS}: expected schema {KILLS_SCHEMA!r} with a mutants object')
        return
    entries = kills['mutants']
    for name in sorted(entries.keys() - blocks.keys()):
        problems.append(f'{KILLS}: kill recorded for {name}, which {MUTATE_SH} no longer has')
    for name in sorted(designated):
        entry, where = entries.get(name), f'{KILLS}: {name}'
        if entry is None:
            problems.append(f'{where}: designated mutant has no recorded kill')
            continue
        by = entry.get('killed_by') if isinstance(entry, dict) else None
        if isinstance(entry, dict) and set(entry) == {'unrecorded', 'block_sha256'} and isinstance(entry['unrecorded'], str):
            if entry['block_sha256'] != blocks.get(name):
                problems.append(f'{where}: unrecorded entry is for a different version of the mutation')
            gaps.append(f'{name}: {entry["unrecorded"]}')
        elif (not isinstance(entry, dict) or set(entry) != {'killed_by', 'block_sha256', 'target_sha256'}
                or not isinstance(by, dict) or set(by) != {'kind', 'target'}
                or by['kind'] not in KILL_KINDS or not isinstance(by['target'], str)):
            problems.append(f'{where}: needs killed_by {{kind: diff|proof, target}}, block_sha256 and target_sha256')
        elif not kill_target_exists(root, by['kind'], by['target']):
            problems.append(f'{where}: killing {by["kind"]} regression {by["target"]!r} does not exist')
        elif entry['block_sha256'] != blocks.get(name):
            problems.append(f'{where}: kill recorded for a different version of the mutation; rerun it and `kills record`')
        elif entry['target_sha256'] != target_sha256(root, by['kind'], by['target']):
            problems.append(f'{where}: kill recorded against other inputs of {by["kind"]} regression {by["target"]}; '
                            'rerun the mutation and `kills record`')


def shard_labels(root):
    return set((root / SHARDS).read_text().split())


def py_mutant_names(root):
    """Keys of the module-level `MUTANTS = {...}` literal, however they are written."""
    for node in ast.parse((root / PY_MUTANTS).read_text()).body:
        if (isinstance(node, ast.Assign) and isinstance(node.value, ast.Dict)
                and any(isinstance(t, ast.Name) and t.id == 'MUTANTS' for t in node.targets)):
            return {k.value for k in node.value.keys if isinstance(k, ast.Constant) and isinstance(k.value, str)}
    raise ValueError(f'{PY_MUTANTS}: no MUTANTS dictionary literal')


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
    """Validate one entry; return (declared categories, tests, mutants, mutant categories).

    Malformed parts are recorded as problems and returned empty, so callers never iterate them.
    """
    fields = ('categories', 'negative_tests', 'mutants')
    if (not isinstance(entry, dict) or set(entry) - {*fields, 'note'}
            or any(not isinstance(entry.get(f, []), list) for f in fields)):
        problems.append(f'{rid}: entry must be an object with categories/negative_tests/mutants lists and a note')
        return [], [], [], set()
    declared = entry.get('categories', [])
    if any(c not in CATEGORIES for c in declared) or len(set(declared)) != len(declared):
        problems.append(f'{rid}: categories must be distinct names from {", ".join(CATEGORIES)}')
        declared = []
    tests, mutants = entry.get('negative_tests', []), entry.get('mutants', [])
    for i, test in enumerate(tests):
        where = f'{rid}: negative_tests[{i}]'
        if (not isinstance(test, dict) or set(test) != {'path', 'anchor'}
                or not isinstance(test['anchor'], str) or not test['anchor']):
            problems.append(f'{where}: needs exactly a path and a nonempty anchor')
            continue
        text = repo_file(root, test['path'], where, problems)
        if text is not None and test['anchor'] not in text:
            problems.append(f'{where}: anchor {test["anchor"]!r} not in {test["path"]}')
    found, seen, valid = set(), set(), []
    for i, mutant in enumerate(mutants):
        where = f'{rid}: mutants[{i}]'
        if (not isinstance(mutant, dict) or not {'name', 'path', 'category'} <= set(mutant) <= {'name', 'path', 'category', 'anchor'}
                or any(not isinstance(mutant[k], str) or not mutant[k] for k in ('name', 'path', 'category'))):
            problems.append(f'{where}: needs name, path, category and optional anchor')
            continue
        valid.append(mutant)
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
    return declared, tests, valid, found


def analyze(root=ROOT, data=None, kills=None):
    """Return the coverage report; report['problems'] is empty iff the map passes."""
    root = Path(root)
    if data is None:
        data = json.loads((root / MAP).read_text())
    if kills is None and (root / KILLS).is_file():
        kills = json.loads((root / KILLS).read_text())
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
        declared, tests, mutants, found = check_entry(root, rid, entry, problems, labels)
        for m in mutants:
            if m['category'] in by_category:
                by_category[m['category']].append(f'{rid}:{m["name"]}')
            if m['path'] in mapped:
                mapped[m['path']].add(m['name'])
        missing = [c for c in declared if c not in found]
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
    kill_gaps = []
    check_kills(root, kills, mapped[MUTATE_SH], mutation_blocks(root), problems, kill_gaps)
    for category in CATEGORIES:
        if not by_category[category]:
            problems.append(f'category {category}: no designated mutant in the map')
    return {'problems': problems, 'categories': by_category, 'gaps': gaps,
            'complete': [r for r, s in rows if s == 'complete'], 'requirements': len(rows), 'kill_gaps': kill_gaps}


def read_kill_log(path):
    """label -> (status, kind, target) from a mutate.sh AIR2LEAN_MUTATION_KILL_LOG."""
    log = {}
    for number, line in enumerate(Path(path).read_text().splitlines(), 1):
        parts = line.split()
        if len(parts) != 4 or parts[1] not in ('killed', 'survived') or parts[2] not in KILL_KINDS:
            raise ValueError(f'{path}:{number}: expected "<label> killed|survived diff|proof <target>"')
        log[parts[0]] = tuple(parts[1:])
    if not log:
        raise ValueError(f'{path}: no mutation was run')
    return log


def kills_command(args):
    log, blocks = read_kill_log(args.log), mutation_blocks(args.root)
    path = args.root / KILLS
    ledger = json.loads(path.read_text()) if path.is_file() else {'schema': KILLS_SCHEMA, 'mutants': {}}
    problems = [f'{name}: survived (ran {kind} {target})' for name, (status, kind, target) in sorted(log.items())
                if status != 'killed']
    problems += [f'{name}: not a {MUTATE_SH} mutation' for name in sorted(log.keys() - blocks.keys())]
    if args.kills_command == 'verify':
        for name, (status, kind, target) in sorted(log.items()):
            entry = ledger['mutants'].get(name)
            if status != 'killed' or name not in blocks or 'unrecorded' in (entry or {}):
                continue
            if entry is None or entry['killed_by'] != {'kind': kind, 'target': target}:
                problems.append(f'{name}: killed by {kind} {target}, ledger records {entry and entry["killed_by"]}')
            elif entry.get('target_sha256') != target_sha256(args.root, kind, target):
                problems.append(f'{name}: the ledger kill was recorded against other inputs of {kind} {target}')
    elif not problems:
        for name, (_, kind, target) in log.items():
            ledger['mutants'][name] = {'killed_by': {'kind': kind, 'target': target}, 'block_sha256': blocks[name],
                                       'target_sha256': target_sha256(args.root, kind, target)}
        ledger['mutants'] = dict(sorted(ledger['mutants'].items()))
        path.write_text(json.dumps(ledger, indent=2) + '\n')
    for problem in problems:
        print(f'error: {problem}', file=sys.stderr)
    if not problems:
        print(f'kills {args.kills_command}: {len(log)} mutations killed')
    return 1 if problems else 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    sub = parser.add_subparsers(dest='command', required=True)
    check = sub.add_parser('check', help='validate the map and report per-category coverage gaps')
    check.add_argument('--root', type=Path, default=ROOT)
    check.add_argument('--json', action='store_true', help='print the report as JSON')
    kills = sub.add_parser('kills', help='record or verify which regression kills each mutate.sh mutant')
    kills.add_argument('kills_command', choices=('record', 'verify'))
    kills.add_argument('--root', type=Path, default=ROOT)
    kills.add_argument('--log', type=Path, required=True, help='AIR2LEAN_MUTATION_KILL_LOG of a mutate.sh run')
    args = parser.parse_args(argv)
    try:
        if args.command == 'kills':
            return kills_command(args)
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
        for gap in report.get('kill_gaps', []):
            print(f'kill gap {gap}')
        for problem in report['problems']:
            print(f'error: {problem}', file=sys.stderr)
        if not report['problems']:
            print(f'mutation map ok: {report["requirements"]} register IDs; '
                  f'{len(report["complete"])} complete rows have negative tests and designated mutants')
    return 1 if report['problems'] else 0


if __name__ == '__main__':
    sys.exit(main())
