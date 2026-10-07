#!/usr/bin/env python3
"""Build-mode and backend qualification records (docs/build-modes.md).

`assurance/build-modes.json` holds one record per optimize mode x backend pair. Each
record states `qualified`, `unqualified` or `excluded`, the claim it supports, the
premise relating the safe analyzed AIR to that build, and the evidence. `check` is a light
source-level gate (no Zig or Lean):

* every mode/backend pair has exactly one record;
* cited evidence exists and its contents match the record's mode and backend;
* a `qualified` record cites a profile and a build command;
* premise IDs exist in docs/premises.md;
* the shipping export/native flags appear in their sources and match compatibility.json;
* fast-math and other changed semantics are excluded, with guard text present in the source;
* every README.md or docs/*.md paragraph that names ReleaseFast or ReleaseSmall links the record.

`commands` prints the heavy commands that unqualified records still need.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = Path('assurance/build-modes.json')
SCHEMA = 'air2lean-build-modes/1'
MODES = ('Debug', 'ReleaseSafe', 'ReleaseFast', 'ReleaseSmall')
BACKENDS = {'llvm': 'stage2_llvm', 'stage2_x86_64': 'stage2_x86_64'}
STATUSES = ('qualified', 'unqualified', 'excluded')
CLAIMS = ('analyzed-air-model', 'no-illegal-behaviour-transfer', 'none')
EVIDENCE = ('profile', 'command', 'literal')
REQUIRED_CHANGED = ('fast-math',)
# Paragraphs naming an unchecked release mode must link the record.
UNCHECKED_MODE = re.compile(r'\bRelease(?:Fast|Small)\b')
RECORD_LINK = re.compile(r'build-modes\.(?:md|json)')
PREMISE_ID = re.compile(r'[A-Z]{3}-\d{2}')


def read(root, rel, errors, where):
    if not isinstance(rel, str) or not rel or Path(rel).is_absolute() or '..' in Path(rel).parts:
        errors.append(f'{where}: invalid repository path {rel!r}')
        return None
    path = root / rel
    if not path.is_file():
        errors.append(f'{where}: missing file {rel}')
        return None
    return path.read_text(encoding='utf-8')


def premise_ids(root):
    text = (root / 'docs/premises.md').read_text(encoding='utf-8')
    return {m.upper() for m in re.findall(r'<a id="([a-z]{3}-\d{2})"></a>', text)}


def check_evidence(root, record, item, errors, where):
    if not isinstance(item, dict) or item.get('kind') not in EVIDENCE:
        errors.append(f'{where}: evidence kind must be one of {", ".join(EVIDENCE)}')
        return
    text = read(root, item.get('path'), errors, where)
    if text is None:
        return
    mode, backend = record['mode'], record['backend']
    if item['kind'] == 'profile':
        try:
            data = json.loads(text)
        except json.JSONDecodeError as error:
            errors.append(f'{where}: {item["path"]} is not JSON ({error})')
            return
        profile = data.get('profile', data) if isinstance(data, dict) else None
        if not isinstance(profile, dict):
            errors.append(f'{where}: {item["path"]} has no profile object')
            return
        if profile.get('build_mode') != mode:
            errors.append(f'{where}: {item["path"]} records build_mode '
                          f'{profile.get("build_mode")!r}, not {mode!r}')
        if profile.get('backend') != BACKENDS[backend]:
            errors.append(f'{where}: {item["path"]} records backend '
                          f'{profile.get("backend")!r}, not {BACKENDS[backend]!r}')
        return
    needle = item.get('text')
    if not isinstance(needle, str) or not needle:
        errors.append(f'{where}: {item["kind"]} evidence needs non-empty text')
        return
    if needle not in text:
        errors.append(f'{where}: {item["path"]} does not contain {needle!r}')
    if item['kind'] == 'command':
        flags = needle.split()
        if '-O' + mode not in flags:
            errors.append(f'{where}: command {needle!r} does not select -O{mode}')
        if backend == 'llvm' and '-fno-llvm' in flags:
            errors.append(f'{where}: command {needle!r} disables LLVM')
        if backend != 'llvm' and '-fno-llvm' not in flags:
            errors.append(f'{where}: command {needle!r} does not select a non-LLVM backend (-fno-llvm)')


def check_record(root, record, known, errors):
    where = f'{record.get("mode")}/{record.get("backend")}'
    if record.get('status') not in STATUSES:
        errors.append(f'{where}: status must be one of {", ".join(STATUSES)}')
    if record.get('claim') not in CLAIMS:
        errors.append(f'{where}: claim must be one of {", ".join(CLAIMS)}')
    for field in ('scope', 'premise'):
        if not isinstance(record.get(field), str) or not record[field].strip():
            errors.append(f'{where}: {field} must be a non-empty statement')
    premises = record.get('premises')
    if not isinstance(premises, list) or not all(isinstance(p, str) and PREMISE_ID.fullmatch(p) for p in premises):
        errors.append(f'{where}: premises must be a list of premise IDs')
        premises = []
    for premise in premises:
        if premise not in known:
            errors.append(f'{where}: unknown premise {premise} (docs/premises.md)')
    evidence = record.get('evidence')
    if not isinstance(evidence, list):
        errors.append(f'{where}: evidence must be a list')
        evidence = []
    for index, item in enumerate(evidence):
        check_evidence(root, record, item, errors, f'{where}: evidence[{index}]')
    kinds = {item.get('kind') for item in evidence if isinstance(item, dict)}
    status, claim = record.get('status'), record.get('claim')
    if claim not in (None, 'none') and not premises:
        errors.append(f'{where}: claim {claim!r} must cite the premises it rests on')
    if status == 'qualified':
        if claim == 'none':
            errors.append(f'{where}: a qualified record must state its claim')
        for kind in ('profile', 'command'):
            if kind not in kinds:
                errors.append(f'{where}: a qualified record must cite {kind} evidence')
    elif status == 'unqualified':
        if not isinstance(record.get('missing'), str) or not record['missing'].strip():
            errors.append(f'{where}: an unqualified record must state the missing evidence')
        if claim != 'none' and not record.get('commands'):
            errors.append(f'{where}: an unqualified claim must list the commands that would qualify it')
    elif status == 'excluded' and claim != 'none':
        errors.append(f'{where}: an excluded record cannot support a claim')


def check_shipping(root, data, records, errors):
    shipping = data.get('shipping')
    if not isinstance(shipping, dict):
        errors.append('shipping: missing record of the shipping compiler, backend and flags')
        return
    for part in ('export', 'native'):
        entry = shipping.get(part)
        if (not isinstance(entry, dict) or not isinstance(entry.get('flags'), str)
                or not isinstance(entry.get('sources'), list) or not entry['sources']):
            errors.append(f'shipping.{part}: needs flags and sources')
            continue
        for rel in entry['sources']:
            text = read(root, rel, errors, f'shipping.{part}')
            if text is not None and entry['flags'] not in text:
                errors.append(f'shipping.{part}: {rel} does not contain {entry["flags"]!r}')
    export = shipping.get('export')
    if isinstance(export, dict) and export.get('recorded_backend') not in BACKENDS.values():
        errors.append('shipping.export: recorded_backend must be a known backend')
    text = read(root, 'compatibility.json', errors, 'shipping')
    try:
        compat = json.loads(text) if text is not None else {}
    except json.JSONDecodeError as error:
        errors.append(f'shipping: compatibility.json is not JSON ({error})')
        compat = {}
    translation = compat.get('translation') if isinstance(compat, dict) else None
    optimize = translation.get('optimize') if isinstance(translation, dict) else None
    if shipping.get('compatibility_optimize') != optimize:
        errors.append(f'shipping: compatibility.json translation.optimize is {optimize!r}, '
                      f'record says {shipping.get("compatibility_optimize")!r}')
    backend = next((name for name, tag in BACKENDS.items()
                    if isinstance(export, dict) and tag == export.get('recorded_backend')), None)
    reference = records.get((optimize, backend))
    if reference is None or reference.get('status') != 'qualified':
        errors.append(f'shipping: the reference build {optimize}/{backend} is not qualified')


def check_changed(root, data, errors):
    entries = data.get('changed_semantics')
    if not isinstance(entries, list):
        errors.append('changed_semantics: must be a list')
        return
    seen = set()
    for entry in entries:
        ident = entry.get('id') if isinstance(entry, dict) else None
        where = f'changed_semantics.{ident}'
        if not isinstance(ident, str) or ident in seen:
            errors.append(f'{where}: missing or duplicate id')
            continue
        seen.add(ident)
        if entry.get('status') != 'excluded':
            errors.append(f'{where}: changed semantics must be excluded until separately treated')
        if not isinstance(entry.get('reason'), str) or not entry['reason'].strip():
            errors.append(f'{where}: needs a reason')
        guards = entry.get('guards')
        if not isinstance(guards, list) or not guards:
            errors.append(f'{where}: needs at least one source guard')
            continue
        for guard in guards:
            text = read(root, guard.get('path') if isinstance(guard, dict) else None, errors, where)
            needle = guard.get('text') if isinstance(guard, dict) else None
            if text is not None and (not isinstance(needle, str) or not needle or needle not in text):
                errors.append(f'{where}: guard text {needle!r} not found in {guard["path"]}')
    for ident in REQUIRED_CHANGED:
        if ident not in seen:
            errors.append(f'changed_semantics: missing {ident!r} treatment')


def doc_files(root):
    yield root / 'README.md'
    yield from sorted((root / 'docs').glob('*.md'))


def check_docs(root, data, errors):
    own = data.get('doc')
    if not isinstance(own, str) or not (root / own).is_file():
        errors.append(f'doc: missing record documentation {own!r}')
    for path in doc_files(root):
        if not path.is_file() or path.relative_to(root).as_posix() == own:
            continue
        text = path.read_text(encoding='utf-8')
        line = 1
        for paragraph in re.split(r'(\n[ \t]*\n)', text):
            if UNCHECKED_MODE.search(paragraph) and not RECORD_LINK.search(paragraph):
                errors.append(f'{path.relative_to(root)}:{line}: paragraph names an unchecked '
                              f'release mode without linking build-modes.md')
            line += paragraph.count('\n')


def validate(data, root=ROOT):
    root = Path(root)
    errors = []
    if not isinstance(data, dict) or data.get('schema') != SCHEMA:
        return [f'registry: schema must be {SCHEMA!r}']
    records = {}
    raw = data.get('records')
    if not isinstance(raw, list):
        return ['records: must be a list']
    known = premise_ids(root)
    for record in raw:
        if not isinstance(record, dict):
            errors.append('records: every record must be an object')
            continue
        key = (record.get('mode'), record.get('backend'))
        if key[0] not in MODES or key[1] not in BACKENDS:
            errors.append(f'records: unknown mode/backend {key[0]}/{key[1]}')
            continue
        if key in records:
            errors.append(f'records: duplicate record {key[0]}/{key[1]}')
            continue
        records[key] = record
        check_record(root, record, known, errors)
    for mode in MODES:
        for backend in BACKENDS:
            if (mode, backend) not in records:
                errors.append(f'records: no qualification record for {mode}/{backend}')
    check_shipping(root, data, records, errors)
    check_changed(root, data, errors)
    check_docs(root, data, errors)
    return errors


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--root', type=Path, default=ROOT)
    sub = parser.add_subparsers(dest='action', required=True)
    sub.add_parser('check', help='light record, evidence and documentation check')
    sub.add_parser('commands', help='print commands that unqualified claims still need')
    args = parser.parse_args(argv)
    try:
        data = json.loads((args.root / REGISTRY).read_text(encoding='utf-8'))
    except (OSError, json.JSONDecodeError) as error:
        print(f'build-modes: cannot read {REGISTRY}: {error}', file=sys.stderr)
        return 1
    if args.action == 'commands':
        for record in data.get('records', []):
            for command in record.get('commands', []):
                print(f'# {record["mode"]}/{record["backend"]}\n{command}')
        return 0
    errors = validate(data, args.root)
    for error in errors:
        print(f'build-modes: {error}', file=sys.stderr)
    if errors:
        return 1
    qualified = sum(r['status'] == 'qualified' for r in data['records'])
    print(f'build-modes: ok ({len(data["records"])} records, {qualified} qualified)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
