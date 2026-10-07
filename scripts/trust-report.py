#!/usr/bin/env python3
"""V03 trust report: classify every pipeline stage from assurance/trust-stages.json.

`write` regenerates docs/trust-report.md. `check` exits 1 when the report is stale or the
stage table is invalid: a required stage is missing, a class is unknown, a premise is not
defined in docs/premises.md, a TRU-* premise is cited by no stage, a cited component,
checker, test or evidence file is missing, a check's CI command is absent from
.github/workflows/ci.yml, or a check's test is not run by CI (directly or through a script
that a CI command names). Runs no Zig, Lake or Lean.
"""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
STAGES = 'assurance/trust-stages.json'
REPORT = 'docs/trust-report.md'
PREMISES = 'docs/premises.md'
CI = '.github/workflows/ci.yml'
CLASSES = {
    'kernel-checked': 'The Lean kernel checks the statement. Trusted base: the cited premises (TRU-01 at least).',
    'independently-checked-metadata': 'A checker that shares no code with the stage re-checks its output metadata '
                                      '(structure, identity, inventory). Semantic preservation stays with the cited premises.',
    'unverified-assumption': 'Believed, not checked. The cited premises state the assumption.',
}
REQUIRED = ('sema', 'exporter', 'decode', 'canonicalization', 'normalization', 'checker', 'emitter',
            'ziglean-semantics', 'theorems', 'lean-kernel', 'native-backend')
PREMISE_HEADING = re.compile(r'^### ([A-Z]{3}-[0-9]{2}) — ', re.M)


def defined_premises(root):
    return set(PREMISE_HEADING.findall((root / PREMISES).read_text(encoding='utf-8')))


def validate(data, root=ROOT):
    """Return a list of problems with the stage table (empty: valid)."""
    problems = []
    if data.get('format') != 1:
        return [f'{STAGES}: unsupported format {data.get("format")!r}']
    premises = defined_premises(root)
    ci = (root / CI).read_text(encoding='utf-8')
    seen, cited = set(), set()

    def exists(where, rel):
        if not isinstance(rel, str) or not rel or not (root / rel).exists():
            problems.append(f'{where}: missing file {rel!r}')
            return False
        return True

    for stage in data.get('stages', []):
        sid = stage.get('id')
        where = f'stage {sid!r}'
        if sid in seen:
            problems.append(f'{where}: duplicate stage')
        seen.add(sid)
        cls = stage.get('class')
        if cls not in CLASSES:
            problems.append(f'{where}: class {cls!r} is not one of {sorted(CLASSES)}')
        for key in ('name', 'summary'):
            if not stage.get(key):
                problems.append(f'{where}: missing {key}')
        ids = stage.get('premises') or []
        if not ids:
            problems.append(f'{where}: cites no premise')
        for pid in ids:
            if pid not in premises:
                problems.append(f'{where}: premise {pid} is not defined in {PREMISES}')
        cited.update(ids)
        if cls == 'kernel-checked' and 'TRU-01' not in ids:
            problems.append(f'{where}: kernel-checked stage must cite its trusted base TRU-01')
        checks = stage.get('checks') or []
        if cls in ('kernel-checked', 'independently-checked-metadata') and not checks:
            problems.append(f'{where}: {cls} stage cites no checker and test')
        if cls == 'unverified-assumption' and checks:
            problems.append(f'{where}: unverified-assumption stage lists checks; reclassify it')
        if not stage.get('components'):
            problems.append(f'{where}: lists no components')
        for rel in stage.get('components', []) + stage.get('evidence', []):
            exists(where, rel)
        for n, check in enumerate(checks):
            here = f'{where} check {n}'
            if not check.get('what'):
                problems.append(f'{here}: missing what')
            exists(here, check.get('checker'))
            test_ok = exists(here, check.get('test'))
            commands = check.get('ci') or []
            if not commands:
                problems.append(f'{here}: names no CI command')
            for command in commands:
                if command not in ci:
                    problems.append(f'{here}: CI command {command!r} is not in {CI}')
            if test_ok and not runs_in_ci(check['test'], ci, commands, root):
                problems.append(f'{here}: test {check["test"]} is not run by CI')
    for sid in REQUIRED:
        if sid not in seen:
            problems.append(f'stage {sid!r}: required pipeline stage is missing')
    for pid in sorted(p for p in premises if p.startswith('TRU-')):
        if pid not in cited:
            problems.append(f'{pid}: compiler/tool trust premise is cited by no stage')
    return problems


def runs_in_ci(test, ci, commands, root):
    """The test is named by CI, or by a script that one of the check's CI commands names."""
    if test in ci:
        return True
    for command in commands:
        if command not in ci:
            continue
        for token in command.split():
            path = root / token
            if path.is_file() and test in path.read_text(encoding='utf-8', errors='replace'):
                return True
    return False


def cell(text):
    return str(text).replace('|', '\\|')


def render(data):
    stages = data['stages']
    lines = [
        '# Pipeline trust report (V03)',
        '',
        '<!-- Generated by scripts/trust-report.py from assurance/trust-stages.json; do not edit. -->',
        '',
        'Every stage between Zig source and a kernel-checked theorem, with one class each. Premise IDs',
        'are defined in [premises.md](premises.md). Regenerate with `python3 scripts/trust-report.py write`;',
        'CI runs `python3 scripts/trust-report.py check`, which also fails on a missing stage, class,',
        'premise, checker or test, or a check whose test CI does not run.',
        '',
        '| Class | Meaning |',
        '|---|---|',
    ]
    lines += [f'| `{name}` | {meaning} |' for name, meaning in CLASSES.items()]
    lines += ['', '## Stages', '', '| Stage | Class | Premises | Checker / test |', '|---|---|---|---|']
    for stage in stages:
        checks = '<br>'.join(f'`{c["checker"]}` / `{c["test"]}`' for c in stage.get('checks', [])) or '—'
        lines.append(f'| {cell(stage["name"])} | `{stage["class"]}` | {", ".join(stage["premises"])} | {checks} |')
    for cls in CLASSES:
        group = [s for s in stages if s['class'] == cls]
        lines += ['', f'## {cls}', '']
        if not group:
            lines.append('No stage.')
        for stage in group:
            lines += [f'### {stage["name"]}', '', stage['summary'], '',
                      '- Components: ' + ', '.join(f'`{c}`' for c in stage['components']),
                      '- Premises: ' + ', '.join(f'[{p}](premises.md#{p.lower()})' for p in stage['premises'])]
            for check in stage.get('checks', []):
                lines.append(f'- Check: {check["what"]}: `{check["checker"]}`, tested by `{check["test"]}`'
                             f' (CI: ' + ', '.join(f'`{c}`' for c in check['ci']) + ')')
            if stage.get('evidence'):
                lines.append('- Further evidence (not a check of this stage): ' +
                             ', '.join(f'`{e}`' for e in stage['evidence']))
            lines.append('')
        if lines[-1] == '':
            lines.pop()
    return '\n'.join(lines) + '\n'


def main(argv=None, root=ROOT):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('mode', choices=['write', 'check'])
    args = parser.parse_args(argv)
    try:
        data = json.loads((root / STAGES).read_text(encoding='utf-8'))
        problems = validate(data, root)
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        print(f'trust-report: {error}', file=sys.stderr)
        return 2
    if problems:
        for problem in problems:
            print(f'trust-report: {problem}', file=sys.stderr)
        return 1
    text = render(data)
    report = root / REPORT
    if args.mode == 'write':
        report.write_text(text, encoding='utf-8')
        return 0
    current = report.read_text(encoding='utf-8') if report.is_file() else None
    if current != text:
        print(f'trust-report: {REPORT} is stale; run python3 scripts/trust-report.py write', file=sys.stderr)
        return 1
    print('trust report current')
    return 0


if __name__ == '__main__':
    sys.exit(main())
