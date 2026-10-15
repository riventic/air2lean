#!/usr/bin/env python3
"""The fsym engine ledger as data: assurance/engine-ledger.json (rows) -> docs/engine-ledger.md (view).

A row is an engine feature or fix that a proof or a library needed and `fsym` did not (yet) provide,
with the workaround sites that stand in for it. CLAUDE.md ("One proof framework") requires a recorded
deletion plan for every transitional item; for an engine gap this file is that record. Code cites a
row as `ledger #62` / `engine ledger #62` (or `#62` after "ledger rows"); the gate below resolves
every citation.

  generate [--root R]   render docs/engine-ledger.md from the JSON
  check    [--root R]   exit 1 on a malformed row, a stale view, or a bad citation (see Gate)

Row (assurance/engine-ledger.json, "rows"):
    id                 "62", "20a", "P09-E1", "T1", or a slug ("pick-bind"); unique
    title              one line
    status             open | closed. A row closes when the engine part has landed AND no workaround
                       for it is left in the tree
    requester          the lane or agent that asked
    progress           the status text as the lane last wrote it (history, not interpreted)
    request            the request, verbatim
    workaround_sites   files that still carry a workaround for the row (existing paths)
    deletion_plan      what is deleted once the row closes; required when workaround_sites is not empty
    note               optional (renumbering, evidence for a status)

Gate (`check`):
  * schema: fields, unique ids, status, sites exist, an open row with sites has a deletion plan,
    a closed row has no sites;
  * the view docs/engine-ledger.md is what `generate` writes;
  * every citation in a tracked .lean/.md/.py file names an existing row;
  * a closed row is not cited near the word "workaround" (the line and two lines either side): the
    workaround is still there, so the row is not closed.

Editing: a PR that adds an engine workaround adds the row (or cites the open one) in the same PR; a PR
that deletes the last workaround of a row sets it to closed, then runs `generate`.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
DATA = 'assurance/engine-ledger.json'
VIEW = 'docs/engine-ledger.md'
STATUSES = ('open', 'closed')
FIELDS = ('id', 'title', 'status', 'requester', 'progress', 'request', 'workaround_sites', 'deletion_plan')
ROW_ID = re.compile(r'[0-9]+[a-z]?|[A-Z][0-9]+(?:-[A-Z][0-9]+)?|P[0-9]+-E[0-9]+|[a-z][a-z0-9]*(?:-[a-z0-9]+)*')
NUMERIC_ID = r'[0-9]+[a-z]?|[A-Z][0-9]+(?:-[A-Z][0-9]+)?|P[0-9]+-E[0-9]+'
SKIP_DIRS = {'.git', '.lake', 'node_modules', '__pycache__'}
# The view and this file's own prose are not citations.
NOT_SCANNED = {VIEW}
WORKAROUND = re.compile(r'workaround', re.I)
RADIUS = 2


def load(root):
    path = Path(root) / DATA
    try:
        return json.loads(path.read_text(encoding='utf-8'))
    except (OSError, ValueError) as e:
        sys.exit(f'{DATA}: cannot read: {e}')


def problems_in_rows(data, root):
    out = []
    seen = set()
    for n, row in enumerate(data.get('rows', [])):
        rid = row.get('id', '')
        where = f'{DATA} row {n} ({rid!r})'
        for f in FIELDS:
            if f not in row:
                out.append(f'{where}: missing field {f!r}')
        if not isinstance(rid, str) or not ROW_ID.fullmatch(rid):
            out.append(f'{where}: bad id')
        if rid in seen:
            out.append(f'{where}: duplicate id')
        seen.add(rid)
        status = row.get('status')
        if status not in STATUSES:
            out.append(f'{where}: status must be one of {STATUSES}')
        sites = row.get('workaround_sites', [])
        if not isinstance(sites, list):
            out.append(f'{where}: workaround_sites must be a list')
            sites = []
        for s in sites:
            if not (Path(root) / s).is_file():
                out.append(f'{where}: workaround site {s} does not exist (delete it from the row)')
        if status == 'closed' and sites:
            out.append(f'{where}: closed, but workaround sites remain: {", ".join(sites)}')
        if status == 'open' and sites and not row.get('deletion_plan', '').strip():
            out.append(f'{where}: open with workaround sites and no deletion_plan')
        if not row.get('title', '').strip():
            out.append(f'{where}: empty title')
    return out


def tracked_files(root):
    try:
        r = subprocess.run(['git', '-C', str(root), 'ls-files', '-z'], capture_output=True, check=True)
        names = [n for n in r.stdout.decode('utf-8').split('\0') if n]
        # a worktree with deleted-but-tracked files must not crash the scan
        return [n for n in names if (Path(root) / n).is_file()]
    except (OSError, subprocess.CalledProcessError):
        pass
    names = []
    for dirpath, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in files:
            names.append(str((Path(dirpath) / f).relative_to(root)))
    return names


def citation_regex(slugs):
    one = '#(?:%s)' % '|'.join([NUMERIC_ID] + [re.escape(s) for s in sorted(slugs, key=len, reverse=True)])
    return re.compile(r'\bledger\s+(?:rows?\s+)?(%s(?:\s*(?:/|,|,\s*and|and|&)\s*%s)*)(?![\w-])' % (one, one), re.I), \
        re.compile(one)


def citations(root, slugs):
    """Yield (path, line number, row id, workaround-nearby) for every citation in the tracked files."""
    cite, one = citation_regex(slugs)
    for rel in tracked_files(root):
        if rel in NOT_SCANNED or not rel.endswith(('.lean', '.md', '.py')):
            continue
        try:
            lines = (Path(root) / rel).read_text(encoding='utf-8').split('\n')
        except (OSError, UnicodeDecodeError):
            continue
        for i, line in enumerate(lines):
            for m in cite.finditer(line):
                near = '\n'.join(lines[max(0, i - RADIUS):i + RADIUS + 1])
                for rid in one.findall(m.group(1)):
                    yield rel, i + 1, rid[1:], bool(WORKAROUND.search(near))


def problems_in_citations(data, root):
    rows = {r['id']: r for r in data.get('rows', []) if 'id' in r}
    out = []
    for rel, ln, rid, workaround in citations(root, [i for i in rows if not re.fullmatch(NUMERIC_ID, i)]):
        row = rows.get(rid)
        if row is None:
            out.append(f'{rel}:{ln}: cites ledger row #{rid}, which is not in {DATA}')
        elif row.get('status') == 'closed' and workaround:
            out.append(f'{rel}:{ln}: cites closed ledger row #{rid} as a workaround that still exists '
                       f'(reopen the row or delete the workaround)')
    return out


def md_cell(text):
    return text.replace('|', '\\|').replace('\n', ' ')


def render(data):
    rows = data['rows']
    n_open = sum(r['status'] == 'open' for r in rows)
    o = ['<!-- Generated from assurance/engine-ledger.json by scripts/engine-ledger.py generate; edit the JSON. -->',
         '# fsym engine ledger', '',
         'Engine features and fixes that proofs and libraries needed from `fsym`, and the workarounds that stand',
         'in for the missing ones. This is the recorded deletion plan that CLAUDE.md asks for: code cites a row as',
         '`ledger #62` (or `engine ledger #62`), and `scripts/engine-ledger.py check` (run by `scripts/preflight.sh`)',
         'fails on a citation of a row that does not exist and on a closed row cited as a workaround that is still',
         f'there. Data and rules: `assurance/engine-ledger.json`, `scripts/engine-ledger.py`. {len(rows)} rows, {n_open} open.',
         '',
         'A row closes when the engine part has landed and no workaround for it is left in the tree. A PR that adds',
         'a workaround adds or cites the row in the same PR; a PR that deletes the last workaround closes the row.',
         'Ids are the ledger numbers; the old handoff reused a few (`20a`, `21a`, `68d`, `69d`, `70d` are the second',
         'rows of a reused number), and rows without a number have a name (`pick-bind`).', '',
         '## Open rows', '',
         '| Row | Title | Requester | Workaround sites | Deletion plan |', '|---|---|---|---|---|']
    for r in rows:
        if r['status'] == 'open':
            sites = ', '.join(f'`{s}`' for s in r['workaround_sites']) or '-'
            o.append(f"| [{r['id']}](#row-{anchor(r['id'])}) | {md_cell(r['title'])} | {md_cell(r['requester'])} "
                     f"| {sites} | {md_cell(r['deletion_plan']) or '-'} |")
    o += ['', '## Closed rows', '', '| Row | Title | How it closed |', '|---|---|---|']
    for r in rows:
        if r['status'] == 'closed':
            o.append(f"| [{r['id']}](#row-{anchor(r['id'])}) | {md_cell(r['title'])} | {md_cell(r['progress'])} |")
    if data.get('mechanisms'):
        o += ['', '## Shared mechanisms', '',
              'Planning units of the engine lane (one PR each, regressions from every requester); the rows list what each closes.', '']
        for m in data['mechanisms']:
            o.append(f"- **{m['id']}** {m['text']}")
    o += ['', '## Rows', '']
    for r in rows:
        o += [f'<a id="row-{anchor(r["id"])}"></a>', f"### #{r['id']} {r['title']}", '',
              f"Status: **{r['status']}**. Requester: {r['requester']}.", '']
        if r.get('note'):
            o += [f"Note: {r['note']}", '']
        o += [f"Progress: {r['progress']}", '', f"Request: {r['request']}", '']
        if r['workaround_sites']:
            o += ['Workaround sites: ' + ', '.join(f'`{s}`' for s in r['workaround_sites']), '']
        if r['deletion_plan']:
            o += [f"Deletion plan: {r['deletion_plan']}", '']
    return '\n'.join(o).rstrip('\n') + '\n'


def anchor(rid):
    return rid.lower()


def cmd_generate(root):
    data = load(root)
    (Path(root) / VIEW).write_text(render(data), encoding='utf-8')
    return 0


def cmd_check(root):
    data = load(root)
    out = problems_in_rows(data, root)
    view = Path(root) / VIEW
    if not out and (not view.is_file() or view.read_text(encoding='utf-8') != render(data)):
        out.append(f'{VIEW} is stale; run scripts/engine-ledger.py generate')
    out += problems_in_citations(data, root)
    for p in out:
        print(p, file=sys.stderr)
    return 1 if out else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('command', choices=('generate', 'check'))
    ap.add_argument('--root', default=str(ROOT))
    a = ap.parse_args()
    return {'generate': cmd_generate, 'check': cmd_check}[a.command](a.root)


if __name__ == '__main__':
    sys.exit(main())
