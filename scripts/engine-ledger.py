#!/usr/bin/env python3
"""The fsym engine ledger as data: assurance/engine-ledger.json (rows) -> docs/engine-ledger.md (view).

A row is an engine feature or fix that a proof or a library needed and `fsym` did not (yet) provide,
with the workaround sites that stand in for it. CLAUDE.md ("One proof framework") requires a recorded
deletion plan for every transitional item; for an engine gap this file is that record. Code cites a
row as ledger `<slug-id>` or `ledger #<id>` (also lists after "ledger rows"); the gate below resolves
every citation, including unknown slugs.

  generate [--root R]   render docs/engine-ledger.md from the JSON
  check    [--root R] [--base REV]   validate against origin/main (or REV) and check the view/citations

Row (assurance/engine-ledger.json, "rows"):
    id                 existing ids stay valid; new ids are lower-case hyphenated slugs; unique
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
  * new ids are descriptive slugs (e.g. "pick-bind"), never the next number; merged id/title pairs
    are stable, so an independently added row cannot reuse an id under another title;
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
NUMERIC_ID = r'[0-9]+[a-z]?|[A-Z][0-9]+(?:-[A-Z][0-9]+)?|P[0-9]+-E[0-9]+'
SLUG_ID = r'[a-z][a-z0-9]*(?:-[a-z0-9]+)+'
ROW_ID = re.compile(rf'(?:{NUMERIC_ID})|[a-z][a-z0-9]*(?:-[a-z0-9]+)*')
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


def problems_against_base(data, root, base='origin/main'):
    """Keep merged row identities stable, even after the PR merges its base branch.

    Scratch trees outside Git can still check the schema/view/citations. A Git checkout must
    have its base ledger available: silently skipping it would disable the collision gate.
    """
    git = ['git', '-C', str(root)]
    if subprocess.run(git + ['rev-parse', '--show-toplevel'], capture_output=True).returncode:
        if os.path.lexists(Path(root) / '.git'):
            return [f'{DATA}: cannot inspect Git checkout; restore its .git metadata before checking ledger ids']
        return []
    result = subprocess.run(git + ['show', f'{base}:{DATA}'], capture_output=True, text=True)
    if result.returncode:
        return [f'{DATA}: cannot read {base}:{DATA}; fetch the base branch before checking ledger ids']
    try:
        before = {r['id']: r for r in json.loads(result.stdout)['rows']}
    except (ValueError, KeyError, TypeError):
        return [f'{DATA}: malformed ledger at {base}']
    out = []
    for row in data.get('rows', []):
        rid = row.get('id', '')
        old = before.get(rid)
        if old is not None and row.get('title') != old.get('title'):
            out.append(f'{DATA}: id {rid!r} already belongs to {old.get("title")!r} on {base}, '
                       f'not {row.get("title")!r}; keep merged id/title pairs stable, or choose a fresh slug '
                       'for a different request and update its citations')
        elif old is None and isinstance(rid, str) and not re.fullmatch(SLUG_ID, rid):
            out.append(f'{DATA}: new id {rid!r} must be a lower-case hyphenated slug (e.g. "pick-bind"); '
                       'legacy numeric ids are frozen')
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


def citation_regex():
    # An id is marked, `#id` or `` `id` ``, so hyphenated prose ("ledger self-check") is not a citation.
    # Parse unknown ids too: building the pattern from the ledger would hide dangling citations.
    rid = rf'(?:{NUMERIC_ID}|[a-z][a-z0-9]*(?:-[a-z0-9]+)*)'
    one = rf'(?:#{rid}(?![\w-])|`#?{rid}`)'
    return re.compile(r'\b(?i:ledger\s+(?:rows?\s+)?)(%s(?:\s*(?:/|,\s*and|,|and|&)\s*%s)*)' % (one, one)), \
        re.compile(rf'(?<=[#`]){rid}(?![\w-])')


def citations(root):
    """Yield (path, line number, row id, workaround-nearby) for every citation in the tracked files."""
    cite, one = citation_regex()
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
                    yield rel, i + 1, rid, bool(WORKAROUND.search(near))


def problems_in_citations(data, root):
    rows = {r['id']: r for r in data.get('rows', []) if 'id' in r}
    out = []
    for rel, ln, rid, workaround in citations(root):
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
         '`ledger #<id>` (or ledger `` `<id>` ``), and `scripts/engine-ledger.py check` (preflight)',
         'fails on a citation of a row that does not exist and on a closed row cited as a workaround that is still',
         f'there. Data and rules: `assurance/engine-ledger.json`, `scripts/engine-ledger.py`. {len(rows)} rows, {n_open} open.',
         '',
         'A row closes when the engine part has landed and no workaround for it is left in the tree. A PR that adds',
         'a workaround adds or cites the row in the same PR; a PR that deletes the last workaround closes the row.',
         'New rows use descriptive lower-case hyphenated slug ids, such as `pick-bind`; never take the next number.',
         'Existing ids and citations stay valid, including `20a`, `21a`, `68d`, `69d`, `70d`, `P09-E1` and `T1`.',
         'After fetching and merging `origin/main`, run `generate`, then `check`. The check rejects duplicate ids,',
         'new numeric ids, and an id whose title differs from `origin/main` (override with `check --base REV`).',
         'Merged id/title pairs are stable: update progress/request text to refine a row; use a fresh slug and',
         'update its citations for a different request. Two PRs can choose slugs independently; if they choose the',
         'same slug for different titles, preflight fails even after merging main. No shared counter is needed.', '',
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


def cmd_check(root, base='origin/main'):
    data = load(root)
    out = problems_in_rows(data, root)
    if not out:
        out += problems_against_base(data, root, base)
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
    ap.add_argument('--base', default='origin/main', help='base ledger for id collision checks (default: origin/main)')
    a = ap.parse_args()
    return cmd_generate(a.root) if a.command == 'generate' else cmd_check(a.root, a.base)


if __name__ == '__main__':
    sys.exit(main())
