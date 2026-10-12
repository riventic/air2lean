#!/usr/bin/env python3
"""The requirement register as data: assurance/register/<ID>.md, one file per requirement.

ROADMAP.md (the register table and counts) and remaining-acceptance.md (the per-requirement
acceptance sections) are generated from these files between marker comments; everything outside
the markers stays hand-written. Two PRs that change different requirements touch different files
and never conflict.

  generate [--root R]   render the marked regions of both documents
  check    [--root R]   exit 1 when a document differs from what `generate` would write
  import   [--root R] [--from REF [--base REF]]
                        (re)build register files from the markdown tables/sections; see below

Register file (assurance/register/T01.md):

    id: T01
    title: Explicit target and build profiles
    status: complete            # complete | partial | open | research
    row: <one line: the "Bounded status and remaining scope" cell of the ROADMAP.md table>
    ---
    <acceptance text, verbatim markdown: the body of the "## T01 - ..." section of
    remaining-acceptance.md after its "Classification:" line>

Order in the documents is fixed: area (the ID's letter, in AREAS order), then number.

`import` is the converter for a branch that still edits the markdown rows directly (kept until
the PRs opened before this register merge). With no options it reads ROADMAP.md and
remaining-acceptance.md of the working tree. With `--from REF --base REF` it reads both versions
from git and writes only the requirements the branch changed relative to the base:

    git merge origin/main                       # conflicts in the two markdown files
    scripts/register.py import --from HEAD --base "$(git merge-base HEAD origin/main)"
    git checkout origin/main -- ROADMAP.md remaining-acceptance.md
    scripts/register.py generate && git add -A && git commit
"""
import argparse
import collections
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
REGISTER_DIR = 'assurance/register'
STATUSES = ('complete', 'partial', 'open', 'research')
AREAS = 'TLCMFAEPIVQDX'
FIELDS = ('id', 'title', 'status', 'row')
ID = re.compile(r'[A-Z]\d\d')

ROADMAP = 'ROADMAP.md'
ACCEPTANCE = 'remaining-acceptance.md'
TABLE_HEADER = '| ID | Requirement | Status | Bounded status and remaining scope |\n|---|---|---|---|'
ROW = re.compile(r'^\| ([A-Z]\d\d) \| ([^|]+) \| (\w+) \| (.*) \|$', re.M)
SECTION = re.compile(r'^## ([A-Z]\d\d) — ([^\n]*)\n\nClassification: (\w+)\.\n\n(.*?)(?=^## [A-Z]\d\d — |\Z)',
                     re.M | re.S)
SECTION_START = re.compile(r'^## [A-Z]\d\d — ', re.M)
COMMENT = re.compile(r'<!-- /?register:[a-z:-]+ -->\n?')


def sort_key(rid):
    return AREAS.index(rid[0]), int(rid[1:])


def parse_file(path):
    head, sep, body = Path(path).read_text(encoding='utf-8').partition('\n---\n')
    if not sep:
        raise ValueError(f'{path}: no "---" line after the header')
    rec = {}
    for line in head.splitlines():
        key, colon, value = line.partition(': ')
        if not colon or key not in FIELDS or key in rec:
            raise ValueError(f'{path}: bad header line {line!r}')
        rec[key] = value
    if sorted(rec) != sorted(FIELDS):
        raise ValueError(f'{path}: header must have exactly {", ".join(FIELDS)}')
    rec['acceptance'] = body.rstrip('\n')
    return rec


def validate(rec, source):
    if not ID.fullmatch(rec['id']) or rec['id'][0] not in AREAS:
        raise ValueError(f'{source}: bad requirement ID {rec["id"]!r}')
    if rec['status'] not in STATUSES:
        raise ValueError(f'{source}: {rec["id"]} has unknown status {rec["status"]!r}')
    if '|' in rec['title'] or not rec['title'] or rec['title'] != rec['title'].strip():
        raise ValueError(f'{source}: {rec["id"]} has a bad title')
    if not rec['row'] or rec['row'] != rec['row'].strip():
        raise ValueError(f'{source}: {rec["id"]} has an empty or unstripped row')
    if SECTION_START.search(rec.get('acceptance', '')):
        raise ValueError(f'{source}: {rec["id"]} acceptance text has a line that starts a "## <ID> — " section')


def load(root=ROOT):
    """Ordered list of {'id','title','status','row','acceptance'} for the whole register."""
    directory = Path(root) / REGISTER_DIR
    recs = []
    for path in sorted(directory.glob('*.md')):
        rec = parse_file(path)
        if path.stem != rec['id']:
            raise ValueError(f'{path}: id {rec["id"]!r} does not match the file name')
        validate(rec, path)
        recs.append(rec)
    if not recs:
        raise ValueError(f'{directory}: requirement register not found')
    return sorted(recs, key=lambda r: sort_key(r['id']))


def counts(recs):
    n = collections.Counter(r['status'] for r in recs)
    return (f'{n["complete"]} complete, {n["partial"]} partial, '
            f'{n["open"]} open and {n["research"]} research')


def inline_values(recs):
    done = sum(r['status'] == 'complete' for r in recs)
    return {
        'counts': f'**{len(recs)} requirements: {counts(recs)}**',
        'counts-plain': counts(recs),
        'total': str(len(recs)),
        'incomplete': str(len(recs) - done),
    }


def render_table(recs):
    return '\n'.join([TABLE_HEADER] + [f'| {r["id"]} | {r["title"]} | {r["status"]} | {r["row"]} |' for r in recs])


def render_acceptance(recs):
    return '\n'.join(f'## {r["id"]} — {r["title"]}\n\nClassification: {r["status"]}.\n\n{r["acceptance"]}\n'
                     for r in recs).rstrip('\n')


def replace_region(text, name, content, source):
    pattern = re.compile(rf'(<!-- register:{name}:begin -->\n).*?(\n<!-- register:{name}:end -->)', re.S)
    if len(pattern.findall(text)) != 1:
        raise ValueError(f'{source}: needs exactly one register:{name}:begin/end marker pair')
    return pattern.sub(lambda m: m.group(1) + content + m.group(2), text)


def replace_inline(text, values, used):
    for name, value in values.items():
        pattern = re.compile(rf'(<!-- register:{name} -->).*?(<!-- /register:{name} -->)')
        text, n = pattern.subn(lambda m: m.group(1) + value + m.group(2), text)
        used[name] += n
    return text


def render_documents(root, recs):
    """{relative path: text the document must have}."""
    values = inline_values(recs)
    out = {}
    used = collections.Counter()
    for rel, name, content in ((ROADMAP, 'table', render_table(recs)),
                               (ACCEPTANCE, 'acceptance', render_acceptance(recs))):
        text = (Path(root) / rel).read_text(encoding='utf-8')
        out[rel] = replace_inline(replace_region(text, name, content, rel), values, used)
    for name in values:
        if not used[name]:
            raise ValueError(f'no <!-- register:{name} --><!-- /register:{name} --> marker pair in {ROADMAP} or {ACCEPTANCE}')
    return out


def generate(root):
    for rel, text in render_documents(root, load(root)).items():
        path = Path(root) / rel
        if path.read_text(encoding='utf-8') != text:
            path.write_text(text, encoding='utf-8')
            print(f'updated {rel}')


def check(root):
    stale = [rel for rel, text in render_documents(root, load(root)).items()
             if (Path(root) / rel).read_text(encoding='utf-8') != text]
    for rel in stale:
        print(f'{rel}: generated register region is stale; run scripts/register.py generate', file=sys.stderr)
    if not stale:
        print('register: documents match assurance/register')
    return 1 if stale else 0


def parse_markdown(roadmap, acceptance):
    """{id: record} from the markdown tables/sections (marked or legacy unmarked)."""
    recs = {}
    for rid, title, status, row in ROW.findall(roadmap):
        recs[rid] = {'id': rid, 'title': title.strip(), 'status': status, 'row': row}
    seen = set()
    for rid, title, status, body in SECTION.findall(acceptance):
        rec = recs.get(rid)
        if rec is None or rec['title'] != title or rec['status'] != status:
            raise ValueError(f'{ACCEPTANCE}: section {rid} disagrees with the {ROADMAP} table (title/classification)')
        rec['acceptance'] = COMMENT.sub('', body).rstrip('\n')
        seen.add(rid)
    if set(recs) != seen:
        raise ValueError(f'{ACCEPTANCE}: sections differ from table IDs: {sorted(set(recs) ^ seen)}')
    for rec in recs.values():
        validate(rec, 'markdown')
    return recs


def git_show(root, ref, rel):
    return subprocess.run(['git', '-C', str(root), 'show', f'{ref}:{rel}'], check=True,
                          capture_output=True, text=True).stdout


def read_markdown(root, ref):
    if ref is None:
        return parse_markdown(*((Path(root) / rel).read_text(encoding='utf-8') for rel in (ROADMAP, ACCEPTANCE)))
    return parse_markdown(git_show(root, ref, ROADMAP), git_show(root, ref, ACCEPTANCE))


def write_record(root, rec):
    path = Path(root) / REGISTER_DIR / f'{rec["id"]}.md'
    path.parent.mkdir(parents=True, exist_ok=True)
    header = ''.join(f'{key}: {rec[key]}\n' for key in FIELDS)
    text = f'{header}---\n{rec["acceptance"]}\n'
    if not path.exists() or path.read_text(encoding='utf-8') != text:
        path.write_text(text, encoding='utf-8')
        return True
    return False


def import_markdown(root, source=None, base=None):
    recs = read_markdown(root, source)
    old = read_markdown(root, base) if base else {}
    changed = [rid for rid in sorted(recs, key=sort_key) if recs[rid] != old.get(rid)]
    for rid in changed:
        path = Path(root) / REGISTER_DIR / f'{rid}.md'
        if rid in old and path.exists() and parse_file(path) not in (old[rid], recs[rid]):
            print(f'import: warning: {rid} changed both on the branch and in {REGISTER_DIR}; the branch version wins',
                  file=sys.stderr)
    written = [rid for rid in changed if write_record(root, recs[rid])]
    print(f'import: {len(recs)} requirements read, {len(changed)} differ from the base, '
          f'{len(written)} register files written' + (': ' + ' '.join(written) if written else ''))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('command', choices=('generate', 'check', 'import'))
    ap.add_argument('--root', type=Path, default=ROOT)
    ap.add_argument('--from', dest='source', help='git ref holding the markdown to import (default: working tree)')
    ap.add_argument('--base', help='git ref of the common ancestor: import only what differs from it')
    args = ap.parse_args(argv)
    if args.base and not args.source:
        ap.error('--base needs --from')
    try:
        if args.command == 'import':
            import_markdown(args.root, args.source, args.base)
            return 0
        if args.command == 'generate':
            generate(args.root)
            return 0
        return check(args.root)
    except (ValueError, OSError, subprocess.CalledProcessError) as e:
        print(f'register: {e}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
