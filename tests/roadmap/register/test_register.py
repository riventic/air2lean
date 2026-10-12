#!/usr/bin/env python3
"""Offline regressions for scripts/register.py: generation, drift, the markdown converter."""
import contextlib
import io
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
REG = runpy.run_path(str(ROOT / 'scripts/register.py'))
MARKER = re.compile(r'<!-- /?register:[a-z:-]+ -->\n?')


def run(*args):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = REG['main'](list(map(str, args)))
    return code, out.getvalue() + err.getvalue()


def legacy(text):
    """A document as it was before the register was data: the generated markers removed."""
    return MARKER.sub('', text)


ROADMAP = '''# Roadmap
The register has <!-- register:counts -->**x**<!-- /register:counts -->; <!-- register:incomplete -->0<!-- /register:incomplete --> remain.

<!-- register:table:begin -->
stale
<!-- register:table:end -->
tail
'''
ACCEPTANCE = '''# Acceptance
All <!-- register:total -->0<!-- /register:total --> IDs: <!-- register:counts-plain -->x<!-- /register:counts-plain -->.

<!-- register:acceptance:begin -->
stale
<!-- register:acceptance:end -->
'''
FILES = {
    'T01': ('Profiles', 'complete', 'done', 'Keep it so.'),
    'L02': ('Bit operations', 'partial', 'more', 'Needs work.\n\nSecond paragraph with `---` below.\n\n---\n\nend'),
    'X01': ('C programs', 'open', 'none yet', 'Open.'),
}


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding='utf-8')


def write_req(root, rid, title, status, row, body):
    write(root / 'assurance/register' / f'{rid}.md', f'id: {rid}\ntitle: {title}\nstatus: {status}\nrow: {row}\n---\n{body}\n')


class Scratch(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='air2lean-register-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        write(self.root / 'ROADMAP.md', ROADMAP)
        write(self.root / 'remaining-acceptance.md', ACCEPTANCE)
        for rid, fields in FILES.items():
            write_req(self.root, rid, *fields)

    def text(self, rel):
        return (self.root / rel).read_text(encoding='utf-8')


class Generate(Scratch):
    def test_generate_renders_in_area_order_with_counts(self):
        self.assertEqual(run('check', '--root', self.root)[0], 1)
        self.assertEqual(run('generate', '--root', self.root)[0], 0)
        roadmap = self.text('ROADMAP.md')
        self.assertIn('<!-- register:counts -->**3 requirements: 1 complete, 1 partial, 1 open and 0 research**<!-- /register:counts -->; '
                      '<!-- register:incomplete -->2<!-- /register:incomplete --> remain.', roadmap)
        rows = re.findall(r'^\| (\w+) \| ([^|]+) \| (\w+) \| (.*) \|$', roadmap, re.M)
        self.assertEqual(rows[1:], [('T01', 'Profiles', 'complete', 'done'), ('L02', 'Bit operations', 'partial', 'more'),
                                ('X01', 'C programs', 'open', 'none yet')])
        self.assertTrue(roadmap.endswith('|\n<!-- register:table:end -->\ntail\n'))
        acceptance = self.text('remaining-acceptance.md')
        self.assertIn('All <!-- register:total -->3<!-- /register:total --> IDs: '
                      '<!-- register:counts-plain -->1 complete, 1 partial, 1 open and 0 research<!-- /register:counts-plain -->.',
                      acceptance)
        self.assertIn('## L02 — Bit operations\n\nClassification: partial.\n\nNeeds work.', acceptance)
        self.assertEqual(run('check', '--root', self.root)[0], 0)

    def test_generate_is_idempotent(self):
        run('generate', '--root', self.root)
        before = (self.text('ROADMAP.md'), self.text('remaining-acceptance.md'))
        self.assertEqual(run('generate', '--root', self.root), (0, ''))
        self.assertEqual(before, (self.text('ROADMAP.md'), self.text('remaining-acceptance.md')))

    def test_editing_one_requirement_changes_only_its_lines(self):
        run('generate', '--root', self.root)
        before = self.text('ROADMAP.md').splitlines()
        write_req(self.root, 'L02', 'Bit operations', 'complete', 'more, done', 'Needs work.')
        self.assertEqual(run('check', '--root', self.root)[0], 1)
        run('generate', '--root', self.root)
        changed = [(a, b) for a, b in zip(before, self.text('ROADMAP.md').splitlines()) if a != b]
        self.assertEqual([a.split(' | ')[0] for a, _ in changed][1:], ['| L02'])  # counts line, then the row
        self.assertIn('2 complete, 0 partial', self.text('ROADMAP.md'))

    def test_hand_edit_of_generated_region_is_drift(self):
        run('generate', '--root', self.root)
        write(self.root / 'ROADMAP.md', self.text('ROADMAP.md').replace('| more |', '| edited |'))
        code, output = run('check', '--root', self.root)
        self.assertEqual(code, 1)
        self.assertIn('ROADMAP.md: generated register region is stale', output)

    def test_missing_marker_is_an_error(self):
        write(self.root / 'ROADMAP.md', '# no markers\n')
        code, output = run('generate', '--root', self.root)
        self.assertEqual(code, 1)
        self.assertIn('register:table:begin/end', output)

    def test_malformed_files_are_rejected(self):
        bad = {
            'unknown status': 'id: T01\ntitle: A\nstatus: done\nrow: r\n---\nb\n',
            'pipe in title': 'id: T01\ntitle: A|B\nstatus: open\nrow: r\n---\nb\n',
            'id mismatch': 'id: T02\ntitle: A\nstatus: open\nrow: r\n---\nb\n',
            'missing field': 'id: T01\ntitle: A\nstatus: open\n---\nb\n',
            'no separator': 'id: T01\ntitle: A\nstatus: open\nrow: r\n',
        }
        for name, text in bad.items():
            with self.subTest(name):
                write(self.root / 'assurance/register/T01.md', text)
                self.assertEqual(run('check', '--root', self.root)[0], 1)


class Converter(Scratch):
    def test_committed_register_round_trips_through_the_markdown_converter(self):
        """The migration proof: the committed documents without markers (the pre-register form)
        convert into exactly the committed register files, and generate puts the markers' content
        back byte for byte."""
        docs = {rel: (ROOT / rel).read_text(encoding='utf-8') for rel in ('ROADMAP.md', 'remaining-acceptance.md')}
        scratch = self.root / 'migration'
        for rel, text in docs.items():
            write(scratch / rel, legacy(text))
        self.assertEqual(run('import', '--root', scratch)[0], 0)
        committed = sorted((ROOT / 'assurance/register').glob('*.md'))
        self.assertEqual(sorted(p.name for p in (scratch / 'assurance/register').glob('*.md')), [p.name for p in committed])
        for path in committed:
            self.assertEqual((scratch / 'assurance/register' / path.name).read_bytes(), path.read_bytes(), path.name)
        for rel, text in docs.items():
            write(scratch / rel, text)
        self.assertEqual(run('check', '--root', scratch)[0], 0)

    def test_legacy_tables_convert_and_regenerate_identically(self):
        run('generate', '--root', self.root)
        marked = {rel: self.text(rel) for rel in ('ROADMAP.md', 'remaining-acceptance.md')}
        shutil.rmtree(self.root / 'assurance')
        for rel, text in marked.items():
            write(self.root / rel, legacy(text))
        self.assertEqual(run('import', '--root', self.root)[0], 0)
        self.assertEqual(REG['load'](self.root)[1]['acceptance'], FILES['L02'][3])
        for rel, text in marked.items():
            write(self.root / rel, text)
        self.assertEqual(run('check', '--root', self.root)[0], 0)

    def test_import_from_git_writes_only_what_the_branch_changed(self):
        run('generate', '--root', self.root)

        def git(*args):
            return subprocess.run(['git', '-C', self.root, '-c', 'user.name=t', '-c', 'user.email=t@t', *args],
                                  check=True, capture_output=True, text=True).stdout.strip()
        git('init', '-q')
        for rel in ('ROADMAP.md', 'remaining-acceptance.md'):
            write(self.root / rel, legacy(self.text(rel)))
        git('add', 'ROADMAP.md', 'remaining-acceptance.md')
        git('commit', '-qm', 'base')
        base = git('rev-parse', 'HEAD')
        # The branch edits the markdown directly: L02's row and acceptance, and adds Q01.
        road = self.text('ROADMAP.md').replace('| more |', '| more, then done |')
        road += '| Q01 | Fuzzing | partial | fuzzed |\n'
        acc = self.text('remaining-acceptance.md').replace('Needs work.', 'Needs less work.')
        acc += '\n## Q01 — Fuzzing\n\nClassification: partial.\n\nFuzz it.\n'
        write(self.root / 'ROADMAP.md', road)
        write(self.root / 'remaining-acceptance.md', acc)
        git('commit', '-qam', 'branch')
        # Meanwhile "main" changed X01 in the register; the import must not revert it.
        write_req(self.root, 'X01', 'C programs', 'partial', 'main moved on', 'Open.')
        self.assertEqual(run('import', '--root', self.root, '--from', 'HEAD', '--base', base)[0], 0)
        recs = {r['id']: r for r in REG['load'](self.root)}
        self.assertEqual(recs['L02']['row'], 'more, then done')
        self.assertTrue(recs['L02']['acceptance'].startswith('Needs less work.'))
        self.assertEqual(recs['Q01']['row'], 'fuzzed')
        self.assertEqual(recs['Q01']['acceptance'], 'Fuzz it.')
        self.assertEqual(recs['X01']['row'], 'main moved on')
        self.assertEqual(recs['T01']['row'], 'done')

    def test_section_that_disagrees_with_the_table_is_rejected(self):
        road = '| T01 | Profiles | complete | done |\n'
        acc = '## T01 — Profiles\n\nClassification: partial.\n\nbody\n'
        with self.assertRaisesRegex(ValueError, 'disagrees'):
            REG['parse_markdown'](road, acc)


if __name__ == '__main__':
    unittest.main()
