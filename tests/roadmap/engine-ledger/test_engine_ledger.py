"""scripts/engine-ledger.py: rows, view, citations and the closed-row workaround rule."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("engine_ledger", ROOT / "scripts/engine-ledger.py")
el = importlib.util.module_from_spec(spec)
spec.loader.exec_module(el)


DIRS = []


def tearDownModule():
    for d in DIRS:
        d.cleanup()


def cite(*ids):
    """A citation as code writes it (built here so that this file is not itself a citation)."""
    return 'ledger ' + ', '.join('#' + i for i in ids)


def row(rid, status='open', sites=(), plan='', **kw):
    r = dict(id=rid, title='row ' + rid, status=status, requester='lane', progress='p', request='r',
             workaround_sites=list(sites), deletion_plan=plan)
    r.update(kw)
    return r


class Tree:
    """A scratch tree with a ledger and some source files; `generate` writes a fresh view."""

    def __init__(self, rows, files=None, view=True):
        self.dir = tempfile.TemporaryDirectory()
        DIRS.append(self.dir)
        self.root = Path(self.dir.name)
        (self.root / 'assurance').mkdir()
        (self.root / 'docs').mkdir()
        (self.root / el.DATA).write_text(json.dumps(dict(rows=rows)), encoding='utf-8')
        for name, text in (files or {}).items():
            p = self.root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text, encoding='utf-8')
        if view:
            try:
                el.cmd_generate(self.root)
            except KeyError:  # a malformed row (the schema tests); `check` reports it
                pass

    def problems(self):
        data = el.load(self.root)
        return el.problems_in_rows(data, self.root) + el.problems_in_citations(data, self.root)

    def check(self):
        return el.cmd_check(self.root)


class Rows(unittest.TestCase):
    def test_valid(self):
        t = Tree([row('1'), row('2', 'closed'), row('3', sites=['A.lean'], plan='delete it'),
                  row('pick-bind'), row('P09-E1'), row('20a')], {'A.lean': '-- x\n'})
        self.assertEqual(t.problems(), [])
        self.assertEqual(t.check(), 0)

    def test_duplicate_and_bad_ids(self):
        t = Tree([row('1'), row('1'), row('Bad Id')])
        text = '\n'.join(t.problems())
        self.assertIn('duplicate id', text)
        self.assertIn('bad id', text)

    def test_status_sites_and_plan(self):
        t = Tree([row('1', 'wip'), row('2', 'closed', sites=['A.lean']), row('3', sites=['A.lean']),
                  row('4', sites=['Missing.lean'], plan='p')], {'A.lean': ''})
        text = '\n'.join(t.problems())
        self.assertIn('status must be', text)
        self.assertIn('closed, but workaround sites remain', text)
        self.assertIn('no deletion_plan', text)
        self.assertIn('Missing.lean does not exist', text)

    def test_missing_field(self):
        r = row('1')
        del r['request']
        self.assertIn("missing field 'request'", '\n'.join(Tree([r]).problems()))

    def test_stale_view(self):
        t = Tree([row('1')])
        self.assertEqual(t.check(), 0)
        (t.root / el.VIEW).write_text('old\n', encoding='utf-8')
        self.assertEqual(t.check(), 1)
        t2 = Tree([row('1')], view=False)
        self.assertEqual(t2.check(), 1)


class Citations(unittest.TestCase):
    def rows(self):
        return [row('1'), row('2', 'closed'), row('20a'), row('pick-bind')]

    def test_existing_citations_pass(self):
        t = Tree(self.rows(), {
            'A.lean': f'-- ({cite("1")}) and engine {cite("2")}\n',
            'B.md': f'See {cite("20a")}; {cite("1")}/#2 and {cite("pick-bind")}.\n',
            'c.py': f'# {cite("1", "2")}\n'})
        self.assertEqual(t.problems(), [])

    def test_missing_row(self):
        t = Tree(self.rows(), {'A.lean': f'-- {cite("99")}\n', 'B.md': f'{cite("1")}/#98 and {cite("3")}\n'})
        text = '\n'.join(t.problems())
        for n in ('99', '98', '3'):
            self.assertIn(f'#{n}, which is not in', text)
        self.assertNotIn('#1,', text)

    def test_slash_list_and_row_word(self):
        t = Tree(self.rows(), {'A.lean': 'ledger rows ' + '#1, #2 and #7\n'})
        self.assertEqual(['A.lean:1: cites ledger row #7, which is not in ' + el.DATA], t.problems())

    def test_closed_row_as_workaround(self):
        t = Tree(self.rows(), {
            'A.lean': f'-- WORKAROUND ({cite("2")}): the step is applied by hand\n',
            'B.lean': f'-- a workaround for\n-- the missing rule\n-- ({cite("2")})\n',
            'C.lean': f'-- history only: fixed in {cite("2")}\n'})
        text = '\n'.join(t.problems())
        self.assertIn('A.lean:1: cites closed ledger row #2', text)
        self.assertIn('B.lean:3: cites closed ledger row #2', text)
        self.assertNotIn('C.lean', text)

    def test_open_row_as_workaround(self):
        t = Tree(self.rows(), {'A.lean': f'-- workaround, {cite("1")}\n'})
        self.assertEqual(t.problems(), [])

    def test_far_workaround_word_does_not_count(self):
        far = '-- workaround\n' + '--\n' * 4 + f'-- {cite("2")}\n'
        self.assertEqual(Tree(self.rows(), {'A.lean': far}).problems(), [])

    def test_other_file_kinds_and_the_view_are_not_scanned(self):
        t = Tree(self.rows(), {'a.txt': f'{cite("99")}\n', 'x/.lake/b.md': f'{cite("99")}\n'})
        self.assertEqual(t.problems(), [])
        (t.root / el.VIEW).write_text(f'{cite("99")}\n', encoding='utf-8')
        self.assertEqual(t.problems(), [])


class RealLedger(unittest.TestCase):
    def test_rows_are_well_formed(self):
        data = el.load(ROOT)
        self.assertEqual(el.problems_in_rows(data, ROOT), [])
        ids = [r['id'] for r in data['rows']]
        self.assertGreaterEqual(len(ids), 100)
        for known in ('1', '27', '62', '64', '71', 'pick-bind', 'P09-E1', 'T1'):
            self.assertIn(known, ids)


if __name__ == '__main__':
    unittest.main()
