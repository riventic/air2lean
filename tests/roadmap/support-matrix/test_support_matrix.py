#!/usr/bin/env python3
"""Offline support-matrix generation and agreement regressions; no Zig, Lake or Lean process."""
import contextlib
import io
from pathlib import Path
import re
import runpy
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
MATRIX = runpy.run_path(str(ROOT/'scripts/support-matrix.py'))


def run(*args):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = MATRIX['main'](list(map(str, args)))
    return code, out.getvalue() + err.getvalue()


def example_cells(doc, example):
    """{version: cell} of one row of the examples-by-version table; independent of how many
    versions are supported and in which order."""
    table = doc.split('## Examples by version')[1].split('\n## ')[0]
    header = next(line for line in table.splitlines() if line.startswith('| Example |'))
    versions = [c.strip() for c in header.strip('|').split('|')][1:]
    row = re.search(rf'^\| `{re.escape(example)}`[^|]*\|(.*)\|$', table, re.M)
    return dict(zip(versions, (c.strip() for c in row.group(1).split('|'))))


class Scratch(unittest.TestCase):
    """Each test edits a private copy of exactly the committed inputs."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='air2lean support matrix ')
        self.root = Path(self.temp.name)
        for rel in MATRIX['SOURCES']:
            (self.root/rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT/rel, self.root/rel)
        shutil.copytree(ROOT/'coverage', self.root/'coverage')
        for example in (ROOT/'examples').iterdir():
            if example.is_dir():
                (self.root/'examples'/example.name).mkdir(parents=True)
                versions = example/'zig-versions'
                if versions.exists():
                    shutil.copyfile(versions, self.root/'examples'/example.name/'zig-versions')

    def tearDown(self):
        self.temp.cleanup()

    def edit(self, rel, old, new, count=1):
        path = self.root/rel
        text = path.read_text(encoding='utf-8')
        self.assertIn(old, text, rel)
        path.write_text(text.replace(old, new, count), encoding='utf-8')

    def check(self):
        return run('check', '--root', self.root)

    def assertProblem(self, needle, code=1):
        status, output = self.check()
        self.assertEqual(status, code, output)
        self.assertIn(needle, output)


class Committed(Scratch):
    def test_committed_tree_is_current(self):
        status, output = run('check', '--root', ROOT)
        self.assertEqual(status, 0, output)
        self.assertIn('support matrix current', output)

    def test_generate_is_idempotent(self):
        before = {rel: (self.root/rel).read_text() for rel in MATRIX['REGIONS']}
        status, output = run('generate', '--root', self.root)
        self.assertEqual(status, 0, output)
        self.assertEqual(output, '')
        self.assertEqual(before, {rel: (self.root/rel).read_text() for rel in MATRIX['REGIONS']})

    def test_matrix_reflects_register_and_selection(self):
        doc = (ROOT/'docs/support-matrix.md').read_text()
        threadsync, asm = example_cells(doc, 'threadsync'), example_cells(doc, 'asm')
        self.assertEqual([threadsync[v] for v in ('0.16.0', '0.15.2', '0.14.1')], ['—', 'yes', '—'])
        self.assertEqual([asm[v] for v in ('0.16.0', '0.15.2', '0.14.1')], ['yes', 'yes', '—'])
        self.assertIn('| `asm` (x86_64 only) |', doc)
        self.assertIn('| D: Documentation | D01, D02, D03, D04 | — | — | — |', doc)
        # No complete requirement is listed as open work, and every register ID appears once.
        region = doc.split(MATRIX['begin']('matrix'))[1].split(MATRIX['end']('matrix'))[0]
        table = region.split('## Requirement register')[1]
        for row in MATRIX['register'](ROOT):
            self.assertEqual(table.count(row['id']), 1, row['id'])


class Stale(Scratch):
    def test_hand_edit_of_region_is_stale(self):
        path = self.root/'docs/support-matrix.md'
        text = path.read_text(encoding='utf-8')
        edited = re.sub(r'^(\| `basic` \|.*)\| yes \|$', r'\1| — |', text, count=1, flags=re.M)
        self.assertNotEqual(edited, text)
        path.write_text(edited, encoding='utf-8')
        self.assertProblem('docs/support-matrix.md: generated region is stale')

    def test_example_selection_change_is_stale_until_regenerated(self):
        (self.root/'examples/vectors/zig-versions').write_text('0.16.0\n')
        self.assertProblem('README.md: generated region is stale')
        status, output = run('generate', '--root', self.root)
        self.assertEqual(status, 0, output)
        self.assertIn('updated PLAN.md', output)
        self.assertEqual(self.check()[0], 0)
        cells = example_cells((self.root/'docs/support-matrix.md').read_text(), 'vectors')
        self.assertEqual(cells, {v: 'yes' if v == '0.16.0' else '—' for v in cells})

    def test_register_status_change_is_stale(self):
        self.edit('ROADMAP.md', '| Q01 | Generated program and parser fuzzing | partial |',
                  '| Q01 | Generated program and parser fuzzing | complete |')
        self.assertProblem('docs/support-matrix.md: generated region is stale')
        reg = MATRIX['register'](self.root)
        complete = sum(row['status'] == 'complete' for row in reg)
        self.assertProblem(f'ROADMAP.md header does not state **{len(reg)} requirements: '
                           f'{complete} complete')

    def test_coverage_change_is_stale(self):
        path = self.root/'coverage/0.15.2.json'
        path.write_text(path.read_text().replace('"translation-rejected"', '"recognized-model-boundary"', 1))
        self.assertProblem('docs/support-matrix.md: generated region is stale')

    def test_missing_region_is_an_input_error(self):
        self.edit('README.md', MATRIX['end']('zig-versions'), '')
        self.assertProblem("expected one 'zig-versions' region", code=2)


class Agreement(Scratch):
    def test_cli_help_must_name_each_version_and_default(self):
        path = self.root/'Air2Lean/Main.lean'
        path.write_text(path.read_text(encoding='utf-8').replace('0.14.1', '0.14.x'), encoding='utf-8')
        self.assertProblem('help does not name Zig 0.14.1')
        self.edit('Air2Lean/Main.lean', '0.16.0 (default)', '0.16.0')
        self.assertProblem('help does not mark 0.16.0 as the default')

    def test_cli_help_must_describe_usage_flags(self):
        self.edit('Air2Lean/Main.lean', '  --model-registry-template    Write',
                  '  (registry template)          Write')
        self.assertProblem('help does not describe --model-registry-template')

    def test_cli_help_flag_prefix_does_not_describe_longer_flag(self):
        self.edit('Air2Lean/Main.lean', '  --model-registry <json>      Bind',
                  '  (model registry)             Bind')
        self.assertProblem('help does not describe --model-registry\n')

    def test_cli_usage_matches_diagnostics_usage(self):
        self.edit('Air2Lean/Diagnose.lean', '[--diagnostic-limit 1..4096]', '[--diagnostic-limit 1..8192]')
        self.assertProblem('usage differs from the --diagnostics-json usage')

    def test_translator_version_must_be_pinned_and_inventoried(self):
        self.edit('Air2Lean/Air/Normalize.lean', 'def supportedVersions : List String := [',
                  'def supportedVersions : List String := ["0.99.0", ')
        status, output = run('generate', '--root', self.root)
        self.assertEqual(status, 1, output)
        self.assertIn('zig-patch/versions.toml pins', output)
        self.assertIn('coverage inventories', output)
        self.assertIn('CI matrix versions', output)
        self.assertIn('compatibility.json lists', output)
        self.assertIn('help does not name Zig 0.99.0', output)

    def test_in_qualification_version_is_labelled(self):
        rows = MATRIX['version_rows'](ROOT)[2]
        status = MATRIX['version_status'](ROOT)
        for row in rows:
            if status.get(row['version']) == 'in-qualification':
                self.assertEqual(row['label'], row['version'] + ' (in qualification)')
        self.assertEqual(MATRIX['version_label']('0.17.0', '0.16.0', {'0.17.0': 'in-qualification'}),
                         '0.17.0 (in qualification)')
        self.assertEqual(MATRIX['version_label']('0.16.0', '0.16.0', {'0.16.0': 'qualified'}),
                         '0.16.0 (default)')

    def test_default_scripts_must_agree(self):
        self.edit('scripts/mutate.sh', 'AIR2LEAN_ZIG_VERSION:-0.16.0', 'AIR2LEAN_ZIG_VERSION:-0.15.2')
        self.assertProblem('default Zig versions disagree', code=2)

    def test_release_metadata_default_must_agree(self):
        self.edit('compatibility.json', '"default": "0.16.0"', '"default": "0.15.2"')
        self.assertProblem('default Zig versions disagree', code=2)

    def test_ci_example_list_must_match_selection(self):
        self.edit('.github/workflows/ci.yml', 'floats errors variants pointers layout"',
                  'floats errors variants pointers layout slices"')
        self.assertProblem('CI 0.14.1 examples')

    def test_readme_examples_table_names_every_example(self):
        self.edit('README.md', '| `threadsync` (0.15.2) |', '| (0.15.2) |')
        self.assertProblem('README.md examples table omits `threadsync`')

    def test_plan_open_work_repeats_no_completed_work(self):
        anchor = 'The former T-series follow-ups now map to register IDs:'
        self.edit('PLAN.md', anchor, 'T01 target profiles. ' + anchor)
        self.assertProblem('PLAN.md open work repeats complete requirement T01')

    def test_plan_open_work_lists_nothing_done(self):
        anchor = 'The former T-series follow-ups now map to register IDs:'
        self.edit('PLAN.md', anchor, 'rwLockRead (done). ' + anchor)
        self.assertProblem('PLAN.md open work lists an item as done')

    def test_plan_open_work_has_no_historical_milestone_rows(self):
        anchor = 'The former T-series follow-ups now map to register IDs:'
        self.edit('PLAN.md', anchor, '| T7 | inventory |\n\n' + anchor)
        self.assertProblem('PLAN.md open work keeps historical T-series milestones')

    def test_plan_marks_history(self):
        self.edit('PLAN.md', '## Historical milestones', '## Status')
        self.assertProblem('PLAN.md has no "## Historical milestones" section')


if __name__ == '__main__':
    unittest.main()
