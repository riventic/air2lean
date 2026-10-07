#!/usr/bin/env python3
"""Tutorial layout regressions (scripts/tutorials.py lint/modules). Files only; no Lean."""
import importlib.util
from pathlib import Path
import re
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('tutorials', ROOT / 'scripts/tutorials.py')
tutorials = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tutorials)
# D04: the tutorials the roadmap names, by directory.
REQUIRED = ('first-proof', 'mutable-arrays', 'generic-containers', 'external-contracts',
            'allocation-failure', 'concurrent-clients', 'cross-target')


class Committed(unittest.TestCase):
    def test_lint_passes(self):
        self.assertEqual(tutorials.lint(ROOT), [])

    def test_required_tutorials_exist(self):
        names = {p.name for p in tutorials.tutorials(ROOT)}
        self.assertLessEqual(set(REQUIRED), names)
        self.assertEqual(set(tutorials.DOCUMENTED), {'cross-target'})

    def test_modules_are_the_imports(self):
        self.assertIn('Proofs.Basic.Proofs', tutorials.modules(ROOT))
        self.assertIn('Proofs.Sync.Mutex', tutorials.modules(ROOT))

    def test_clean_env_and_ci_run_every_tutorial(self):
        clean = (ROOT / 'scripts/clean-env.sh').read_text()
        self.assertIn('lake build $(python3 scripts/tutorials.py modules)', clean)
        self.assertIn('python3 scripts/tutorials.py check', clean)
        ci = (ROOT / '.github/workflows/ci.yml').read_text()
        self.assertIn('scripts/tutorials.py check', ci)
        self.assertIn('tests/roadmap/tutorials', ci)

    def test_negative_controls_are_excluded_from_premises(self):
        excluded = (ROOT / 'assurance/premises.json').read_text()
        for path in tutorials.checked(ROOT):
            self.assertIn(f'"tutorials/{path.name}/Negative.lean"', excluded)


class Fixture(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        shutil.copytree(ROOT / 'tutorials', self.root / 'tutorials')
        (self.root / 'docs').mkdir()
        shutil.copy(ROOT / 'docs/premise-index.md', self.root / 'docs/premise-index.md')
        self.assertEqual(tutorials.lint(self.root), [])

    def errors(self):
        return '\n'.join(tutorials.lint(self.root))

    def edit(self, rel, old, new):
        path = self.root / rel
        text = path.read_text()
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1))

    def test_missing_negative_control(self):
        (self.root / 'tutorials/mutable-arrays/Negative.lean').unlink()
        self.assertIn('tutorials/mutable-arrays: missing Negative.lean', self.errors())

    def test_missing_expected_error(self):
        path = self.root / 'tutorials/mutable-arrays/Negative.lean'
        path.write_text(re.sub(r'^-- expect-error: .*\n', '', path.read_text(), flags=re.M))
        self.assertIn('Negative.lean: missing "-- expect-error', self.errors())

    def test_missing_assumptions_section(self):
        self.edit('tutorials/allocation-failure/README.md', '## Assumptions and remaining obligations',
                  '## Notes')
        self.assertIn('missing ## Assumptions and remaining obligations', self.errors())

    def test_premise_list_must_match_index(self):
        self.edit('tutorials/allocation-failure/README.md', '[ALC-02](../../docs/premises.md#alc-02)', 'the policy')
        self.assertIn("tutorials/allocation-failure/README.md: assumptions list", self.errors())

    def test_unindexed_tutorial(self):
        self.edit('docs/premise-index.md', '## `tutorials/mutable-arrays/Main.lean`', '## `elsewhere`')
        self.assertIn('tutorials/mutable-arrays/Main.lean: not in docs/premise-index.md', self.errors())

    def test_documented_tutorial_has_only_a_readme(self):
        (self.root / 'tutorials/cross-target/Main.lean').write_text('')
        self.assertIn('tutorials/cross-target: a documented tutorial has only README.md', self.errors())

    def test_new_directory_must_be_complete(self):
        (self.root / 'tutorials/new').mkdir()
        (self.root / 'tutorials/new/README.md').write_text('# New\n')
        self.assertIn('tutorials/new: missing Main.lean, Solution.lean, Negative.lean', self.errors())


if __name__ == '__main__':
    unittest.main()
