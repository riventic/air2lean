import importlib.util
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('qualification', HERE / 'compiler-qualification.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
TRANSLATOR = Path(os.environ.get('AIR2LEAN_TRANSLATOR', HERE.parents[2] / '.lake/build/bin/air2lean'))


class CompilerQualificationTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.case = Path(temp.name) / 'case'
        for name in ('air-fresh', 'aliases/air-fresh'):
            shutil.copytree(HERE / name, self.case / name)
        for name in ('TryPointers/Gen.lean', 'aliases/TryAliases/Gen.lean', 'compiler-qualification.json'):
            (self.case / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(HERE / name, self.case / name)

    def air(self, name):
        return next(self.case.glob(f'**/{name}.json'))

    def test_retained_record_passes(self):
        self.assertEqual(len(gate.inspect()), 7)
        self.assertEqual(len(gate.inspect(self.case)), 7)

    def test_changed_air_is_stale(self):
        path = self.air('try_pointers.writeAlias')
        path.write_text(path.read_text() + ' ')
        with self.assertRaisesRegex(ValueError, 'stale or incomplete'):
            gate.inspect(self.case)

    def test_missing_function_changes_the_inventory(self):
        self.air('try_aliases.twoPaths').unlink()
        with self.assertRaisesRegex(ValueError, 'inventory differs'):
            gate.inspect(self.case)

    def test_profile_must_be_linux_baseline_release_safe(self):
        path = self.air('try_pointers.cleanup')
        doc = json.loads(path.read_text())
        doc['profile']['build_mode'] = 'Debug'
        path.write_text(json.dumps(doc))
        with self.assertRaisesRegex(ValueError, 'profile differs'):
            gate.inspect(self.case)

    def test_both_pointer_try_tags_must_occur(self):
        for name in ('try_pointers.cleanup', 'try_pointers.coldPayload'):
            path = self.air(name)
            path.write_text(path.read_text().replace('try_ptr_cold', 'try_ptr'))
        with self.assertRaisesRegex(ValueError, 'lacks required tags'):
            gate.inspect(self.case)

    @unittest.skipUnless(TRANSLATOR.exists(), 'translator is not built')
    def test_translation_matches_retained_modules_and_a_changed_module_does_not(self):
        gate.inspect(self.case, translator=TRANSLATOR)
        path = self.case / 'aliases/TryAliases/Gen.lean'
        path.write_text(path.read_text() + '\n-- changed\n')
        with self.assertRaisesRegex(ValueError, 'differs'):
            gate.inspect(self.case, translator=TRANSLATOR)


if __name__ == '__main__':
    unittest.main()
