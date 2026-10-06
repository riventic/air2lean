import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('payload_mutants', HERE/'mutations.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class Mutations(unittest.TestCase):
    def test_exact_typed_targets(self):
        source = (HERE.parents[2]/'zig-patch/air-json/pointer-offset.zig').read_text()
        for name in module.MUTANTS:
            self.assertNotEqual(module.mutate(source, name), source)
            with self.assertRaises(ValueError): module.mutate('', name)

    def test_named_assertions_only(self):
        title = module.MUTANTS['forget-parent'][2]
        good = f'1/3 pointer-offset.test.{title}...FAIL (TestExpectedEqual)\n'
        self.assertTrue(module.classify(1, good, 'forget-parent'))
        for status, log in [(0, good), (2, good), (-9, good), (1, 'error: import failed'),
                            (1, good+'error: import failed'), (1, good.replace(title, 'different')),
                            (1, good.replace('TestExpectedEqual', 'OutOfMemory'))]:
            with self.assertRaises(ValueError): module.classify(status, log, 'forget-parent')

if __name__ == '__main__': unittest.main()
