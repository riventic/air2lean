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

    def test_actual_zig16_multiline_diagnostics(self):
        log = self.multiline()
        self.assertTrue(module.classify(1, log, 'forget-parent'))
        self.assertTrue(module.classify(1, log, 'forget-payload'))
        self.assertTrue(module.classify(1, log, 'wrap-offset'))
        with self.assertRaises(ValueError): module.classify(1, log, 'unbounded')

    @staticmethod
    def multiline():
        return (
            '1/3 forget-parent.test.accumulates leaf, exact payload, and every parent offset...expected 33, found 5\n'
            'FAIL (TestExpectedEqual)\n'
            '2/3 forget-parent.test.both overflow additions fail without committing partial state...expected error.Overflow, found void\n'
            'FAIL (TestExpectedError)\n'
            '3/3 forget-parent.test.bounded recursion rejects a cycle or deep chain at the same boundary...OK\n'
            '1 passed; 0 skipped; 2 failed.\n')

    def test_multiline_failure_framing_is_strict(self):
        log = self.multiline()
        bad = [
            'FAIL (TestExpectedEqual)\n' + log,
            log + 'FAIL (TestExpectedEqual)\n',
            log.replace('FAIL (TestExpectedEqual)', 'FAIL (OutOfMemory)'),
            log.replace('FAIL (TestExpectedError)', 'FAIL (UnknownError)'),
            log.replace('FAIL (TestExpectedEqual)', 'FAIL'),
            log.replace('FAIL (TestExpectedEqual)', 'FAIL (TestExpectedEqual) trailing'),
            log.replace('FAIL (TestExpectedEqual)', 'FAIL (TestExpectedEqual)\nFAIL (TestExpectedEqual)'),
            log.replace('accumulates leaf, exact payload, and every parent offset', 'different'),
            log.replace('both overflow additions fail without committing partial state', 'unknown additional test'),
            log.replace('1/3 forget-parent.test.', 'unframed.test.'),
        ]
        for candidate in bad:
            with self.subTest(log=candidate):
                with self.assertRaises(ValueError): module.classify(1, candidate, 'forget-parent')

    def test_multiline_tool_panic_import_signal_timeout_rejected(self):
        log = self.multiline()
        for diagnostic in ['error: import failed', 'panic: unreachable', 'panic', 'thread panicked', 'Segmentation fault',
                           'signal 11', 'SIGABRT', 'unable to load module', 'FileNotFound',
                           'import failed', 'module not found', 'compiler failed', 'build failed',
                           'timeout', 'timed out']:
            with self.subTest(diagnostic=diagnostic):
                with self.assertRaises(ValueError): module.classify(1, log + diagnostic, 'forget-parent')
        for status in (0, 2, -9, 137):
            with self.subTest(status=status):
                with self.assertRaises(ValueError): module.classify(status, log, 'forget-parent')

if __name__ == '__main__': unittest.main()
