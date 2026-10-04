import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('mutation', Path(__file__).with_name('mutate-offset.py'))
mutation = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mutation)


class OffsetMutationTests(unittest.TestCase):
    def setUp(self):
        self.proof = '\n'.join([
            mutation.BEGIN,
            'theorem payload8_program (p : Ptr) : baseline = expected := by',
            '  simp [baseline, expected]', mutation.END,
            'theorem unrelated : True := by trivial'])
        self.path = '/private/tmp/mutant/TryPointers/Proofs.lean'
        self.log = f'{self.path}:3:2: error: unsolved goals\np : Ptr\n⊢ shifted = original\n'

    def test_one_typed_success_offset_changes(self):
        source = ('def payload64 (p : Ptr) := pure ((.ok v2) : Except Zig.ErrName (Zig.Ptr))\n'
                  'structure payload8Locals where\n'
                  'def payload8 (p : Ptr) :=\n  pure ((.ok v2) : Except Zig.ErrName (Zig.Ptr))\n'
                  'structure nextLocals where\n')
        changed = mutation.mutate(source)
        self.assertEqual(changed.count('v2.add 1'), 1)
        self.assertIn('def payload64 (p : Ptr) := pure ((.ok v2)', changed)
        self.assertEqual(changed.replace('(v2.add 1)', 'v2'), source)

    def test_missing_or_ambiguous_mutation_site_fails(self):
        with self.assertRaises(ValueError):
            mutation.mutate('def payload8 (p : Ptr) := pure p\nend TryPointers\n')
        needle = 'pure ((.ok v2) : Except Zig.ErrName (Zig.Ptr))'
        with self.assertRaises(ValueError):
            mutation.mutate(f'def payload8 (p : Ptr) := {needle}\n{needle}\nend TryPointers\n')
        with self.assertRaises(ValueError):
            mutation.mutate(f'def payload8 (p : Ptr) := {needle}\ndef payload8 (q : Ptr) := {needle}\nend TryPointers\n')

    def test_exact_located_bridge_kernel_failure_passes(self):
        self.assertTrue(mutation.classify(1, self.path, self.proof, self.log))

    def test_exit_status_success_signal_or_tool_failure_rejected(self):
        for code in [0, 2, 137, -9]:
            with self.subTest(code=code), self.assertRaises(ValueError):
                mutation.classify(code, self.path, self.proof, self.log)

    def test_parser_import_unknown_identifier_type_failure_rejected(self):
        for message in ["unexpected identifier; expected '}'", 'unknown module prefix ZigLean',
                        'unknown identifier missing', 'type mismatch', 'failed to synthesize']:
            with self.subTest(message=message), self.assertRaises(ValueError):
                mutation.classify(1, self.path, self.proof,
                                  f'{self.path}:3:2: error: {message}\n')

    def test_unlocated_tool_failure_missing_error_and_other_file_rejected(self):
        for log in ['', 'error: cannot open file\n', self.log + 'error: package failed\n',
                    self.log.replace(self.path, '/wrong/Proofs.lean')]:
            with self.subTest(log=log), self.assertRaises(ValueError):
                mutation.classify(1, self.path, self.proof, log)

    def test_unrelated_or_second_error_rejected(self):
        for line in [1, 4, 5]:
            bad = f'{self.path}:{line}:2: error: unsolved goals\n'
            with self.subTest(line=line), self.assertRaises(ValueError):
                mutation.classify(1, self.path, self.proof, bad)
            with self.subTest(second=line), self.assertRaises(ValueError):
                mutation.classify(1, self.path, self.proof, self.log + bad)

    def test_bad_marker_or_theorem_identity_rejected(self):
        for proof in [self.proof.replace(mutation.BEGIN, ''), self.proof + '\n' + mutation.END,
                      self.proof.replace('theorem payload8_program', 'theorem helper_only')]:
            with self.subTest(proof=proof), self.assertRaises(ValueError):
                mutation.classify(1, self.path, proof, self.log)

    def test_bounded_log_reader(self):
        with tempfile.TemporaryDirectory() as work:
            p = Path(work) / 'log'
            p.write_bytes(b'x' * (mutation.CAP + 1))
            with self.assertRaises(ValueError):
                mutation.bounded_text(p)


if __name__ == '__main__':
    unittest.main()
