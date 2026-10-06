"""Metadata-only regressions; these are not manufactured compiler AIR fixtures."""
import copy
import runpy
from pathlib import Path
import unittest

GATE = runpy.run_path(str(Path(__file__).with_name('check-export.py')))

def metadata(version='0.16.0'):
    return {'schema': 12, 'zig_version': version, 'target_endian': 'little', 'profile': {
        'name': 'abi64-le-v1', 'zig_version': version, 'target_triple': 'x86_64-linux-musl',
        'pointer_bits': 64, 'endian': 'little', 'abi': 'musl', 'backend': 'stage2_x86_64',
        'cpu': 'x86_64', 'features': sorted(GATE['BASELINE_FEATURES']),
        'build_mode': 'ReleaseSafe', 'float_mode': 'per-instruction', 'error_set_bits': 16,
        'error_layout': 'type-table', 'error_tracing': False, 'export_stage': 'analyzed-air'}}

class Profiles(unittest.TestCase):
    def test_requested_version_and_profile(self):
        for version in ('0.14.1', '0.15.2', '0.16.0'):
            GATE['profile'](metadata(version), version, 'stage2_x86_64')
        for key, value in [('backend', 'stage2_llvm'), ('abi', 'gnu'), ('cpu', 'haswell'),
                           ('features', []), ('build_mode', 'Debug'), ('error_tracing', True),
                           ('target_triple', 'aarch64-macos-none')]:
            bad = copy.deepcopy(metadata()); bad['profile'][key] = value
            with self.assertRaises(ValueError): GATE['profile'](bad, '0.16.0', 'stage2_x86_64')
        with self.assertRaises(ValueError): GATE['profile'](metadata('0.15.2'), '0.16.0', 'stage2_x86_64')
        bad = metadata(); bad['schema'] = 11
        with self.assertRaises(ValueError): GATE['profile'](bad, '0.16.0', 'stage2_x86_64')

    def test_llvm_request_rejected(self):
        bad = metadata(); bad['profile']['backend'] = 'stage2_llvm'
        with self.assertRaises(ValueError): GATE['profile'](bad, '0.16.0', 'stage2_llvm')

    def test_type_indices_rejected(self):
        table = {'types': [{'k': 'int'}]}
        for index in (-1, 1, True, '0'):
            with self.assertRaises(ValueError): GATE['type_at'](table, index)
        self.assertEqual(GATE['type_at'](table, 0), {'k': 'int'})

    def test_duplicate_members_rejected(self):
        with self.assertRaises(ValueError): GATE['HELPERS']['parse_json']('{"off":-1,"off":3}')

if __name__ == '__main__': unittest.main()
