import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('guard', Path(__file__).with_name('check-artifacts.py'))
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        self.case = self.repo / 'case'
        (self.case / 'air/0.16.0').mkdir(parents=True)
        (self.case / 'TryPointers').mkdir()
        (self.repo / 'source.zig').write_text('fixture source')
        (self.repo / 'exporter.zig').write_text('fixture exporter')
        (self.case / 'TryPointers/Gen.lean').write_text('fixture generated output')
        for name, tag in [('hot', 'try_ptr'), ('cold', 'try_ptr_cold')]:
            (self.case / ('air/0.16.0/' + name + '.json')).write_text(json.dumps({
                'schema': 11, 'zig_version': '0.16.0', 'target_endian': 'little',
                'name': 'try_pointers.' + name, 'body': [{'tag': tag}]}))
        self.manifest = {'source': 'source.zig', 'source_sha256': guard.digest(self.repo/'source.zig'),
                         'exporter': 'exporter.zig', 'exporter_sha256': guard.digest(self.repo/'exporter.zig'),
                         'functions': ['hot', 'cold'], 'artifacts': {}}
        self.save()
        guard.inspect(self.repo, self.case, record=True)
        self.manifest = json.loads((self.case/'provenance.json').read_text())

    def save(self):
        (self.case/'provenance.json').write_text(json.dumps(self.manifest))

    def test_complete_inventory_and_stale_source(self):
        self.assertEqual(len(guard.inspect(self.repo, self.case)), 3)
        (self.repo/'source.zig').write_text('modified')
        with self.assertRaisesRegex(ValueError, 'stale source'): guard.inspect(self.repo, self.case)

    def test_expected_hash_format_and_exporter(self):
        self.manifest['source_sha256'] = 'not a SHA-256'
        self.save()
        with self.assertRaisesRegex(ValueError, 'invalid source'): guard.inspect(self.repo, self.case)
        self.manifest['source_sha256'] = guard.digest(self.repo/'source.zig')
        self.save()
        (self.repo/'exporter.zig').write_text('modified')
        with self.assertRaisesRegex(ValueError, 'stale exporter'): guard.inspect(self.repo, self.case)

    def test_missing_and_duplicate_function_inventory(self):
        hot = self.case/'air/0.16.0/hot.json'
        hot.unlink()
        with self.assertRaisesRegex(ValueError, 'function inventory'): guard.inspect(self.repo, self.case)
        hot.write_text((self.case/'air/0.16.0/cold.json').read_text())
        with self.assertRaisesRegex(ValueError, 'function inventory'): guard.inspect(self.repo, self.case)

    def test_unsupported_and_wrong_profile(self):
        hot = self.case/'air/0.16.0/hot.json'
        data = json.loads(hot.read_text())
        data['body'][0]['unsupported'] = True
        hot.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'unsupported'): guard.inspect(self.repo, self.case)
        data['body'][0].pop('unsupported')
        data['zig_version'] = '0.15.2'
        hot.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'profile differs'): guard.inspect(self.repo, self.case)

    def test_required_cold_and_hot_tags(self):
        cold = self.case/'air/0.16.0/cold.json'
        data = json.loads(cold.read_text())
        data['body'][0]['tag'] = 'try_ptr'
        cold.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'both pointer-try tags'): guard.inspect(self.repo, self.case)

    def test_generated_hash_and_exact_recorded_inventory(self):
        (self.case/'TryPointers/Gen.lean').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'artifact inventory'): guard.inspect(self.repo, self.case)
        guard.inspect(self.repo, self.case, record=True)
        self.manifest = json.loads((self.case/'provenance.json').read_text())
        self.manifest['artifacts']['not-an-artifact'] = '0'*64
        self.save()
        with self.assertRaisesRegex(ValueError, 'artifact inventory'): guard.inspect(self.repo, self.case)

    def fresh(self):
        fresh = self.repo / 'external-fresh-air'
        fresh.mkdir()
        for source in (self.case/'air/0.16.0').glob('*.json'):
            data = json.loads(source.read_text())
            data['schema'] = 12
            data['profile'] = {
                'name': 'abi64-le-v1', 'target_triple': 'x86_64-linux.6.1...6.6-musl',
                'pointer_bits': 64, 'endian': 'little', 'abi': 'musl', 'zig_version': '0.16.0',
                'backend': 'stage2_llvm', 'cpu': 'x86_64', 'features': sorted(guard.BASELINE_FEATURES),
                'build_mode': 'ReleaseSafe', 'float_mode': 'per-instruction', 'error_set_bits': 16,
                'error_layout': 'type-table', 'error_tracing': False, 'export_stage': 'analyzed-air'}
            (fresh/source.name).write_text(json.dumps(data))
        return fresh

    def integration(self):
        before = (self.case/'provenance.json').read_bytes()
        (self.repo/'exporter.zig').write_text('combined exporter')
        variant = {
            'format': 'l04-integration-inputs-v1', 'status': 'inputs-only-not-compilation-attestation',
            'origin_provenance_sha256': guard.digest(self.case/'provenance.json'),
            'origin_exporter_sha256': self.manifest['exporter_sha256'],
            'current_exporter_sha256': guard.digest(self.repo/'exporter.zig')}
        path = self.case/'integration-qualification.json'
        path.write_text(json.dumps(variant))
        return before, path, variant

    def test_fresh_air_reuses_inventory_profile_and_source_guards(self):
        fresh = self.fresh()
        before = (self.case/'provenance.json').read_bytes()
        self.assertEqual(set(guard.inspect(self.repo, self.case, fresh_air=fresh)),
                         {'hot.json', 'cold.json'})
        self.assertEqual((self.case/'provenance.json').read_bytes(), before)
        hot = fresh/'hot.json'
        data = json.loads(hot.read_text())
        data['zig_version'] = '0.15.2'
        hot.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'profile differs'):
            guard.inspect(self.repo, self.case, fresh_air=fresh)
        (self.repo/'source.zig').write_text('modified')
        with self.assertRaisesRegex(ValueError, 'stale source'):
            guard.inspect(self.repo, self.case, fresh_air=fresh)

    def test_fresh_air_missing_inventory_or_record_request_fails(self):
        fresh = self.repo / 'empty-fresh-air'
        fresh.mkdir()
        with self.assertRaisesRegex(ValueError, 'function inventory'):
            guard.inspect(self.repo, self.case, fresh_air=fresh)
        with self.assertRaisesRegex(ValueError, 'cannot record'):
            guard.inspect(self.repo, self.case, record=True, fresh_air=fresh)

    def test_integration_binds_current_and_origin_without_rewriting_history(self):
        before, path, variant = self.integration()
        self.assertEqual(len(guard.inspect(self.repo, self.case)), 3)
        self.assertEqual(len(guard.inspect(self.repo, self.case, fresh_air=self.fresh())), 2)
        self.assertEqual((self.case/'provenance.json').read_bytes(), before)
        with self.assertRaisesRegex(ValueError, 'cannot rewrite historical'):
            guard.inspect(self.repo, self.case, record=True)
        self.assertEqual((self.case/'provenance.json').read_bytes(), before)
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'stale exporter'):
            guard.inspect(self.repo, self.case)

    def test_integration_stale_current_origin_and_historical_receipt_fail(self):
        before, path, variant = self.integration()
        (self.repo/'exporter.zig').write_text('drifted combined exporter')
        with self.assertRaisesRegex(ValueError, 'stale exporter'):
            guard.inspect(self.repo, self.case)
        (self.repo/'exporter.zig').write_text('combined exporter')
        for field, diagnostic in [('origin_exporter_sha256', 'origin exporter'),
                                  ('origin_provenance_sha256', 'historical provenance'),
                                  ('current_exporter_sha256', 'stale exporter')]:
            changed = dict(variant, **{field: '0'*64})
            path.write_text(json.dumps(changed))
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, diagnostic):
                guard.inspect(self.repo, self.case)
        path.write_text(json.dumps(variant))
        self.manifest['artifacts']['TryPointers/Gen.lean'] = '0'*64
        self.save()
        with self.assertRaisesRegex(ValueError, 'historical provenance'):
            guard.inspect(self.repo, self.case)
        (self.case/'provenance.json').write_bytes(before)

    def test_integration_manifest_shape_status_and_digest_format_fail(self):
        before, path, variant = self.integration()
        for changed in [dict(variant, extra=True), dict(variant, status='qualified'),
                        dict(variant, current_exporter_sha256='not-sha256')]:
            path.write_text(json.dumps(changed))
            with self.subTest(changed=changed), self.assertRaisesRegex(ValueError, 'invalid integration'):
                guard.inspect(self.repo, self.case)
        self.assertEqual((self.case/'provenance.json').read_bytes(), before)

    def emitter_integration(self):
        before = (self.case/'provenance.json').read_bytes()
        origin = self.case/'origin/TryPointers/Gen.lean'
        origin.parent.mkdir(parents=True)
        origin.write_bytes((self.case/'TryPointers/Gen.lean').read_bytes())
        emitter = self.repo/'Air2Lean/Emit.lean'
        emitter.parent.mkdir()
        emitter.write_text('finite emitter fixture')
        (self.case/'TryPointers/Gen.lean').write_text('current finite generated output')
        variant = {
            'format': 'l04-emitter-integration-inputs-v1',
            'status': 'inputs-only-not-compilation-attestation',
            'origin_provenance_sha256': guard.digest(self.case/'provenance.json'),
            'origin_generated_sha256': self.manifest['artifacts']['TryPointers/Gen.lean'],
            'current_generated_sha256': guard.digest(self.case/'TryPointers/Gen.lean'),
            'current_emitter_sha256': guard.digest(emitter)}
        path = self.case/'emitter-integration.json'
        path.write_text(json.dumps(variant))
        return before, path, variant

    def test_emitter_variant_preserves_history_and_fresh_guards(self):
        before, path, variant = self.emitter_integration()
        self.assertEqual(len(guard.inspect(self.repo, self.case)), 3)
        self.assertEqual(len(guard.inspect(self.repo, self.case, fresh_air=self.fresh())), 2)
        with self.assertRaisesRegex(ValueError, 'cannot rewrite historical'):
            guard.inspect(self.repo, self.case, record=True)
        self.assertEqual((self.case/'provenance.json').read_bytes(), before)
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'artifact inventory'):
            guard.inspect(self.repo, self.case)

    def test_emitter_variant_rejects_each_drift_and_invalid_shape(self):
        before, path, variant = self.emitter_integration()
        for relative, diagnostic in [
                ('Air2Lean/Emit.lean', 'stale current emitter'),
                ('case/TryPointers/Gen.lean', 'stale current generated'),
                ('case/origin/TryPointers/Gen.lean', 'stale historical generated')]:
            item = self.repo/relative
            old = item.read_bytes()
            item.write_bytes(old + b'changed')
            with self.subTest(relative=relative), self.assertRaisesRegex(ValueError, diagnostic):
                guard.inspect(self.repo, self.case)
            item.write_bytes(old)
        for field, diagnostic in [
                ('origin_provenance_sha256', 'historical provenance'),
                ('origin_generated_sha256', 'origin generated'),
                ('current_generated_sha256', 'stale current generated'),
                ('current_emitter_sha256', 'stale current emitter')]:
            path.write_text(json.dumps(dict(variant, **{field: '0'*64})))
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, diagnostic):
                guard.inspect(self.repo, self.case)
        for changed in [dict(variant, extra=True), dict(variant, status='qualified'),
                        dict(variant, current_generated_sha256='not-sha256')]:
            path.write_text(json.dumps(changed))
            with self.subTest(changed=changed), self.assertRaisesRegex(ValueError, 'invalid emitter'):
                guard.inspect(self.repo, self.case)
        self.assertEqual((self.case/'provenance.json').read_bytes(), before)

    def test_fresh_schema12_exact_linux_baseline_profile_and_mixed_profiles(self):
        fresh = self.fresh()
        hot = fresh/'hot.json'
        original = json.loads(hot.read_text())
        variants = [dict(original, schema=11), dict(original, target_endian='big')]
        for key, value in [('target_triple', 'aarch64-macos-none'), ('abi', 'gnu'),
                           ('pointer_bits', 32), ('cpu', 'haswell'), ('backend', 'stage2_c'),
                           ('build_mode', 'Debug'), ('error_tracing', True),
                           ('features', ['sse', 'sse2'])]:
            variants.append(dict(original, profile=dict(original['profile'], **{key: value})))
        for data in variants:
            hot.write_text(json.dumps(data))
            with self.subTest(data=data), self.assertRaises(ValueError):
                guard.inspect(self.repo, self.case, fresh_air=fresh)
        hot.write_text(json.dumps(original))
        guard.inspect(self.repo, self.case, fresh_air=fresh)
        # Valid individual GNU/Musl profiles must still agree across the inventory.
        changed = dict(original, profile=dict(original['profile'], abi='gnu',
                       target_triple='x86_64-linux-gnu'))
        hot.write_text(json.dumps(changed))
        with self.assertRaisesRegex(ValueError, 'mixed profiles'):
            guard.inspect(self.repo, self.case, fresh_air=fresh)
        for source in fresh.glob('*.json'):
            data = json.loads(source.read_text())
            data['profile']['abi'] = 'gnu'
            data['profile']['target_triple'] = 'x86_64-linux.6.1...6.6-gnu.2.17'
            source.write_text(json.dumps(data))
        guard.inspect(self.repo, self.case, fresh_air=fresh)

    def test_fresh_receipt_preserves_body_and_rejects_changed_output_or_receipt(self):
        fresh = self.fresh()
        data = json.loads((fresh/'hot.json').read_text())
        metadata = dict(profile=guard.HELPERS['profile_for_air'](data),
                        float_semantics='ieee', correspondence='model')
        baseline = self.case/'TryPointers/Gen.lean'
        body = baseline.read_bytes()
        generated = self.repo/'fresh.lean'
        raw = guard.HELPERS['PREFIX'] + json.dumps(metadata).encode() + b'\n' + body
        generated.write_bytes(raw)
        receipt = self.repo/'generated-report.json'
        guard.HELPERS['write_report'](generated, fresh, receipt)
        guard.HELPERS['compare'](baseline, generated, receipt)
        self.assertEqual(generated.read_bytes(), raw)
        report = json.loads(receipt.read_text())
        self.assertEqual(len(report['air']), 2)
        generated.write_bytes(raw + b'\nchanged body')
        with self.assertRaisesRegex(ValueError, 'validated check report'):
            guard.HELPERS['compare'](baseline, generated, receipt)
        guard.HELPERS['write_report'](generated, fresh, receipt)
        with self.assertRaisesRegex(ValueError, 'semantics changed'):
            guard.HELPERS['compare'](baseline, generated, receipt)
        generated.write_bytes(raw)
        guard.HELPERS['write_report'](generated, fresh, receipt)
        report = json.loads(receipt.read_text())
        report['generated_sha256'] = '0'*64
        receipt.write_text(json.dumps(report))
        with self.assertRaisesRegex(ValueError, 'validated check report'):
            guard.HELPERS['compare'](baseline, generated, receipt)

    def test_ci_fresh_comparison_uses_receipt_and_retained_comparison_is_variant_scoped(self):
        repo = Path(__file__).resolve().parents[3]
        workflow = (repo/'.github/workflows/ci.yml').read_text()
        step = workflow.split('- name: Pointer try ownership, native and fresh source regressions', 1)[1]
        step = step.split('- name:', 1)[0]
        report = 'scripts/normalize-generated.py report "$fresh/Gen.lean" "$fresh/air" "$fresh/generated-report.json"'
        compare = 'scripts/normalize-generated.py compare tests/roadmap/try-pointers/TryPointers/Gen.lean "$fresh/Gen.lean" "$fresh/generated-report.json"'
        self.assertLess(step.index(report), step.index(compare))
        self.assertNotIn('cmp "$fresh/Gen.lean"', step)
        gate = (Path(__file__).with_name('check.sh')).read_text()
        retained = gate.split('if [ -f tests/roadmap/try-pointers/integration-qualification.json ]; then', 1)[1]
        variant, standalone = retained.split('else', 1)
        self.assertLess(variant.index('normalize-generated.py report'), variant.index('normalize-generated.py compare'))
        self.assertNotIn('cmp ', variant)
        self.assertIn('cmp "$work/TryPointers/Gen.lean" tests/roadmap/try-pointers/TryPointers/Gen.lean', standalone)

if __name__ == '__main__': unittest.main()
