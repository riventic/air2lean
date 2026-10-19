#!/usr/bin/env python3
"""Exercise cache invalidation without running compiler processes outside the build guard."""
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
from test_policy import audit


class ToolCacheTests(unittest.TestCase):
    def test_verified_cache_reuse_and_invalidation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tools").mkdir()
            source = root / "tools/Assurance.lean"
            source.write_text("import Lean\n")
            pin = root / "lean-toolchain"
            pin.write_text("leanprover/lean4:v4.34.0\n")
            (root / "lakefile.toml").write_text('name = "test"\n[[lean_lib]]\nname = "tools"\n')
            dependency = root / "imported-dependency"
            dependency.write_text("original dependency")
            artifact = root / ".lake/build/lib/lean/tools/Assurance.olean"
            artifact.parent.mkdir(parents=True)
            builds, validations, previous_inputs = [], [], []

            def validate_and_build(command):
                # Mock Lake's responsibility for dependency freshness, never skip asking it.
                self.assertEqual(command, ["lake", "--rehash", "build", "AssuranceTools"])
                validations.append(command)
                inputs = source.read_bytes() + pin.read_bytes() + dependency.read_bytes()
                if not artifact.is_file() or previous_inputs != [inputs]:
                    builds.append(inputs)
                    artifact.write_bytes(b"checked artifact: " + inputs)
                    artifact.with_suffix(".trace").write_bytes(hashlib.sha256(inputs).digest())
                    previous_inputs[:] = [inputs]

            def prepare():
                trace = audit.prepare_tool(root, validate_and_build)
                self.assertEqual(trace["olean_sha256"], audit.file_sha256(artifact))
                self.assertEqual(trace["lake_trace_sha256"], audit.file_sha256(artifact.with_suffix(".trace")))
                return trace

            self.assertFalse(prepare()["cache_reused"])
            self.assertTrue(prepare()["cache_reused"])
            self.assertEqual(len(builds), 1)
            source.write_text(source.read_text() + "-- extractor changed\n")
            self.assertFalse(prepare()["cache_reused"])
            pin.write_text("leanprover/lean4:changed-release-pin\n")
            self.assertFalse(prepare()["cache_reused"])
            artifact.write_bytes(b"invalid cached tool")
            self.assertFalse(prepare()["cache_reused"])
            artifact.unlink()
            self.assertFalse(prepare()["cache_reused"])
            dependency.write_text("changed imported dependency")
            self.assertFalse(prepare()["cache_reused"])
            self.assertEqual(len(builds), 6)
            self.assertEqual(len(validations), 7)

    def test_failed_preparation_never_publishes_valid_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tools").mkdir()
            (root / "tools/Assurance.lean").write_text("import Lean\n")
            (root / "lean-toolchain").write_text("pin\n")
            (root / "lakefile.toml").write_text('name = "test"\n[[lean_lib]]\nname = "tools"\n')

            def failed_builder(_):
                raise RuntimeError("compiler failed")

            with self.assertRaises(RuntimeError):
                audit.prepare_tool(root, failed_builder)
            self.assertFalse((root / ".lake/assurance/tool-trace.json").exists())

    def source_project(self, root):
        (root / 'tools').mkdir()
        (root / 'tools/Assurance.lean').write_text('import tools.Helper\n')
        (root / 'tools/Helper.lean').write_text('def value := 1\n')
        (root / 'lean-toolchain').write_text('pin\n')
        (root / 'lakefile.toml').write_text('[[lean_lib]]\nname = "tools"\n')
        artifact = root / '.lake/build/lib/lean/tools/Assurance.olean'

        def build(command):
            self.assertEqual(command, ['lake', '--rehash', 'build', 'AssuranceTools'])
            if not artifact.is_file():
                artifact.parent.mkdir(parents=True, exist_ok=True)
                artifact.write_bytes(b'fixed extractor')
                artifact.with_suffix('.trace').write_bytes(b'fixed Lake trace')

        return build, artifact

    def test_helper_source_change_invalidates_trace_with_fixed_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build, artifact = self.source_project(root)
            audit.prepare_tool(root, build)
            self.assertTrue(audit.prepare_tool(root, build)['cache_reused'])
            fixed = artifact.read_bytes(), artifact.with_suffix('.trace').read_bytes()
            helper = root / 'tools/Helper.lean'
            saved = helper.stat()
            helper.write_text('def value := 2\n')
            os.utime(helper, ns=(saved.st_atime_ns, saved.st_mtime_ns))
            changed = audit.prepare_tool(root, build)
            self.assertFalse(changed['cache_reused'])
            self.assertEqual(fixed, (artifact.read_bytes(), artifact.with_suffix('.trace').read_bytes()))
            self.assertEqual(changed['library_sources_sha256'], audit.library_sources_sha256(root))
            self.assertTrue(audit.prepare_tool(root, build)['cache_reused'])
            external = root / 'outside-library.lean'
            external.write_bytes(helper.read_bytes())
            helper.unlink()
            helper.symlink_to(external)
            self.assertTrue(audit.prepare_tool(root, build)['cache_reused'])
            external.write_text('def value := 3\n')
            self.assertFalse(audit.prepare_tool(root, build)['cache_reused'])
            extra = root / 'tools/Unused.lean'
            extra.write_text('def unused := 1\n')
            self.assertFalse(audit.prepare_tool(root, build)['cache_reused'])
            extra.unlink()
            self.assertFalse(audit.prepare_tool(root, build)['cache_reused'])
            manifest = root / '.lake/assurance/tool-trace.json'
            unbound = json.loads(manifest.read_text())
            del unbound['library_sources_sha256']
            manifest.write_text(json.dumps(unbound))
            self.assertFalse(audit.prepare_tool(root, build)['cache_reused'])
            self.assertEqual(fixed, (artifact.read_bytes(), artifact.with_suffix('.trace').read_bytes()))

    def test_source_mutation_during_preparation_and_extraction_is_rejected(self):
        for stage in ('unchanged', 'preparation', 'extraction'):
            with self.subTest(stage=stage), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                build, _ = self.source_project(root)

                def run(command):
                    if command[:3] == ['lake', 'env', 'lean']:
                        if stage == 'extraction':
                            (root / 'tools/Helper.lean').write_text('def value := 2\n')
                        return audit.MARKER + json.dumps({'modules': ['Proofs.Fixture'], 'nodes': []})
                    build(command)
                    if stage == 'preparation':
                        (root / 'tools/Helper.lean').write_text('def value := 2\n')

                prepare = audit.prepare_tool
                with patch.object(audit, 'ROOT', root), patch.object(audit, 'run', run), \
                        patch.object(audit, 'prepare_tool', side_effect=lambda: prepare(root, run)):
                    if stage == 'unchanged':
                        self.assertEqual(audit.extract(['Proofs.Fixture'], False)['modules'], ['Proofs.Fixture'])
                    else:
                        with self.assertRaisesRegex(ValueError, 'sources changed during extractor ' + stage):
                            audit.extract(['Proofs.Fixture'], False)
                if stage == 'preparation':
                    self.assertFalse((root / '.lake/assurance/tool-trace.json').exists())


if __name__ == "__main__":
    unittest.main()
