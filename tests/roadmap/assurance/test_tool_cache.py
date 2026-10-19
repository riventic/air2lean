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


def toolchain(root):
    (root / 'bin').mkdir(parents=True)
    for name in ('lean', 'leanchecker'):
        (root / 'bin' / name).write_bytes(name.encode())
    (root / 'lib/lean').mkdir(parents=True)
    (root / 'lib/libleanshared.so').write_bytes(b'runtime1')
    return root


class ToolCacheTests(unittest.TestCase):
    def test_verified_cache_reuse_and_invalidation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            toolchain(root)
            (root / "tools").mkdir()
            source = root / "tools/Assurance.lean"
            source.write_text("import Lean\n")
            pin = root / "lean-toolchain"
            pin.write_text("leanprover/lean4:v4.34.0\n")
            (root / "lakefile.toml").write_text('name = "test"\n')
            dependency = root / "imported-dependency"
            dependency.write_text("original dependency")
            artifact = root / ".lake/build/lib/lean/tools/Assurance.olean"
            artifact.parent.mkdir(parents=True)
            builds, validations, previous_inputs = [], [], []

            def validate_and_build(command):
                if command == ['lake', 'env', 'printenv', 'LEAN_SYSROOT']:
                    return str(root)
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
            # Same executable, path, size and mtime do not identify the loaded runtime.
            library = root / 'lib/libleanshared.so'
            saved = library.stat()
            library.write_bytes(b'runtime2')
            os.utime(library, ns=(saved.st_atime_ns, saved.st_mtime_ns))
            self.assertFalse(prepare()['cache_reused'])
            self.assertTrue(prepare()['cache_reused'])
            self.assertEqual(len(builds), 7)
            # Installed logical/IR inputs are also loaded by the extractor's pinned Lean.
            for suffix in audit.COMPILED_SUFFIXES:
                companion = root / ('lib/lean/Init' + suffix)
                companion.write_bytes(b'original')
                self.assertFalse(prepare()['cache_reused'])
                companion.write_bytes(b'modified')
                self.assertFalse(prepare()['cache_reused'])
                companion.unlink()
                self.assertFalse(prepare()['cache_reused'])
            manifest = root / '.lake/assurance/tool-trace.json'
            unbound = json.loads(manifest.read_text())
            del unbound['toolchain_runtime_sha256']
            manifest.write_text(json.dumps(unbound))
            self.assertFalse(prepare()['cache_reused'])

    def test_failed_preparation_never_publishes_valid_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            toolchain(root)
            (root / "tools").mkdir()
            (root / "tools/Assurance.lean").write_text("import Lean\n")
            (root / "lean-toolchain").write_text("pin\n")
            (root / "lakefile.toml").write_text('name = "test"\n')

            def failed_builder(command):
                if command == ['lake', 'env', 'printenv', 'LEAN_SYSROOT']:
                    return str(root)
                raise RuntimeError("compiler failed")

            with self.assertRaises(RuntimeError):
                audit.prepare_tool(root, failed_builder)
            self.assertFalse((root / ".lake/assurance/tool-trace.json").exists())

    def test_changed_runtime_during_preparation_does_not_publish_trace(self):
        with tempfile.TemporaryDirectory() as directory:
            root = toolchain(Path(directory))
            (root / 'tools').mkdir()
            (root / 'tools/Assurance.lean').write_text('import Lean\n')
            (root / 'lean-toolchain').write_text('pin\n')
            (root / 'lakefile.toml').write_text('name = "test"\n')

            def changing_builder(command):
                if command == ['lake', 'env', 'printenv', 'LEAN_SYSROOT']:
                    return str(root)
                self.assertEqual(command, ['lake', '--rehash', 'build', 'AssuranceTools'])
                (root / 'lib/libleanshared.so').write_bytes(b'runtime2')

            with self.assertRaisesRegex(ValueError, 'runtime changed during extractor preparation'):
                audit.prepare_tool(root, changing_builder)
            self.assertFalse((root / '.lake/assurance/tool-trace.json').exists())


class RuntimeDigestTests(unittest.TestCase):
    def test_alias_identity_target_bytes_and_directory_aliases(self):
        with tempfile.TemporaryDirectory() as directory:
            root = toolchain(Path(directory) / 'install')
            library = root / 'lib/libleanshared.so'
            target = Path(directory) / 'external'
            target.write_bytes(library.read_bytes())
            first = audit.toolchain_runtime_sha256(root)
            library.unlink()
            library.symlink_to(target)
            linked = audit.toolchain_runtime_sha256(root)
            self.assertNotEqual(first, linked)
            target.write_bytes(b'runtime2')
            self.assertNotEqual(linked, audit.toolchain_runtime_sha256(root))
            target.unlink()
            with self.assertRaisesRegex(ValueError, 'missing compiled input symlink target'):
                audit.toolchain_runtime_sha256(root)
            library.unlink()
            external = Path(directory) / 'external-lib'
            external.mkdir()
            (external / 'Only.ir.sig').write_bytes(b'original')
            (root / 'lib/alias').symlink_to(external, target_is_directory=True)
            aliased = audit.toolchain_runtime_sha256(root)
            (external / 'Only.ir.sig').write_bytes(b'modified')
            self.assertNotEqual(aliased, audit.toolchain_runtime_sha256(root))
            (external / 'cycle').symlink_to(external, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'cyclic compiled input directory'):
                audit.toolchain_runtime_sha256(root)

    def test_loader_overlay_missing_inputs_and_hash_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            root = toolchain(Path(directory))
            initial = audit.toolchain_runtime_sha256(root)
            (root / 'lib/lean/Init.olean.hash').write_bytes(b'mutable')
            self.assertEqual(initial, audit.toolchain_runtime_sha256(root))
            # A directory's spelling does not turn loaded contents into hash metadata.
            nested = root / 'lib/runtime.hash'
            nested.mkdir()
            library = nested / 'libleanshared.dylib'
            library.write_bytes(b'original')
            with_directory = audit.toolchain_runtime_sha256(root)
            library.write_bytes(b'modified')
            self.assertNotEqual(with_directory, audit.toolchain_runtime_sha256(root))
            library.unlink()
            nested.rmdir()
            for variable in ('LD_PRELOAD', 'DYLD_LIBRARY_PATH'):
                with patch.dict(os.environ, {variable: 'external'}):
                    with self.assertRaisesRegex(ValueError, 'runtime loader overlay'):
                        audit.toolchain_runtime_sha256(root)
            (root / 'bin/lean').unlink()
            with self.assertRaisesRegex(ValueError, 'missing toolchain executable'):
                audit.toolchain_runtime_sha256(root)
            (root / 'bin/lean').write_bytes(b'lean')
            (root / 'lib/lean/Init.olean.hash').unlink()
            (root / 'lib/lean').rmdir()
            (root / 'lib/libleanshared.so').unlink()
            (root / 'lib').rmdir()
            with self.assertRaisesRegex(ValueError, 'missing toolchain library directory'):
                audit.toolchain_runtime_sha256(root)


if __name__ == "__main__":
    unittest.main()
