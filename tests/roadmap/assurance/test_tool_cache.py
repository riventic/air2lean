#!/usr/bin/env python3
"""Exercise cache invalidation and the extractor lock without running compiler processes outside
the build guard."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
from test_policy import audit

INPUTS = ("tools/Assurance.lean", "lean-toolchain", "imported-dependency")


def make_root(directory: str) -> Path:
    root = toolchain(Path(directory))
    (root / "tools").mkdir()
    (root / "tools/Assurance.lean").write_text("import Lean\n")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
    (root / "lakefile.toml").write_text('name = "test"\n[[lean_lib]]\nname = "tools"\n')
    (root / "imported-dependency").write_text("original dependency")
    olean(root).parent.mkdir(parents=True)
    return root


def olean(root: Path) -> Path:
    return root / ".lake/build/lib/lean/tools/Assurance.olean"


def record_of(root: Path, trace: dict) -> Path:
    """The per-context record `prepared_tool` wrote for `trace`."""
    found = [r for r in (root / ".lake/assurance/tool-traces").glob("*.json") if json.loads(r.read_text()) == trace]
    assert len(found) == 1, found
    return found[0]


class Lake:
    """Mock `lake --rehash build AssuranceTools`, which owns dependency freshness: it rebuilds a
    missing olean or one whose inputs changed. The olean's bytes follow from its inputs only, so
    two contexts that differ in the Lake configuration share them. The root is the sysroot."""

    def __init__(self, root: Path):
        self.root, self.builds, self.validations = root, 0, 0

    def __call__(self, command):
        if command == ["lake", "env", "printenv", "LEAN_SYSROOT"]:
            return str(self.root)
        assert command == ["lake", "--rehash", "build", "AssuranceTools"], command
        self.validations += 1
        inputs = b"".join((self.root / name).read_bytes() for name in INPUTS)
        artifact, trace = olean(self.root), olean(self.root).with_suffix(".trace")
        if not artifact.is_file() or not trace.is_file() or trace.read_bytes() != hashlib.sha256(inputs).digest():
            self.builds += 1
            artifact.write_bytes(b"checked artifact: " + inputs)
            trace.write_bytes(hashlib.sha256(inputs).digest())


def contend(root: Path) -> None:
    """The second invocation of the lock test (a separate process): mark when the extractor lock
    blocks it, then prepare and print the trace."""
    flock = fcntl.flock

    def reporting_flock(descriptor, operation):
        try:
            flock(descriptor, operation | fcntl.LOCK_NB)
        except BlockingIOError:
            (root / "blocked").touch()
            flock(descriptor, operation)

    fcntl.flock = reporting_flock
    lake = Lake(root)

    def after_release(command):
        assert (root / "released").is_file(), "prepared while the first holder had the lock"
        return lake(command)

    with audit.prepared_tool(root, after_release) as trace:
        print(json.dumps(trace))


def toolchain(root):
    (root / 'bin').mkdir(parents=True)
    for name in ('lean', 'leanchecker'):
        (root / 'bin' / name).write_bytes(name.encode())
    (root / 'lib/lean').mkdir(parents=True)
    (root / 'lib/libleanshared.so').write_bytes(b'runtime1')
    return root


def no_record(root: Path) -> bool:
    return list((root / ".lake/assurance").glob("tool-trace*/*")) == []


class ToolCacheTests(unittest.TestCase):
    def project(self, root):
        toolchain(root)
        (root / 'tools').mkdir()
        (root / 'tools/Assurance.lean').write_text('import Lean\n')
        (root / 'lean-toolchain').write_text('pin\n')
        (root / 'lakefile.toml').write_text('name = "test"\n[[lean_lib]]\nname = "tools"\n')
        artifact = root / '.lake/build/lib/lean/tools/Assurance.olean'

        def build(command):
            if command == ['lake', 'env', 'printenv', 'LEAN_SYSROOT']:
                return str(root)
            self.assertEqual(command, ['lake', '--rehash', 'build', 'AssuranceTools'])
            artifact.parent.mkdir(parents=True, exist_ok=True)
            artifact.write_bytes(b'fixed compiled extractor')
            artifact.with_suffix('.trace').write_bytes(b'fixed Lake trace')

        return build

    @staticmethod
    def prepare(root, runner):
        with audit.prepared_tool(root, runner) as trace:
            return trace

    def test_verified_cache_reuse_and_invalidation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = make_root(directory)
            source, pin, artifact, lake = root / INPUTS[0], root / INPUTS[1], olean(root), Lake(root)

            def prepare():
                with audit.prepared_tool(root, lake) as trace:
                    self.assertEqual(trace["olean_sha256"], audit.file_sha256(artifact))
                    self.assertEqual(trace["lake_trace_sha256"], audit.file_sha256(artifact.with_suffix(".trace")))
                    return trace

            self.assertFalse(prepare()["cache_reused"])
            self.assertTrue(prepare()["cache_reused"])
            self.assertEqual(lake.builds, 1)
            source.write_text(source.read_text() + "-- extractor changed\n")
            self.assertFalse(prepare()["cache_reused"])
            pin.write_text("leanprover/lean4:changed-release-pin\n")
            self.assertFalse(prepare()["cache_reused"])
            artifact.write_bytes(b"invalid cached tool")
            self.assertFalse(prepare()["cache_reused"])
            artifact.unlink()
            self.assertFalse(prepare()["cache_reused"])
            (root / "imported-dependency").write_text("changed imported dependency")
            self.assertFalse(prepare()["cache_reused"])
            self.assertEqual(lake.builds, 6)
            self.assertEqual(lake.validations, 7)
            # Same executable, path, size and mtime do not identify the loaded runtime.
            library = root / 'lib/libleanshared.so'
            saved = library.stat()
            library.write_bytes(b'runtime2')
            os.utime(library, ns=(saved.st_atime_ns, saved.st_mtime_ns))
            self.assertFalse(prepare()['cache_reused'])
            self.assertTrue(prepare()['cache_reused'])
            self.assertEqual(lake.builds, 7)
            # Installed logical/IR inputs are also loaded by the extractor's pinned Lean.
            for suffix in audit.COMPILED_SUFFIXES:
                companion = root / ('lib/lean/Init' + suffix)
                companion.write_bytes(b'original')
                self.assertFalse(prepare()['cache_reused'])
                companion.write_bytes(b'modified')
                self.assertFalse(prepare()['cache_reused'])
                companion.unlink()
                # Back to the runtime without the companion: that context's record still matches.
                trace = prepare()
                self.assertTrue(trace['cache_reused'])
            for field in ('toolchain_runtime_sha256', 'caller_lean_path'):
                record = record_of(root, trace)
                unbound = json.loads(record.read_text())
                del unbound[field]
                record.write_text(json.dumps(unbound))
                trace = prepare()
                self.assertFalse(trace['cache_reused'])

    def test_contexts_keep_their_own_records(self):
        # Two invocations in one worktree with different contexts (here the Lake configuration)
        # alternate: neither invalidates the other's record of the shared olean.
        with tempfile.TemporaryDirectory() as directory:
            root = make_root(directory)
            config, lake = root / "lakefile.toml", Lake(root)
            first, second = config.read_text(), 'name = "other context"\n[[lean_lib]]\nname = "tools"\n'

            def reused(text):
                config.write_text(text)
                with audit.prepared_tool(root, lake) as trace:
                    return trace["cache_reused"]

            # The second context has no record yet: the olean is unlinked and Lake rebuilds it.
            self.assertEqual([reused(first), reused(second), reused(first), reused(second)],
                             [False, False, True, True])
            self.assertEqual(lake.builds, 2)
            records = list((root / ".lake/assurance/tool-traces").glob("*.json"))
            self.assertEqual(len(records), 2)
            # A corrupt record forces a rebuild for its context only.
            first_sha = hashlib.sha256(first.encode()).hexdigest()
            corrupt, = [r for r in records if json.loads(r.read_text())["lake_config_sha256"] == first_sha]
            corrupt.write_text("{corrupt")
            self.assertEqual([reused(first), reused(second)], [False, True])
            self.assertEqual(lake.builds, 3)

    def test_lock_keeps_the_olean_while_a_holder_imports_it(self):
        with tempfile.TemporaryDirectory() as directory:
            root = make_root(directory)
            artifact = olean(root)
            with audit.prepared_tool(root, Lake(root)) as trace:
                # The body stands for the `lake env lean` run importing the olean. A second
                # invocation with another context (no record yet) would unlink and rebuild it.
                (root / "lakefile.toml").write_text('name = "other context"\n[[lean_lib]]\nname = "tools"\n')
                child = subprocess.Popen([sys.executable, "-B", __file__, "--contend", str(root)],
                                         stdout=subprocess.PIPE, text=True)
                try:
                    deadline = time.monotonic() + 60
                    while not (root / "blocked").exists():
                        self.assertIsNone(child.poll(), "the second invocation did not wait for the lock")
                        self.assertLess(time.monotonic(), deadline, "the second invocation never took the lock")
                        time.sleep(0.01)
                    self.assertEqual(audit.file_sha256(artifact), trace["olean_sha256"])
                    (root / "released").touch()
                except BaseException:
                    child.kill()
                    raise
            output, _ = child.communicate(timeout=60)
            self.assertEqual(child.returncode, 0)
            self.assertFalse(json.loads(output)["cache_reused"])

    def test_lock_error_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = make_root(directory)
            (root / ".lake/assurance/tool.lock").mkdir(parents=True)
            lake = Lake(root)
            with self.assertRaises(OSError):
                with audit.prepared_tool(root, lake):
                    pass
            self.assertEqual(lake.validations, 0)

    def test_failed_preparation_never_publishes_valid_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            root = make_root(directory)

            def failed_builder(command):
                if command == ['lake', 'env', 'printenv', 'LEAN_SYSROOT']:
                    return str(root)
                raise RuntimeError("compiler failed")

            with self.assertRaises(RuntimeError):
                with audit.prepared_tool(root, failed_builder):
                    pass
            self.assertTrue(no_record(root))

    def test_changed_runtime_during_preparation_does_not_publish_trace(self):
        with tempfile.TemporaryDirectory() as directory:
            root = toolchain(Path(directory))
            (root / 'tools').mkdir()
            (root / 'tools/Assurance.lean').write_text('import Lean\n')
            (root / 'lean-toolchain').write_text('pin\n')
            (root / 'lakefile.toml').write_text('name = "test"\n[[lean_lib]]\nname = "tools"\n')

            def changing_builder(command):
                if command == ['lake', 'env', 'printenv', 'LEAN_SYSROOT']:
                    return str(root)
                self.assertEqual(command, ['lake', '--rehash', 'build', 'AssuranceTools'])
                (root / 'lib/libleanshared.so').write_bytes(b'runtime2')

            with self.assertRaisesRegex(ValueError, 'runtime changed during extractor preparation'):
                self.prepare(root, changing_builder)
            self.assertTrue(no_record(root))

    def test_empty_sysroot_is_rejected_before_using_current_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = toolchain(Path(directory))
            for value, error in [(' \n', 'empty'), ('relative', 'nonabsolute')]:
                calls = []

                def invalid_sysroot(command):
                    calls.append(command)
                    return value

                with self.assertRaisesRegex(ValueError, error + ' LEAN_SYSROOT'):
                    self.prepare(root, invalid_sysroot)
                self.assertEqual(calls, [['lake', 'env', 'printenv', 'LEAN_SYSROOT']])
            self.assertTrue(no_record(root))

    def test_private_caller_paths_remain_supported_but_changes_invalidate(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build = self.project(root)
            private = root / 'private'
            private.mkdir()
            with patch.dict(os.environ, {'LEAN_PATH': 'private'}):
                first = self.prepare(root, build)
                self.assertEqual(first['caller_lean_path']['roots'], [str(private)])
                self.assertTrue(self.prepare(root, build)['cache_reused'])
                # Keep every extractor/trace byte fixed; only a private input changes.
                for name in ('Witness.olean', 'Witness.olean.private', 'Witness.olean.server',
                             'Witness.ir', 'Witness.ir.sig'):
                    companion = private / name
                    companion.write_bytes(b'original')
                    self.assertFalse(self.prepare(root, build)['cache_reused'])
                    saved = companion.stat()
                    companion.write_bytes(b'modified')
                    os.utime(companion, ns=(saved.st_atime_ns, saved.st_mtime_ns))
                    self.assertFalse(self.prepare(root, build)['cache_reused'])
                    companion.unlink()
                    # Back to the caller tree without the companion: its record still matches.
                    self.assertTrue(self.prepare(root, build)['cache_reused'])
                (private / 'EmptyTop').mkdir()
                self.assertFalse(self.prepare(root, build)['cache_reused'])
                second = root / 'second'
                second.mkdir()
                os.environ['LEAN_PATH'] = os.pathsep.join(map(str, [private, second]))
                forward = self.prepare(root, build)
                os.environ['LEAN_PATH'] = os.pathsep.join(map(str, [second, private]))
                backward = self.prepare(root, build)
                self.assertNotEqual(forward['caller_lean_path'], backward['caller_lean_path'])
                self.assertFalse(backward['cache_reused'])
                (second / 'EmptyTop').mkdir()
                alias = root / 'alias'
                alias.symlink_to(private, target_is_directory=True)
                os.environ['LEAN_PATH'] = str(alias)
                linked = self.prepare(root, build)
                alias.unlink()
                alias.symlink_to(second, target_is_directory=True)
                retargeted = self.prepare(root, build)
                self.assertNotEqual(linked['caller_lean_path'], retargeted['caller_lean_path'])
                self.assertFalse(retargeted['cache_reused'])
                record = record_of(root, retargeted)
                unbound = json.loads(record.read_text())
                del unbound['caller_lean_path']
                record.write_text(json.dumps(unbound))
                self.assertFalse(self.prepare(root, build)['cache_reused'])

    def test_caller_mutation_during_preparation_or_extraction_fails_closed(self):
        for stage in ('unchanged', 'preparation', 'extraction'):
            with self.subTest(stage=stage), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                build = self.project(root)
                private = root / 'private'
                private.mkdir()
                dependency = private / 'Witness.ir.sig'
                dependency.write_bytes(b'original')

                def runner(command, *, root=root):
                    if command[:3] == ['lake', 'env', 'lean']:
                        if stage == 'extraction':
                            dependency.write_bytes(b'modified')
                        return audit.MARKER + json.dumps({'modules': ['Proofs.Fixture'], 'nodes': []})
                    result = build(command)
                    if stage == 'preparation' and command[:3] == ['lake', '--rehash', 'build']:
                        dependency.write_bytes(b'modified')
                    return result

                with patch.dict(os.environ, {'LEAN_PATH': str(private)}), \
                        patch.object(audit, 'ROOT', root), patch.object(audit, 'run', runner):
                    if stage == 'unchanged':
                        raw = audit.extract(['Proofs.Fixture'], False)
                        self.assertEqual(raw['modules'], ['Proofs.Fixture'])
                        self.assertEqual(raw['extractor']['caller_lean_path']['roots'], [str(private)])
                    else:
                        with self.assertRaisesRegex(ValueError, 'LEAN_PATH changed during extractor ' + stage):
                            audit.extract(['Proofs.Fixture'], False)
                self.assertEqual(list((root / '.lake/assurance').glob('*.lean')), [])
                if stage == 'preparation':
                    self.assertTrue(no_record(root))

    def test_sysroot_overlay_and_invalid_caller_roots_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build = self.project(root)
            with patch.dict(os.environ, {'LEAN_SYSROOT': str(root)}):
                with self.assertRaisesRegex(ValueError, 'unsupported caller LEAN_SYSROOT'):
                    self.prepare(root, build)
            with patch.dict(os.environ, {'LEAN_PATH': 'private' + os.pathsep}):
                with self.assertRaisesRegex(ValueError, 'empty root in caller LEAN_PATH'):
                    self.prepare(root, build)
            with patch.dict(os.environ, {'LEAN_PATH': str(root / 'lean-toolchain')}):
                with self.assertRaisesRegex(ValueError, 'root is not a directory'):
                    self.prepare(root, build)


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

class SourceInputTests(unittest.TestCase):
    prepare = staticmethod(ToolCacheTests.prepare)

    def source_project(self, root):
        make_root(str(root))
        (root / 'tools/Assurance.lean').write_text('import tools.Helper\n')
        (root / 'tools/Helper.lean').write_text('def value := 1\n')
        return Lake(root), olean(root)

    def test_helper_source_change_invalidates_trace_with_fixed_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build, artifact = self.source_project(root)
            self.prepare(root, build)
            self.assertTrue(self.prepare(root, build)['cache_reused'])
            fixed = artifact.read_bytes(), artifact.with_suffix('.trace').read_bytes()
            helper = root / 'tools/Helper.lean'
            saved = helper.stat()
            helper.write_text('def value := 2\n')
            os.utime(helper, ns=(saved.st_atime_ns, saved.st_mtime_ns))
            changed = self.prepare(root, build)
            self.assertFalse(changed['cache_reused'])
            self.assertEqual(fixed, (artifact.read_bytes(), artifact.with_suffix('.trace').read_bytes()))
            self.assertEqual(changed['library_source_inputs'], audit.library_source_inputs(root))
            self.assertTrue(self.prepare(root, build)['cache_reused'])
            external = root / 'outside-library.lean'
            external.write_bytes(helper.read_bytes())
            helper.unlink()
            helper.symlink_to(external)
            self.assertFalse(self.prepare(root, build)['cache_reused'])
            other = root / 'same-bytes.lean'
            other.write_bytes(external.read_bytes())
            helper.unlink()
            helper.symlink_to(other)
            self.assertFalse(self.prepare(root, build)['cache_reused'])
            helper.unlink()
            helper.symlink_to(external)
            external.write_text('def value := 3\n')
            self.assertFalse(self.prepare(root, build)['cache_reused'])
            extra = root / 'tools/Unused.lean'
            extra.write_text('def unused := 1\n')
            self.assertFalse(self.prepare(root, build)['cache_reused'])
            extra.unlink()
            latest = self.prepare(root, build)
            self.assertFalse(latest['cache_reused'])
            manifest = record_of(root, latest)
            unbound = json.loads(manifest.read_text())
            del unbound['library_source_inputs']
            manifest.write_text(json.dumps(unbound))
            self.assertFalse(self.prepare(root, build)['cache_reused'])
            self.assertEqual(fixed, (artifact.read_bytes(), artifact.with_suffix('.trace').read_bytes()))

    def test_source_mutation_during_preparation_and_extraction_is_rejected(self):
        for stage in ('unchanged', 'preparation', 'extraction'):
            with self.subTest(stage=stage), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                build, _ = self.source_project(root)

                def run(command, *, root=root):
                    if command[:3] == ['lake', 'env', 'lean']:
                        if stage == 'extraction':
                            (root / 'tools/Helper.lean').write_text('def value := 2\n')
                        return audit.MARKER + json.dumps({'modules': ['Proofs.Fixture'], 'nodes': []})
                    result = build(command)
                    if stage == 'preparation' and command[:3] == ['lake', '--rehash', 'build']:
                        (root / 'tools/Helper.lean').write_text('def value := 2\n')
                    return result

                with patch.object(audit, 'ROOT', root), patch.object(audit, 'run', run):
                    if stage == 'unchanged':
                        self.assertEqual(audit.extract(['Proofs.Fixture'], False)['modules'], ['Proofs.Fixture'])
                    else:
                        with self.assertRaisesRegex(ValueError, 'sources changed during extractor ' + stage):
                            audit.extract(['Proofs.Fixture'], False)
                if stage == 'preparation':
                    self.assertTrue(no_record(root))


    def test_manifest_add_change_and_remove_bind_the_current_state(self):
        for before, after in ((None, '{}'), ('{}', '{"changed":true}'), ('{}', None)):
            with self.subTest(before=before, after=after), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                build, _ = self.source_project(root)
                manifest = root / 'lake-manifest.json'
                if before is not None:
                    manifest.write_text(before)
                first = self.prepare(root, build)
                self.assertTrue(self.prepare(root, build)['cache_reused'])
                if after is None:
                    manifest.unlink()
                else:
                    manifest.write_text(after)
                changed = self.prepare(root, build)
                self.assertNotEqual(first['library_source_inputs'], changed['library_source_inputs'])
                self.assertFalse(changed['cache_reused'])
                latest = self.prepare(root, build)
                self.assertTrue(latest['cache_reused'])
                record = record_of(root, latest)
                unbound = json.loads(record.read_text())
                del unbound['lake_manifest_sha256']
                record.write_text(json.dumps(unbound))
                self.assertFalse(self.prepare(root, build)['cache_reused'])

    def test_configuration_mutations_are_rejected_in_both_phases(self):
        for stage in ('preparation', 'extraction'):
            for name in ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json'):
                with self.subTest(stage=stage, name=name), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    build, _ = self.source_project(root)

                    def runner(command, *, root=root):
                        phase = 'extraction' if command[:3] == ['lake', 'env', 'lean'] else 'preparation'
                        if phase == 'extraction':
                            result = audit.MARKER + json.dumps({'modules': ['Proofs.Fixture'], 'nodes': []})
                        else:
                            result = build(command)
                        if phase == stage and command[:3] != ['lake', 'env', 'printenv']:
                            path = root / name
                            path.write_text(path.read_text() + '\n# changed\n' if path.exists() else '{}')
                        return result

                    with patch.object(audit, 'ROOT', root), patch.object(audit, 'run', runner):
                        with self.assertRaisesRegex(ValueError, 'sources changed during extractor ' + stage):
                            audit.extract(['Proofs.Fixture'], False)
                    if stage == 'preparation':
                        self.assertTrue(no_record(root))

    def test_source_selection_uses_the_shared_alias_traversal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.source_project(root)
            (root / 'tools.lean').write_text('import tools.Helper\n')
            (root / 'Other').mkdir()
            (root / 'Other/Unused.lean').write_text('def unused := 1\n')
            (root / 'lakefile.toml').write_text(
                '[[lean_lib]]\nname = "Extractor"\nroots = ["tools.Assurance"]\nglobs = ["Other.+"]\n')
            inputs = audit.library_source_inputs(root)
            files = {path for path, _, content in inputs if content}
            self.assertTrue({'tools.lean', 'tools/Helper.lean', 'Other/Unused.lean'} <= files)
            (root / 'external').mkdir()
            target = root / 'external/Only.lean'
            target.write_text('def only := 1\n')
            alias = root / 'tools/alias'
            alias.symlink_to(root / 'external', target_is_directory=True)
            linked = audit.library_source_inputs(root)
            self.assertNotEqual(inputs, linked)
            target.write_text('def only := 2\n')
            self.assertNotEqual(linked, audit.library_source_inputs(root))
            target.unlink()
            alias.unlink()
            alias.symlink_to(root / 'missing', target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'missing compiled input symlink target'):
                audit.library_source_inputs(root)
            alias.unlink()
            alias.symlink_to(root / 'tools', target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'cyclic compiled input directory'):
                audit.library_source_inputs(root)
            alias.unlink()
            (root / 'lakefile.toml').write_text('[[lean_lib]]\nname = "Missing"\n')
            with self.assertRaisesRegex(ValueError, 'Missing.*no Lean sources'):
                audit.library_source_inputs(root)

    def test_extract_forwards_the_selected_root_to_every_phase(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build, _ = self.source_project(root)
            selected = []

            def runner(command, *, root):
                selected.append(root)
                if command[:3] == ['lake', 'env', 'lean']:
                    self.assertEqual(Path(command[-1]).parent, root / '.lake/assurance')
                    return audit.MARKER + json.dumps({'modules': ['Proofs.Fixture'], 'nodes': []})
                return build(command)

            with patch.object(audit, 'run', runner):
                raw = audit.extract(['Proofs.Fixture'], False, root=root)
                relative = Path(os.path.relpath(root))
                audit.extract(['Proofs.Fixture'], False, root=relative)
            self.assertTrue(selected)
            self.assertEqual({path.resolve() for path in selected}, {root.resolve()})
            self.assertEqual(raw['extractor']['library_source_inputs'], audit.library_source_inputs(root))


if __name__ == "__main__":
    if sys.argv[1:2] == ["--contend"]:
        contend(Path(sys.argv[2]))
    else:
        unittest.main()
