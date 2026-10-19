#!/usr/bin/env python3
"""Exercise cache invalidation and the extractor lock without running compiler processes outside
the build guard."""
import fcntl
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

sys.dont_write_bytecode = True
from test_policy import audit

INPUTS = ("tools/Assurance.lean", "lean-toolchain", "imported-dependency")


def make_root(directory: str) -> Path:
    root = Path(directory)
    (root / "tools").mkdir()
    (root / "tools/Assurance.lean").write_text("import Lean\n")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
    (root / "lakefile.toml").write_text('name = "test"\n')
    (root / "imported-dependency").write_text("original dependency")
    olean(root).parent.mkdir(parents=True)
    return root


def olean(root: Path) -> Path:
    return root / ".lake/build/lib/lean/tools/Assurance.olean"


class Lake:
    """Mock `lake --rehash build AssuranceTools`, which owns dependency freshness: it rebuilds a
    missing olean or one whose inputs changed. The olean's bytes follow from its inputs only, so
    two contexts that differ in the Lake configuration share them."""

    def __init__(self, root: Path):
        self.root, self.builds, self.validations = root, 0, 0

    def __call__(self, command):
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
        lake(command)

    with audit.prepared_tool(root, after_release) as trace:
        print(json.dumps(trace))


class ToolCacheTests(unittest.TestCase):
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

    def test_contexts_keep_their_own_records(self):
        # Two invocations in one worktree with different contexts (here the Lake configuration)
        # alternate: neither invalidates the other's record of the shared olean.
        with tempfile.TemporaryDirectory() as directory:
            root = make_root(directory)
            config, lake = root / "lakefile.toml", Lake(root)
            first, second = config.read_text(), 'name = "other context"\n'

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
                (root / "lakefile.toml").write_text('name = "other context"\n')
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

            def failed_builder(_):
                raise RuntimeError("compiler failed")

            with self.assertRaises(RuntimeError):
                with audit.prepared_tool(root, failed_builder):
                    pass
            self.assertEqual(list((root / ".lake/assurance").glob("tool-trace*/*")), [])


if __name__ == "__main__":
    if sys.argv[1:2] == ["--contend"]:
        contend(Path(sys.argv[2]))
    else:
        unittest.main()
