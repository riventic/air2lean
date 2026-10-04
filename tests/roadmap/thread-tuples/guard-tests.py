#!/usr/bin/env python3
"""Pure guard regressions; they do not start Zig, Lean, Lake, or elan."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent

class Guards(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        shutil.copyfile(ROOT / "check-artifacts.py", self.root / "check-artifacts.py")
        (self.root / "thread_tuples.zig").write_text("// original test source\n")
        self.air = self.root / "air/0.16.0"
        self.air.mkdir(parents=True)
        self.path = self.air / "thread_tuples.empty.json"
        self.path.write_text(json.dumps({"schema":11,"zig_version":"0.16.0", "target_endian":"little", "name":"thread_tuples.empty"}))
        self.manifest = {"source_sha256": hashlib.sha256((self.root / "thread_tuples.zig").read_bytes()).hexdigest(),
            "air":{"zig_version":"0.16.0","schema":11}, "functions":["empty"],
            "air_sha256":{self.path.name:hashlib.sha256(self.path.read_bytes()).hexdigest()}}
        self.save()

    def save(self):
        (self.root / "provenance.json").write_text(json.dumps(self.manifest))

    def check(self, passes, expected=""):
        p = subprocess.run(["python3", str(self.root / "check-artifacts.py")], capture_output=True, text=True)
        self.assertEqual(p.returncode == 0, passes, p.stdout + p.stderr)
        if expected:
            self.assertIn(expected, p.stdout + p.stderr)

    def test_current(self):
        self.check(True)

    def test_source_stale(self):
        (self.root / "thread_tuples.zig").write_text("// mutated\n")
        self.check(False, "stale thread tuple source")

    def test_manifest_hash_invalid(self):
        self.manifest["source_sha256"] = "z" * 64
        self.save()
        self.check(False, "invalid source_sha256")

    def test_air_stale(self):
        self.path.write_text(self.path.read_text() + "\n")
        self.check(False, "stale checked AIR hash")

    def test_air_missing(self):
        self.path.unlink()
        self.check(False, "filename inventory")

    def test_air_extra(self):
        shutil.copyfile(self.path, self.air / "extra.json")
        self.check(False, "filename inventory")

    def test_wrong_schema(self):
        data = json.loads(self.path.read_text())
        data["schema"] = 10
        self.path.write_text(json.dumps(data))
        self.manifest["air_sha256"][self.path.name] = hashlib.sha256(self.path.read_bytes()).hexdigest()
        self.save()
        self.check(False, "wrong schema")

    def test_wrong_function(self):
        data = json.loads(self.path.read_text())
        data["name"] = "thread_tuples.wrong"
        self.path.write_text(json.dumps(data))
        self.manifest["air_sha256"][self.path.name] = hashlib.sha256(self.path.read_bytes()).hexdigest()
        self.save()
        self.check(False, "function inventory")

class ExportGate(unittest.TestCase):
    """The fake executable writes JSON only; no compiler is started."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.fixture = self.root / "tests/roadmap/thread-tuples"
        self.fixture.mkdir(parents=True)
        shutil.copyfile(ROOT / "check.sh", self.fixture / "check.sh")
        self.manifest = {"functions":["empty", "genericEmpty", "ZeroWorker(u8).run", "groupMixed"],
            "stdlib_functions":["atomic.Value(u32).init"]}
        (self.fixture / "provenance.json").write_text(json.dumps(self.manifest))
        (self.fixture / "filter").write_text("thread_tuples\natomic.Value(u32).init\n")
        self.tool = self.root / "fake-air-writer"
        self.tool.write_text("""#!/usr/bin/env python3
import json, os
from pathlib import Path
manifest=json.loads(Path('tests/roadmap/thread-tuples/provenance.json').read_text())
mode=os.environ.get('FAKE_AIR_MODE','good')
version=os.environ.get('FAKE_AIR_VERSION','0.16.0')
names=['thread_tuples.'+n for n in manifest['functions']] + manifest['stdlib_functions']
if version!='0.16.0': names.remove('thread_tuples.groupMixed')
if mode=='missing': names.pop()
if mode=='duplicate': names.append(names[0])
for i, name in enumerate(names):
 data={'name':name,'schema':10 if mode=='schema' else 11,'zig_version':version,'target_endian':'little'}
 (Path(os.environ['ZIG_AIR_JSON_DIR'])/(str(i)+'.json')).write_text(json.dumps(data))
""")
        self.tool.chmod(0o755)

    def check(self, passes, mode="good", version="0.16.0", expected=""):
        env = dict(os.environ, AIR2LEAN_ZIG_AIR=str(self.tool), FAKE_AIR_MODE=mode, FAKE_AIR_VERSION=version)
        p = subprocess.run(["bash", str(self.fixture / "check.sh"), "--export", str(self.root / "output")],
            capture_output=True, text=True, env=env)
        self.assertEqual(p.returncode == 0, passes, p.stdout + p.stderr)
        if expected:
            self.assertIn(expected, p.stdout + p.stderr)

    def test_complete(self):
        self.check(True)

    def test_previous_version_no_group(self):
        self.check(True, version="0.15.2")

    def test_missing_callee(self):
        self.check(False, mode="missing", expected="function inventory")

    def test_duplicate_function(self):
        self.check(False, mode="duplicate", expected="function inventory")

    def test_wrong_schema(self):
        self.check(False, mode="schema", expected="wrong schema")

    def test_failed_filter(self):
        (self.fixture / "filter").unlink()
        self.check(False, expected="filter")

if __name__ == "__main__":
    unittest.main()
