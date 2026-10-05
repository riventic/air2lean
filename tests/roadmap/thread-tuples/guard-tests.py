#!/usr/bin/env python3
"""Pure guard regressions; they do not start Zig, Lean, Lake, or elan."""
import copy
import hashlib
import json
import os
from pathlib import Path
import runpy
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
        for name in ("check.sh", "check-export.py"):
            shutil.copyfile(ROOT / name, self.fixture / name)
        (self.root / "scripts").mkdir()
        shutil.copyfile(ROOT.parents[2] / "scripts/normalize-generated.py",
                        self.root / "scripts/normalize-generated.py")
        profile = json.loads((ROOT.parent / "profiles/current.json").read_text())["profile"]
        (self.root / "profile.json").write_text(json.dumps(profile))
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
 if mode.startswith('profile'):
  data['schema']=12
  data['profile']=json.loads(Path('profile.json').read_text())
  if mode=='profile-malformed': data['profile'].pop('abi')
  if mode=='profile-mixed' and i==0: data['profile']['backend']='stage2_x86_64'
  if mode=='profile-mixed-schema' and i==0:
   data['schema']=11
   data.pop('profile')
  for suffix, key, value in [('target','target_triple','aarch64-macos-none'),('cpu','cpu','haswell'),
                            ('mode','build_mode','Debug'),('tracing','error_tracing',True)]:
   if mode=='profile-'+suffix: data['profile'][key]=value
  if mode=='profile-target': data['profile']['abi']='none'
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

    def test_current_profile(self):
        self.check(True, mode="profile")

    def test_malformed_profile(self):
        self.check(False, mode="profile-malformed", expected="profile fields")

    def test_mixed_profile(self):
        self.check(False, mode="profile-mixed", expected="mixed profiles")

    def test_mixed_schema(self):
        self.check(False, mode="profile-mixed-schema", expected="mixed profiles")

    def test_wrong_profile_export_flags(self):
        for mode in ("target", "cpu", "mode", "tracing"):
            with self.subTest(mode=mode):
                shutil.rmtree(self.root / "output", ignore_errors=True)
                self.check(False, mode="profile-" + mode, expected="explicit Linux/baseline ReleaseSafe flags")

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

class FreshAdapterProfile(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.check = runpy.run_path(str(ROOT / "check-export.py"))["check_export"]
        current = json.loads((ROOT.parent / "profiles/current.json").read_text())
        for name in ("mutableCapture", "strongCapture", "weakCapture", "sliceWorker"):
            self.doc = dict(current, name="thread_adapter_contract." + name)
            (self.root / (name + ".json")).write_text(json.dumps(self.doc))

    def set_profiles(self, triple, abi):
        for path in self.root.glob("*.json"):
            doc = json.loads(path.read_text())
            doc["profile"].update(target_triple=triple, abi=abi)
            path.write_text(json.dumps(doc))

    def test_actual_versioned_musl_target(self):
        self.set_profiles("x86_64-linux.5.10...6.19-musl", "musl")
        self.check(self.root, adapter=True)

    def test_versioned_gnu_target(self):
        self.set_profiles("x86_64-linux.5.10...6.19-gnu", "gnu")
        self.check(self.root, adapter=True)

    def test_wrong_arch_or_os(self):
        for triple, abi in (("aarch64-macos-none", "none"),
                            ("aarch64-linux.5.10...6.19-musl", "musl"),
                            ("x86_64-windows-gnu", "gnu")):
            with self.subTest(triple=triple):
                self.set_profiles(triple, abi)
                with self.assertRaises(ValueError):
                    self.check(self.root, adapter=True)

    def test_unsupported_or_inconsistent_abi(self):
        for triple, abi in (("x86_64-linux.5.10...6.19-none", "none"),
                            ("x86_64-linux.5.10...6.19-musl", "gnu")):
            with self.subTest(triple=triple, abi=abi):
                self.set_profiles(triple, abi)
                with self.assertRaises(ValueError):
                    self.check(self.root, adapter=True)

    def test_current_adapter_profile(self):
        self.check(self.root, adapter=True)

    def test_adapter_inventory_failure(self):
        (self.root / "sliceWorker.json").unlink()
        with self.assertRaisesRegex(ValueError, "function inventory"):
            self.check(self.root, adapter=True)

    def test_adapter_malformed_profile(self):
        self.doc["profile"]["pointer_bits"] = 32
        (self.root / "sliceWorker.json").write_text(json.dumps(self.doc))
        with self.assertRaisesRegex(ValueError, "incompatible target profile"):
            self.check(self.root, adapter=True)


class GeneratedReceipt(unittest.TestCase):
    """Exercise the exact shared report/compare calls used by the tuple gates."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.helpers = runpy.run_path(str(ROOT.parents[2] / "scripts/normalize-generated.py"))
        self.air = self.root / "air"
        self.air.mkdir()
        self.doc = json.loads((ROOT.parent / "profiles/current.json").read_text())
        self.input = self.air / "tuple.json"
        self.input.write_text(json.dumps(self.doc))
        self.body = b"import ZigLean\nnamespace ThreadTuples\ndef worker := 42\nend ThreadTuples\n"
        self.output = self.root / "Gen.lean"
        self.baseline = self.root / "Legacy.lean"
        self.baseline.write_bytes(self.body)
        self.report = self.root / "receipt.json"
        self.output.write_bytes(self.generated(self.doc))
        self.helpers["write_report"](self.output, self.air, self.report)

    def generated(self, doc):
        metadata = dict(profile=self.helpers["profile_for_air"](doc),
                        float_semantics="ieee", correspondence="model")
        return self.helpers["PREFIX"] + json.dumps(metadata).encode() + b"\n" + self.body

    def test_exact_air_and_generated_hash_binding(self):
        report = json.loads(self.report.read_text())
        self.assertEqual(report["generated_sha256"], hashlib.sha256(self.output.read_bytes()).hexdigest())
        self.assertEqual(report["air"], [{"file": self.input.name,
                                        "sha256": hashlib.sha256(self.input.read_bytes()).hexdigest()}])
        self.helpers["compare"](self.baseline, self.output, self.report)
        self.assertTrue(self.output.read_bytes().startswith(self.helpers["PREFIX"]))

    def test_full_generated_header_tamper(self):
        changed = copy.deepcopy(self.doc)
        changed["profile"]["backend"] = "stage2_x86_64"
        self.output.write_bytes(self.generated(changed))
        with self.assertRaisesRegex(ValueError, "validated check report"):
            self.helpers["compare"](self.baseline, self.output, self.report)

    def test_full_generated_body_tamper(self):
        self.output.write_bytes(self.output.read_bytes().replace(b"42", b"41"))
        with self.assertRaisesRegex(ValueError, "validated check report"):
            self.helpers["compare"](self.baseline, self.output, self.report)

    def test_fresh_body_diff(self):
        self.output.write_bytes(self.output.read_bytes().replace(b"42", b"41"))
        self.helpers["write_report"](self.output, self.air, self.report)
        with self.assertRaisesRegex(ValueError, "semantics changed"):
            self.helpers["compare"](self.baseline, self.output, self.report)

    def test_mixed_air_profile_cannot_create_receipt(self):
        changed = copy.deepcopy(self.doc)
        changed["profile"]["backend"] = "stage2_x86_64"
        (self.air / "other.json").write_text(json.dumps(changed))
        with self.assertRaisesRegex(ValueError, "AIR profile differs"):
            self.helpers["write_report"](self.output, self.air, self.report)


class ProofTrustScan(unittest.TestCase):
    """Run the real shell scan before the absent translator; no compiler is started."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.fixture = self.root / "tests/roadmap/thread-tuples"
        (self.fixture / "ThreadTuples").mkdir(parents=True)
        shutil.copyfile(ROOT / "check.sh", self.fixture / "check.sh")
        # Isolate the source scan from unrelated AIR/provenance checks.
        (self.fixture / "check-artifacts.py").write_text("pass\n")
        self.proof = self.fixture / "ThreadTuples/Proofs.lean"

    def check(self, expected):
        result = subprocess.run(["bash", str(self.fixture / "check.sh"), "--check-artifacts"],
            capture_output=True, text=True, env=dict(os.environ, AIR2LEAN_TRANSLATOR=str(self.root / "absent-translator")))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(expected, result.stdout + result.stderr)

    def test_clean_source_reaches_translator_check(self):
        self.proof.write_text("theorem clean : True := by trivial\n-- axiomatic sorry_name admit_ native_decideX\n")
        self.check("build the translator first")

    def test_each_forbidden_word_rejected(self):
        for word in ("sorry", "admit", "native_decide", "axiom"):
            with self.subTest(word=word):
                # The original scan also rejected forbidden words in comments.
                self.proof.write_text(f"theorem clean : True := by trivial\n-- {word}\n")
                self.check(f"proof contains an untrusted declaration: {self.proof.relative_to(self.root)}:2:")

    def test_unreadable_sources_rejected(self):
        self.check("proof scan failed:")  # Missing file.
        self.proof.mkdir()
        self.check("proof scan failed:")  # Directory cannot be read as source.
        self.proof.rmdir()
        self.proof.write_bytes(b"\xff")
        self.check("proof scan failed:")  # Invalid UTF-8 must not pass the scan.

if __name__ == "__main__":
    unittest.main()
