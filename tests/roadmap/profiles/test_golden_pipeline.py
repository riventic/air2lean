#!/usr/bin/env python3
"""Profile/golden receipt regressions; only fake Zig/Lake tools are invoked."""
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

ROOT = Path(__file__).resolve().parents[3]
HELPER = runpy.run_path(str(ROOT / "scripts/normalize-generated.py"))
NORMALIZER = runpy.run_path(str(ROOT / "scripts/normalize-air.py"))
CURRENT = json.loads((Path(__file__).parent / "current.json").read_text())
LEGACY = json.loads((Path(__file__).parent / "legacy.json").read_text())
BODY = b"import ZigLean\nnamespace Basic\ndef checked := 42\nend Basic\n"


def generated(doc, body=BODY, semantics="ieee"):
    metadata = dict(profile=HELPER["profile_for_air"](doc), float_semantics=semantics, correspondence="model")
    return HELPER["PREFIX"] + json.dumps(metadata).encode() + b"\n" + body


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="air2lean-golden-receipt-")
        self.directory = Path(self.temp.name)
        self.air = self.directory / "air"
        self.air.mkdir()
        self.input = self.air / "one.json"
        self.input.write_text(json.dumps(CURRENT))
        self.output = self.directory / "Gen.lean"
        self.output.write_bytes(generated(CURRENT))
        self.report = self.directory / "report.json"
        HELPER["write_report"](self.output, self.air, self.report)

    def tearDown(self):
        self.temp.cleanup()

    def test_full_artifact_hash_and_profile_recorded(self):
        report = json.loads(self.report.read_text())
        self.assertEqual(report["generated_sha256"], hashlib.sha256(self.output.read_bytes()).hexdigest())
        self.assertEqual(report["metadata"]["profile"]["name"], "abi64-le-v1")
        self.assertEqual(report["air"][0]["sha256"], hashlib.sha256(self.input.read_bytes()).hexdigest())

    def test_legacy_generated_body_compares_but_output_keeps_header(self):
        baseline = self.directory / "baseline.lean"
        baseline.write_bytes(BODY)
        HELPER["compare"](baseline, self.output, self.report)
        self.assertTrue(self.output.read_bytes().startswith(HELPER["PREFIX"]))
        baseline.write_bytes(generated(LEGACY))
        HELPER["compare"](baseline, self.output, self.report)

    def test_real_generated_body_change_fails(self):
        baseline = self.directory / "baseline.lean"
        baseline.write_bytes(BODY.replace(b"42", b"41"))
        with self.assertRaisesRegex(ValueError, "semantics changed"):
            HELPER["compare"](baseline, self.output, self.report)

    def test_mutated_actual_source_fails_even_when_only_header_changed(self):
        changed = copy.deepcopy(CURRENT)
        changed["profile"]["cpu"] = "haswell"
        self.output.write_bytes(generated(changed))
        with self.assertRaisesRegex(ValueError, "validated check report"):
            HELPER["checked_generated"](self.output, self.report)

    def test_mixed_inputs_and_missing_header_fail(self):
        changed = copy.deepcopy(CURRENT)
        changed["profile"]["build_mode"] = "Debug"
        self.input.write_text(json.dumps(changed))
        with self.assertRaisesRegex(ValueError, "AIR profile differs"):
            HELPER["write_report"](self.output, self.air, self.report)
        self.output.write_bytes(BODY)
        with self.assertRaisesRegex(ValueError, "first-line profile"):
            HELPER["write_report"](self.output, self.air, self.report)

    def test_malformed_and_nonfirst_headers_remain_rejected_or_observable(self):
        with self.assertRaises(ValueError):
            HELPER["split_generated"](HELPER["PREFIX"] + b"{}\n" + BODY)
        with self.assertRaises(ValueError):
            HELPER["split_generated"](HELPER["PREFIX"] + b'{"profile":{},"profile":{}}\n')
        data = b"-- another comment\n" + generated(CURRENT)
        self.assertEqual(HELPER["split_generated"](data), (None, data))

    def test_schema_transition_requires_receipt_and_preserves_nested_data(self):
        plain = NORMALIZER["normalize"](CURRENT)
        self.assertEqual(plain["schema"], 12)
        self.assertIn("profile", plain)
        receipt = json.loads(self.report.read_text())["metadata"]["profile"]
        actual = NORMALIZER["normalize"](CURRENT, checked_profile=receipt, actual=True)
        legacy = NORMALIZER["normalize"](LEGACY, checked_profile=receipt)
        self.assertEqual(actual, legacy)
        changed = copy.deepcopy(CURRENT)
        changed["body"][0]["profile"] = {"schema": 999, "name": "observable"}
        normalized = NORMALIZER["normalize"](changed, checked_profile=receipt, actual=True)
        self.assertEqual(normalized["body"][0]["profile"], changed["body"][0]["profile"])

    def test_unsupported_golden_schema_and_profile_are_not_stripped(self):
        receipt = json.loads(self.report.read_text())["metadata"]["profile"]
        changed = copy.deepcopy(CURRENT)
        changed["schema"] = 13
        with self.assertRaisesRegex(ValueError, "unsupported AIR schema"):
            NORMALIZER["normalize"](changed, checked_profile=receipt)
        changed = copy.deepcopy(CURRENT)
        changed["profile"]["endian"] = "big"
        with self.assertRaisesRegex(ValueError, "incompatible target"):
            NORMALIZER["normalize"](changed, checked_profile=receipt)
        old = copy.deepcopy(LEGACY)
        old["schema"] = 10
        self.assertEqual(NORMALIZER["normalize"](old, checked_profile=receipt)["schema"], 10)

    def test_changed_air_after_receipt_fails_cli(self):
        changed = copy.deepcopy(CURRENT)
        changed["name"] = "changed"
        self.input.write_text(json.dumps(changed))
        result = subprocess.run(["python3", str(ROOT / "scripts/normalize-air.py"), str(self.input),
                                 "--check-report", str(self.report), "--actual"], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("AIR artifact does not match", result.stderr)


class FakePipelineTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="air2lean-profile-pipeline-")
        self.repo = Path(self.temp.name)
        for relative in ("scripts", "bin", "examples/basic", "tests/golden/basic/air", "Proofs/Basic"):
            (self.repo / relative).mkdir(parents=True)
        for name in ("check.sh", "normalize-air.py", "normalize-generated.py"):
            shutil.copy2(ROOT / "scripts" / name, self.repo / "scripts" / name)
        (self.repo / "examples/basic/basic.zig").touch()
        self.fixture = copy.deepcopy(CURRENT)
        self.fixture["name"] = "basic.fixture"
        self.legacy = copy.deepcopy(self.fixture)
        self.legacy.pop("profile")
        self.legacy["schema"] = 11
        (self.repo / "tests/golden/basic/air/basic.fixture.json").write_text(json.dumps(self.legacy))
        (self.repo / "fixture.json").write_text(json.dumps(self.fixture))
        (self.repo / "generated.txt").write_bytes(generated(self.fixture))
        self.proof = self.repo / "Proofs/Basic/Gen.lean"
        self.proof.write_bytes(BODY)
        (self.repo / "bin/zig").write_text('''#!/usr/bin/env python3
import os
from pathlib import Path
import shutil
shutil.copyfile("fixture.json", Path(os.environ["ZIG_AIR_JSON_DIR"]) / "basic.fixture.json")
''')
        (self.repo / "bin/lake").write_text('''#!/usr/bin/env python3
import os
from pathlib import Path
import shutil
import sys
args = sys.argv[1:]
with Path("calls.log").open("a") as log: log.write(" ".join(args) + "\\n")
if args[0] == "exe":
    if os.environ.get("FAKE_TRANSLATOR_FAIL"):
        print("invalid actual profile rejected", file=sys.stderr)
        sys.exit(1)
    shutil.copyfile("generated.txt", args[args.index("-o") + 1])
elif os.environ.get("FAKE_PROOF_FAIL"):
    print("proof gate rejected generated source", file=sys.stderr)
    sys.exit(1)
''')
        for tool in ("zig", "lake"):
            (self.repo / "bin" / tool).chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.repo / "bin") + os.pathsep + os.environ["PATH"],
                        AIR2LEAN_ZIG_AIR=str(self.repo / "bin/zig"), AIR2LEAN_EXAMPLES="basic",
                        AIR2LEAN_CI="1", AIR2LEAN_DIFF="0", AIR2LEAN_ZIG_VERSION="0.16.0",
                        AIR2LEAN_OUT_DIR="", AIR2LEAN_CHECK_REPORT_DIR=".lake/check-reports/0.16.0")
        self.git("init", "-q")
        self.git("add", "Proofs")
        self.git("-c", "user.name=Profile Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "baseline")

    def tearDown(self):
        self.temp.cleanup()

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.repo, check=True, capture_output=True).stdout

    def pipeline(self, **env):
        return subprocess.run(["bash", "scripts/check.sh"], cwd=self.repo, env=dict(self.env, **env),
                              text=True, capture_output=True, check=False)

    def test_new_profile_against_legacy_air_and_head_passes_with_header_retained(self):
        result = self.pipeline()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.proof.read_bytes(), generated(self.fixture))
        report = self.repo / ".lake/check-reports/0.16.0/basic.json"
        self.assertEqual(json.loads(report.read_text())["generated_sha256"], hashlib.sha256(self.proof.read_bytes()).hexdigest())
        self.assertIn("build Proofs.Basic.Gen", (self.repo / "calls.log").read_text())
        self.assertEqual(self.pipeline().returncode, 0, "validated header-only dirty Gen should pass")

    def test_version_and_os_gen_goldens_also_accept_only_header_transition(self):
        os_name = subprocess.run(["uname", "-s"], check=True, capture_output=True, text=True).stdout.strip().lower()
        golden = self.repo / f"tests/golden/0.16.0/basic/Gen-{os_name}.lean"
        golden.parent.mkdir(parents=True)
        golden.write_bytes(BODY)
        result = self.pipeline()
        self.assertEqual(result.returncode, 0, result.stderr)
        golden.write_bytes(BODY.replace(b"42", b"40"))
        result = self.pipeline()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("generated semantics changed", result.stderr)

    def test_real_body_change_and_dirty_index_fail_before_replacement(self):
        (self.repo / "generated.txt").write_bytes(generated(self.fixture, BODY.replace(b"42", b"41")))
        result = self.pipeline()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.proof.read_bytes(), BODY)
        self.assertIn("differs from the translator output", result.stderr)
        (self.repo / "generated.txt").write_bytes(generated(self.fixture))
        self.proof.write_bytes(BODY + b"-- manual body edit\n")
        self.git("add", "Proofs/Basic/Gen.lean")
        self.proof.write_bytes(BODY)
        result = self.pipeline()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("first-line profile record", result.stderr)
        self.assertEqual(self.proof.read_bytes(), BODY)

    def test_untracked_and_unrelated_proof_changes_fail(self):
        other = self.repo / "Proofs/Basic/Proofs.lean"
        other.write_text("theorem extra : True := trivial\n")
        result = self.pipeline()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unrelated or untracked proof change", result.stderr)
        self.git("add", "Proofs/Basic/Proofs.lean")
        self.git("-c", "user.name=Profile Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "proof baseline")
        other.write_text("changed proof\n")
        result = self.pipeline()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unrelated or untracked proof change", result.stderr)

    def test_invalid_actual_profile_precedes_any_golden_comparison(self):
        golden = self.repo / "tests/golden/basic/air/basic.fixture.json"
        golden.write_text("invalid golden JSON")
        result = self.pipeline(FAKE_TRANSLATOR_FAIL="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("invalid actual profile rejected", result.stderr)
        self.assertNotIn("checking against golden", result.stderr)
        self.assertEqual(self.proof.read_bytes(), BODY)

    def test_proof_gate_remains_mandatory_when_diff_is_disabled(self):
        result = self.pipeline(FAKE_PROOF_FAIL="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("proof gate rejected generated source", result.stderr)
        self.assertTrue(self.proof.read_bytes().startswith(HELPER["PREFIX"]))


if __name__ == "__main__":
    unittest.main()
