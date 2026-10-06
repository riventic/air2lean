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
from unittest import mock

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

    def test_duplicate_receipt_filenames_fail_for_actual_and_golden_batches(self):
        report = json.loads(self.report.read_text())
        report["air"].append(dict(report["air"][0]))
        self.report.write_text(json.dumps(report))
        for actual in (False, True):
            with self.assertRaisesRegex(ValueError, "duplicate AIR receipt filename"):
                NORMALIZER["ValidationContext"](self.report, actual)

    def test_directory_bad_hash_leaves_existing_overlay_untouched(self):
        second = self.air / "two.json"
        second.write_text(json.dumps(dict(CURRENT, name="profile.second")))
        HELPER["write_report"](self.output, self.air, self.report)
        second.write_text(json.dumps(dict(CURRENT, name="changedAfterReceipt")))
        destination = self.directory / "normalized"
        destination.mkdir()
        previous = destination / "one.json"
        previous.write_bytes(b"previous overlay\n")
        context = NORMALIZER["ValidationContext"](self.report, True)
        with self.assertRaisesRegex(ValueError, "AIR artifact does not match"):
            NORMALIZER["add_directory"](self.air, destination, context)
        self.assertEqual(previous.read_bytes(), b"previous overlay\n")
        self.assertEqual(sorted(p.name for p in destination.iterdir()), ["one.json"])

    def test_directory_checks_profiles_even_when_raw_hash_matches(self):
        changed = copy.deepcopy(CURRENT)
        changed["profile"]["cpu"] = "haswell"
        self.input.write_text(json.dumps(changed))
        report = json.loads(self.report.read_text())
        report["air"][0]["sha256"] = hashlib.sha256(self.input.read_bytes()).hexdigest()
        self.report.write_text(json.dumps(report))
        context = NORMALIZER["ValidationContext"](self.report, True)
        with self.assertRaisesRegex(ValueError, "AIR profile differs"):
            NORMALIZER["add_directory"](self.air, self.directory / "normalized", context)

    def test_golden_batch_checks_profile_without_matching_actual_receipt_entry(self):
        source = self.directory / "golden"
        source.mkdir()
        path = source / "notInActualReceipt.json"
        path.write_text(json.dumps(LEGACY))
        context = NORMALIZER["ValidationContext"](self.report)
        destination = self.directory / "normalized"
        NORMALIZER["add_directory"](source, destination, context)
        self.assertEqual(json.loads((destination / NORMALIZER["canonical_filename"](LEGACY["name"])).read_text())["schema"], 11)
        malformed = copy.deepcopy(LEGACY)
        malformed["target_endian"] = "big"
        path.write_text(json.dumps(malformed))
        with self.assertRaisesRegex(ValueError, "little-endian"):
            NORMALIZER["add_directory"](source, destination, context)

    def test_directory_helpers_and_receipt_load_once_each_file_normalizes_once(self):
        second = self.air / "two.json"
        second.write_text(json.dumps(dict(CURRENT, name="profile.second")))
        HELPER["write_report"](self.output, self.air, self.report)
        NORMALIZER["load_helpers"].cache_clear()
        with mock.patch.object(runpy, "run_path", wraps=runpy.run_path) as load:
            helpers = NORMALIZER["load_helpers"]()
            report_loader = mock.Mock(wraps=helpers["load_report"])
            profile_checker = mock.Mock(wraps=helpers["profile_for_air"])
            with mock.patch.dict(helpers, {"load_report": report_loader, "profile_for_air": profile_checker}):
                context = NORMALIZER["ValidationContext"](self.report, True)
                NORMALIZER["add_directory"](self.air, self.directory / "normalized", context)
            self.assertEqual(load.call_count, 1)
            self.assertEqual(report_loader.call_count, 1)
            self.assertEqual(profile_checker.call_count, 2)

    def test_collision_hashes_match_single_file_cli_and_overlays_remove_all_variants(self):
        source = self.directory / "golden"
        source.mkdir()
        destination = self.directory / "normalized"
        expected = {}
        for i in (1, 23):
            doc = copy.deepcopy(LEGACY)
            doc["name"] = f"math.sub__anon_{i}"
            doc["body"][0]["args"][0]["val"] = str(i)
            doc["body"][0]["observable"] = "naïve__anon_9"
            path = source / f"math.sub__anon_{i}.json"
            path.write_text(json.dumps(doc))
            result = subprocess.run(["python3", str(ROOT / "scripts/normalize-air.py"), str(path),
                                     "--check-report", str(self.report)], check=True, capture_output=True)
            self.assertTrue(result.stdout.endswith(b"\n"))
            canonical = (json.dumps(json.loads(result.stdout), ensure_ascii=False,
                                    sort_keys=True, indent=2) + "\n").encode()
            self.assertEqual(result.stdout, canonical)
            name = "math.sub__anon_N." + hashlib.sha1(canonical).hexdigest()[:12] + ".json"
            expected[name] = canonical
        context = NORMALIZER["ValidationContext"](self.report)
        NORMALIZER["add_directory"](source, destination, context)
        self.assertEqual({p.name: p.read_bytes() for p in destination.iterdir()}, expected)
        (destination / "unrelated.json").write_bytes(b"retain\n")
        (destination / "math.sub__anon_N.arbitrary.extra.json").write_bytes(b"stale\n")
        overlay = self.directory / "overlay"
        overlay.mkdir()
        (overlay / "math.sub__anon_99.json").write_text(json.dumps(dict(LEGACY, name="math.sub__anon_99")))
        NORMALIZER["add_directory"](overlay, destination, context)
        self.assertEqual(sorted(p.name for p in destination.iterdir()),
                         ["math.sub__anon_N.json", "unrelated.json"])
        NORMALIZER["add_directory"](source, destination, context)
        self.assertEqual(set(p.name for p in destination.iterdir()), set(expected) | {"unrelated.json"})
        self.assertEqual((destination / "unrelated.json").read_bytes(), b"retain\n")



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
