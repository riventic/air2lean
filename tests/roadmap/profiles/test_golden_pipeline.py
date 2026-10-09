#!/usr/bin/env python3
"""Profile/golden receipt regressions; only fake Zig/Lake tools are invoked."""
import copy
import re
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

    def test_legacy_schema_selects_legacy_profile(self):
        try:
            profile = HELPER["profile_for_air"](LEGACY)
        except ValueError as error:
            self.fail(f"schema-11 AIR was not routed to the legacy profile: {error}")
        self.assertEqual((profile["name"], profile["schema"]), ("legacy-abi64-le", 11))

    def test_unknown_profile_name_is_rejected(self):
        changed = copy.deepcopy(CURRENT)
        changed["profile"]["name"] = "abi64-le-v2"
        with self.assertRaisesRegex(ValueError, "incompatible target profile"):
            HELPER["profile_for_air"](changed)

    def test_pointer_width_follows_the_target(self):
        # T02: wasm32 profiles have 32-bit pointers; every other target stays 64-bit.
        wasm = copy.deepcopy(CURRENT)
        wasm["profile"].update(target_triple="wasm32-wasi.0.1.0...0.1.0-musl", abi="musl", pointer_bits=32)
        self.assertEqual(HELPER["profile_for_air"](wasm)["pointer_bits"], 32)
        for triple, abi, bits in (("wasm32-wasi.0.1.0...0.1.0-musl", "musl", 64),
                                  (CURRENT["profile"]["target_triple"], CURRENT["profile"]["abi"], 32)):
            changed = copy.deepcopy(CURRENT)
            changed["profile"].update(target_triple=triple, abi=abi, pointer_bits=bits)
            with self.assertRaisesRegex(ValueError, "incompatible target profile"):
                HELPER["profile_for_air"](changed)

    def test_future_schema_fails_closed(self):
        changed = copy.deepcopy(CURRENT)
        changed["schema"] = 13
        with self.assertRaisesRegex(ValueError, "unsupported AIR schema"):
            HELPER["profile_for_air"](changed)

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

    def test_null_vector_index_matches_golden_without_field_but_lanes_stay_observable(self):
        pointer = {"k": "ptr", "size": "one", "child": 0, "host_size": 4, "bit_offset": 3}
        golden = copy.deepcopy(CURRENT)
        golden["types"].append(dict(pointer))
        fresh = copy.deepcopy(CURRENT)
        fresh["types"].append(dict(pointer, vector_index=None))
        self.assertEqual(NORMALIZER["normalize"](fresh), NORMALIZER["normalize"](golden))
        for lane in (2, "runtime"):
            lane_ptr = copy.deepcopy(CURRENT)
            lane_ptr["types"].append(dict(pointer, vector_index=lane))
            normalized = NORMALIZER["normalize"](lane_ptr)
            self.assertEqual(normalized["types"][-1]["vector_index"], lane)
            self.assertNotEqual(normalized, NORMALIZER["normalize"](golden))
        # Only a type entry's field is dropped; the same key elsewhere stays observable.
        nested = copy.deepcopy(CURRENT)
        nested["body"].append({"vector_index": None})
        self.assertIn("vector_index", NORMALIZER["normalize"](nested)["body"][-1])

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
        # Copy check.sh plus every script it (transitively) sources or invokes via $repo_root/scripts/.
        pending, copied = ["check.sh", "normalize-air.py", "normalize-generated.py"], set()
        while pending:
            name = pending.pop()
            if name in copied:
                continue
            copied.add(name)
            shutil.copy2(ROOT / "scripts" / name, self.repo / "scripts" / name)
            if name.endswith(".sh"):
                text = (ROOT / "scripts" / name).read_text()
                pending += re.findall(r"repo_root/scripts/([\w.-]+\.(?:sh|py))", text)
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
        (self.repo / ".gitignore").write_text(".lake/\ncalls.log\n")
        self.commit("baseline")

    def commit(self, message):
        self.git("add", "-A")
        self.git("-c", "user.name=Profile Test", "-c", "user.email=test@example.invalid", "-c", "commit.gpgsign=false",
                 "-c", "core.hooksPath=/dev/null", "commit", "-qm", message)

    def assert_checkout_unchanged(self):
        self.assertEqual(self.proof.read_bytes(), BODY)
        self.assertEqual(self.git("status", "--porcelain", "--untracked-files=all"), b"")

    def build_tree(self):
        return Path((self.repo / ".lake/check-reports/0.16.0/build-tree").read_text().strip())

    def tearDown(self):
        self.temp.cleanup()

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.repo, check=True, capture_output=True).stdout

    def pipeline(self, **env):
        return subprocess.run(["bash", "scripts/check.sh"], cwd=self.repo, env=dict(self.env, **env),
                              text=True, capture_output=True, check=False)

    def test_same_body_builds_the_checkout_and_writes_nothing_tracked(self):
        for _ in range(2):
            result = self.pipeline()
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assert_checkout_unchanged()
            self.assertEqual(self.build_tree(), self.repo.resolve())
        # The receipt binds the actual translation, kept beside it; the checkout's file is the body.
        actual = self.repo / ".lake/check-reports/0.16.0/basic.Gen.lean"
        self.assertEqual(actual.read_bytes(), generated(self.fixture))
        report = json.loads((self.repo / ".lake/check-reports/0.16.0/basic.json").read_text())
        self.assertEqual(report["generated_sha256"], hashlib.sha256(actual.read_bytes()).hexdigest())
        self.assertIn("build Proofs.Basic.Gen", (self.repo / "calls.log").read_text())

    def test_version_golden_is_built_in_a_check_tree(self):
        os_name = subprocess.run(["uname", "-s"], check=True, capture_output=True, text=True).stdout.strip().lower()
        golden = self.repo / f"tests/golden/0.16.0/basic/Gen-{os_name}.lean"
        golden.parent.mkdir(parents=True)
        version_body = BODY.replace(b"42", b"40")
        golden.write_bytes(version_body)
        (self.repo / "generated.txt").write_bytes(generated(self.fixture, version_body))
        self.commit("version golden")
        result = self.pipeline()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_checkout_unchanged()
        tree = self.build_tree()
        self.assertEqual(tree, (self.repo / ".lake/check-tree/0.16.0").resolve())
        self.assertEqual((tree / "Proofs/Basic/Gen.lean").read_bytes(), generated(self.fixture, version_body))
        self.assertIn("build Proofs.Basic.Gen", (tree / "calls.log").read_text())
        self.assertNotIn("build", (self.repo / "calls.log").read_text())
        # A golden that is not this translation fails, still without writing.
        golden.write_bytes(BODY.replace(b"42", b"39"))
        self.commit("stale golden")
        result = self.pipeline()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("generated semantics changed", result.stderr)
        self.assert_checkout_unchanged()

    def test_new_translation_outside_ci_is_tested_in_a_check_tree(self):
        changed = BODY.replace(b"42", b"41")
        (self.repo / "generated.txt").write_bytes(generated(self.fixture, changed))
        self.commit("translator change")
        result = self.pipeline(AIR2LEAN_CI="0")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("to commit it: cp .lake/check-reports/0.16.0/basic.Gen.lean Proofs/Basic/Gen.lean", result.stderr)
        self.assert_checkout_unchanged()
        self.assertEqual((self.build_tree() / "Proofs/Basic/Gen.lean").read_bytes(), generated(self.fixture, changed))

    def test_real_body_change_fails_in_ci(self):
        (self.repo / "generated.txt").write_bytes(generated(self.fixture, BODY.replace(b"42", b"41")))
        self.commit("translator change")
        result = self.pipeline()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("differs from the translator output", result.stderr)
        self.assert_checkout_unchanged()
        self.assertFalse((self.repo / ".lake/check-reports/0.16.0/build-tree").exists())

    def test_any_proof_or_golden_change_fails_in_ci(self):
        for path, text in (("Proofs/Basic/Proofs.lean", "theorem extra : True := trivial\n"),
                           ("Proofs/Basic/Gen.lean", "-- a header-only edit is a change too\n" + BODY.decode()),
                           ("tests/golden/basic/air/basic.fixture.json", "{}")):
            with self.subTest(path=path):
                target = self.repo / path
                original = target.read_bytes() if target.exists() else None
                target.write_text(text)
                result = self.pipeline()
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("differ from HEAD in CI", result.stderr)
                self.assertNotIn("dumping AIR", result.stderr)
                if original is None:
                    target.unlink()
                else:
                    target.write_bytes(original)
        self.proof.write_bytes(BODY + b"-- staged\n")
        self.git("add", "Proofs/Basic/Gen.lean")  # A staged change is a change.
        self.proof.write_bytes(BODY)
        self.assertIn("differ from HEAD in CI", self.pipeline().stderr)

    def test_invalid_actual_profile_precedes_any_golden_comparison(self):
        golden = self.repo / "tests/golden/basic/air/basic.fixture.json"
        golden.write_text("invalid golden JSON")
        self.commit("invalid golden")
        result = self.pipeline(FAKE_TRANSLATOR_FAIL="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("invalid actual profile rejected", result.stderr)
        self.assertNotIn("checking against golden", result.stderr)
        self.assert_checkout_unchanged()

    def test_proof_gate_remains_mandatory_when_diff_is_disabled(self):
        result = self.pipeline(FAKE_PROOF_FAIL="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("proof gate rejected generated source", result.stderr)
        self.assert_checkout_unchanged()


if __name__ == "__main__":
    unittest.main()
