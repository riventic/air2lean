#!/usr/bin/env python3
"""Offline perf-budget gate tests: synthetic measurements and fake tools only.

No Lean, Lake or Zig process starts; the record test uses a Python stand-in for
`air2lean --timing-json` and skips elaboration/proof builds.
"""

import contextlib
import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("perf_budgets", ROOT / "scripts/perf-budgets.py")
perf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(perf)

TOLERANCE = {
    "translator": {"time_ratio": 2.0, "time_slack_seconds": 0.25, "rss_ratio": 1.5, "rss_slack_kib": 65536},
    "lean": {"time_ratio": 1.5, "time_slack_seconds": 10.0, "rss_ratio": 1.3, "rss_slack_kib": 262144},
}
PLATFORM = {"system": "Linux", "machine": "x86_64"}


def measured_workload(scale=1.0, rss=100_000, sha="a" * 64):
    phases = {phase: {"seconds": 0.01 * scale} for phase in perf.INTERNAL_PHASES}
    phases["translate.cold"] = {"seconds": 0.08 * scale, "peak_rss_kib": rss}
    phases["translate.warm"] = {"seconds": 0.05 * scale, "peak_rss_kib": rss}
    phases["elaborate"] = {"seconds": 20.0 * scale, "peak_rss_kib": rss * 10}
    phases["proof.cold"] = {"seconds": 60.0 * scale, "peak_rss_kib": rss * 20}
    phases["proof.warm"] = {"seconds": 1.0 * scale, "peak_rss_kib": rss * 2}
    return {"status": "ok", "phases": phases,
            "output": {"bytes": 1234, "sha256": sha, "matches_reference": True}}


def measurement(**workloads):
    return {"schema": perf.MEASUREMENT_SCHEMA, "platform": dict(PLATFORM),
            "lean_num_threads": "1", "recorded_at": "2026-10-07T00:00:00+00:00",
            "revision": {"head": "0" * 40, "tracked_dirty": False},
            "translator": {"sha256": "f" * 64},
            "workloads": workloads or {"basic": measured_workload(), "layout": measured_workload()}}


AIR_VERSIONS = {"basic": "0.15.2", "layout": "0.16.0"}


def pending_budgets(ids=("basic", "layout")):
    return {"schema": perf.BUDGETS_SCHEMA, "status": "pending", "reference_platform": None,
            "tolerance": copy.deepcopy(TOLERANCE),
            "workloads": [{"id": ident, "air": [f"tests/golden/{ident}/air"],
                           "air_zig_version": AIR_VERSIONS[ident],
                           "namespace": ident.capitalize(), "prefix": ident + ".",
                           "translate_args": [], "reference_gen": f"Proofs/{ident.capitalize()}/Gen.lean",
                           "proof_modules": [], "budget": None} for ident in ids]}


def recorded_budgets():
    return perf.derive(pending_budgets(), measurement())


def kinds(findings):
    return sorted({item["kind"] for item in findings})


class CommittedBudgets(unittest.TestCase):
    def test_committed_file_is_valid(self):
        data = perf.load_json(perf.BUDGETS)
        self.assertEqual(perf.validate_budgets(data), [])
        ids = [workload["id"] for workload in data["workloads"]]
        self.assertGreaterEqual(len(ids), 5)
        for workload in data["workloads"]:
            self.assertTrue((ROOT / workload["reference_gen"]).is_file(), workload["id"])
            self.assertTrue(workload["proof_modules"], workload["id"])
        if data["status"] == "pending":
            self.assertTrue(any(workload["budget"] is None for workload in data["workloads"]))
        for workload in data["workloads"]:
            if workload["budget"] is not None:
                self.assertIs(workload["budget"]["output"]["matches_reference"], True, workload["id"])

    def test_validation_rejects_bad_documents(self):
        data = pending_budgets()
        data["workloads"].append(copy.deepcopy(data["workloads"][0]))
        self.assertTrue(any("duplicated" in error for error in perf.validate_budgets(data)))
        data = pending_budgets()
        data["workloads"][0]["air"] = ["tests/golden/no-such-example/air"]
        self.assertTrue(any("missing AIR" in error for error in perf.validate_budgets(data)))
        # A shared golden folder plus a version overlay can mix Zig versions.
        data = pending_budgets()
        data["workloads"][0]["air"].append("tests/golden/0.16.0/basic/air")
        self.assertTrue(any("mixed AIR" in error for error in perf.validate_budgets(data)))
        data = pending_budgets()
        data["workloads"][0]["air_zig_version"] = "0.16.0"
        self.assertTrue(any("expected 0.16.0" in error for error in perf.validate_budgets(data)))
        data = pending_budgets()
        data["status"] = "recorded"
        self.assertTrue(any("pending" in error for error in perf.validate_budgets(data)))
        data = pending_budgets()
        data["tolerance"]["lean"]["time_ratio"] = 0.5
        self.assertTrue(any("at least 1" in error for error in perf.validate_budgets(data)))
        self.assertEqual(perf.validate_budgets(recorded_budgets()), [])


class Gate(unittest.TestCase):
    def test_pass_within_tolerance(self):
        code, findings = perf.gate(recorded_budgets(), measurement(
            basic=measured_workload(scale=1.4, rss=125_000), layout=measured_workload()))
        self.assertEqual((code, findings), (0, []))

    def test_time_regression(self):
        code, findings = perf.gate(recorded_budgets(), measurement(
            basic=measured_workload(scale=3.0), layout=measured_workload()))
        self.assertEqual(code, 1)
        self.assertEqual(kinds(findings), ["time-regression"])
        self.assertIn("proof.cold", {item["phase"] for item in findings})
        self.assertEqual({item["workload"] for item in findings}, {"basic"})

    def test_small_translator_noise_is_absorbed_by_slack(self):
        # 0.05s -> 0.25s is 5x but within the 0.25s absolute slack (limit 0.30s).
        budgets = recorded_budgets()
        self.assertEqual(budgets["workloads"][0]["budget"]["phases"]["translate.warm"]["max_seconds"], 0.3)
        noisy = measured_workload()
        noisy["phases"]["translate.warm"]["seconds"] = 0.25
        self.assertEqual(perf.gate(budgets, measurement(basic=noisy, layout=measured_workload()))[0], 0)

    def test_memory_regression(self):
        code, findings = perf.gate(recorded_budgets(), measurement(
            basic=measured_workload(rss=1_000_000), layout=measured_workload()))
        self.assertEqual(code, 1)
        self.assertEqual(kinds(findings), ["memory-regression"])

    def test_missing_workload(self):
        code, findings = perf.gate(recorded_budgets(), measurement(basic=measured_workload()))
        self.assertEqual(code, 1)
        self.assertEqual(findings[0]["kind"], "missing-workload")
        self.assertEqual(findings[0]["workload"], "layout")

    def test_missing_phase(self):
        partial = measured_workload()
        del partial["phases"]["proof.cold"]
        code, findings = perf.gate(recorded_budgets(), measurement(basic=partial, layout=measured_workload()))
        self.assertEqual(code, 1)
        self.assertEqual([(item["kind"], item.get("phase")) for item in findings],
                         [("missing-phase", "proof.cold")])

    def test_failed_and_unbudgeted_workloads(self):
        code, findings = perf.gate(recorded_budgets(), measurement(
            basic={"status": "failed", "error": "translator exited 1"},
            layout=measured_workload(), vectors=measured_workload()))
        self.assertEqual(code, 1)
        self.assertEqual(kinds(findings), ["failed-workload", "unbudgeted-workload"])

    def test_output_change_is_a_preservation_failure(self):
        code, findings = perf.gate(recorded_budgets(), measurement(
            basic=measured_workload(sha="b" * 64), layout=measured_workload()))
        self.assertEqual(code, 1)
        self.assertEqual(kinds(findings), ["output-changed"])

    def test_pending_budgets(self):
        code, findings = perf.gate(pending_budgets(), measurement())
        self.assertEqual(code, perf.EXIT_PENDING)
        self.assertEqual(kinds(findings), ["pending"])
        code, _ = perf.gate(pending_budgets(), measurement(), allow_pending=True)
        self.assertEqual(code, 0)
        # Pending never hides a real failure.
        code, findings = perf.gate(pending_budgets(), measurement(basic=measured_workload()),
                                   allow_pending=True)
        self.assertEqual((code, kinds(findings)), (1, ["missing-workload", "pending"]))

    def test_platform_and_serialization(self):
        other = measurement()
        other["platform"] = {"system": "Darwin", "machine": "arm64"}
        code, findings = perf.gate(recorded_budgets(), other)
        self.assertEqual((code, kinds(findings)), (1, ["platform-mismatch"]))
        self.assertEqual(perf.gate(recorded_budgets(), other, allow_platform_mismatch=True)[0], 0)
        parallel = measurement()
        parallel["lean_num_threads"] = None
        self.assertEqual(kinds(perf.gate(recorded_budgets(), parallel)[1]), ["unserialized-measurement"])
        self.assertEqual(perf.gate(recorded_budgets(), {"schema": "other"})[0], 1)


class Baseline(unittest.TestCase):
    def test_limits_use_larger_of_ratio_and_slack(self):
        budgets = recorded_budgets()
        self.assertEqual(budgets["status"], "recorded")
        self.assertEqual(budgets["reference_platform"], PLATFORM)
        phases = budgets["workloads"][0]["budget"]["phases"]
        self.assertEqual(phases["proof.cold"]["max_seconds"], 90.0)  # 60 * 1.5
        self.assertEqual(phases["proof.warm"]["max_seconds"], 11.0)  # 1 + 10
        self.assertEqual(phases["proof.cold"]["max_peak_rss_kib"], 2_600_000)
        self.assertEqual(phases["translate.warm"]["max_peak_rss_kib"], 165_536)
        self.assertNotIn("max_peak_rss_kib", phases["parse"])
        self.assertEqual(budgets["workloads"][0]["budget"]["output"]["sha256"], "a" * 64)

    def test_refuses_unusable_measurements(self):
        dirty = measurement()
        dirty["revision"]["tracked_dirty"] = True
        with self.assertRaisesRegex(ValueError, "clean"):
            perf.derive(pending_budgets(), dirty)
        self.assertEqual(perf.derive(pending_budgets(), dirty, allow_dirty=True)["status"], "recorded")
        failed = measurement(basic={"status": "failed", "error": "x"}, layout=measured_workload())
        with self.assertRaisesRegex(ValueError, "basic"):
            perf.derive(pending_budgets(), failed)
        with self.assertRaisesRegex(ValueError, "unknown"):
            perf.derive(pending_budgets(), measurement(), only=["nope"])
        skipped = measured_workload()
        del skipped["phases"]["elaborate"]
        with self.assertRaisesRegex(ValueError, "elaborate"):
            perf.derive(pending_budgets(), measurement(basic=skipped, layout=measured_workload()))
        partial = perf.derive(pending_budgets(), measurement(), only=["basic"])
        self.assertEqual(partial["status"], "pending")
        self.assertIsNone(partial["workloads"][1]["budget"])

    def test_cli_baseline_then_gate(self):
        with tempfile.TemporaryDirectory() as temporary:
            budgets = Path(temporary) / "budgets.json"
            measured = Path(temporary) / "measurement.json"
            report = Path(temporary) / "findings.json"
            budgets.write_text(json.dumps(pending_budgets()))
            measured.write_text(json.dumps(measurement()))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(perf.main(["gate", "--measurement", str(measured),
                                            "--budgets", str(budgets)]), perf.EXIT_PENDING)
                self.assertEqual(perf.main(["baseline", "--measurement", str(measured),
                                            "--budgets", str(budgets)]), 0)
                self.assertEqual(perf.main(["gate", "--measurement", str(measured),
                                            "--budgets", str(budgets), "--json", str(report)]), 0)
                measured.write_text(json.dumps(measurement(basic=measured_workload(scale=4),
                                                           layout=measured_workload())))
                self.assertEqual(perf.main(["gate", "--measurement", str(measured),
                                            "--budgets", str(budgets), "--json", str(report)]), 1)
            self.assertEqual(json.loads(report.read_text())["exit_code"], 1)


class RecordHelpers(unittest.TestCase):
    def test_stage_air_overlays_later_directories(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "shared").mkdir()
            (root / "version").mkdir()
            def air(path, version, tag):
                (root / path).write_text(json.dumps({"schema": 11, "zig_version": version, "tag": tag}))
            air("shared/a.json", "0.15.2", "shared-a")
            air("shared/b.json", "0.16.0", "shared-b")
            air("version/b.json", "0.15.2", "version-b")
            (root / "shared/notes.txt").write_text("ignored")
            out = perf.stage_air(root, ["shared", "version"], root / "out", "0.15.2")
            self.assertEqual(sorted(path.name for path in out.iterdir()), ["a.json", "b.json"])
            self.assertEqual(json.loads((out / "b.json").read_text())["tag"], "version-b")
            with self.assertRaisesRegex(RuntimeError, "mixed AIR"):
                perf.stage_air(root, ["shared"], root / "mixed")
            self.assertFalse((root / "mixed").exists())
            with self.assertRaisesRegex(RuntimeError, "expected 0.16.0"):
                perf.stage_air(root, ["shared", "version"], root / "other", "0.16.0")
            (root / "empty").mkdir()
            with self.assertRaises(RuntimeError):
                perf.stage_air(root, ["empty"], root / "x")

    def test_reference_comparison_ignores_only_the_profile_record(self):
        body = b"import ZigLean\n\ndef f := 1\n"
        header = b'-- air2lean-profile: {"profile":{}}\n'
        self.assertEqual(perf.lean_body(header + body), body)
        self.assertEqual(perf.lean_body(body), body)
        self.assertEqual(perf.lean_body(b"-- other\n" + body), b"-- other\n" + body)

    def test_cold_removal_is_module_local(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            lib = root / ".lake/build/lib/lean/Proofs/Basic"
            ir = root / ".lake/build/ir/Proofs/Basic"
            lib.mkdir(parents=True)
            ir.mkdir(parents=True)
            for name in ("Gen.olean", "Gen.ilean", "Gen.trace", "Gen.olean.hash",
                         "GenExtra.olean", "Proofs.olean"):
                (lib / name).write_text("x")
            (ir / "Gen.c").write_text("x")
            removed = perf.remove_module_artifacts(root, ["Proofs.Basic.Gen", "Proofs.Missing.X"])
            self.assertEqual(removed, 5)
            self.assertEqual(sorted(path.name for path in lib.iterdir()), ["GenExtra.olean", "Proofs.olean"])

    def test_measure_reports_time_rss_and_exit(self):
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / "log"
            step = perf.measure([sys.executable, "-c", "x = bytearray(48 << 20); raise SystemExit(3)"],
                                temporary, log, timeout=30)
            self.assertEqual(step["exit_code"], 3)
            self.assertFalse(step["timed_out"])
            self.assertGreaterEqual(step["peak_rss_kib"], 48 * 1024)
            step = perf.measure([sys.executable, "-c", "import time; time.sleep(30)"],
                                temporary, log, timeout=0.5)
            self.assertTrue(step["timed_out"])
            self.assertLess(step["seconds"], 10)


FAKE_AIR2LEAN = r'''#!/usr/bin/env python3
import json, sys
from pathlib import Path
args = sys.argv[1:]
air, out, timing = Path(args[0]), Path(args[args.index("-o") + 1]), args[args.index("--timing-json") + 1]
names = sorted(path.name for path in air.glob("*.json"))
out.write_text("-- fake\n" + "\n".join(names) + "\n")
phases = {"read": 1, "renumber": 1, "parse": 2000, "normalize": 3000, "check": 4000, "emit": 5000, "write": 1}
Path(timing).write_text(json.dumps({"schema": "air2lean-timing/1", "files": len(names),
    "functions": len(names), "input_bytes": 1, "output_bytes": out.stat().st_size, "phases_ns": phases}))
'''


class Record(unittest.TestCase):
    def test_record_with_fake_translator(self):
        with tempfile.TemporaryDirectory() as temporary:
            temporary = Path(temporary)
            fake = temporary / "air2lean"
            fake.write_text(FAKE_AIR2LEAN)
            fake.chmod(0o755)
            out = temporary / "measurement.json"
            with mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "1"}), \
                    contextlib.redirect_stderr(io.StringIO()):
                code = perf.main(["record", "--out", str(out), "--air2lean", str(fake),
                                  "--lake", "/nonexistent/lake", "--no-build", "--skip-elaborate",
                                  "--skip-proof", "--workload", "basic", "--repeat", "2"])
            self.assertEqual(code, 0)
            data = json.loads(out.read_text())
            result = data["workloads"]["basic"]
            self.assertEqual(result["status"], "ok", result)
            self.assertEqual(set(result["phases"]),
                             {"translate.cold", "translate.warm", *perf.INTERNAL_PHASES})
            self.assertEqual(result["phases"]["emit"]["seconds"], 5e-06)
            self.assertIs(result["output"]["matches_reference"], False)
            # Same platform as the committed baseline, so only the reference check can refuse.
            committed = perf.load_json(perf.BUDGETS)
            committed["reference_platform"] = data["platform"]
            with self.assertRaisesRegex(ValueError, "differ from"):
                perf.derive(committed, data, only=["basic"], allow_dirty=True)
            self.assertEqual(data["lean_num_threads"], "1")
            self.assertTrue(out.with_suffix(".log").is_file())
            # One measured workload: the gate reports the missing ones.
            code, findings = perf.gate(perf.load_json(perf.BUDGETS), data, allow_pending=True)
            self.assertEqual(code, 1)
            self.assertIn("missing-workload", kinds(findings))

    def test_record_refuses_unserialized_runs(self):
        with tempfile.TemporaryDirectory() as temporary, \
                mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "4"}):
            with self.assertRaisesRegex(SystemExit, "build-guard"):
                perf.main(["record", "--out", str(Path(temporary) / "m.json"), "--no-build"])


if __name__ == "__main__":
    unittest.main()
