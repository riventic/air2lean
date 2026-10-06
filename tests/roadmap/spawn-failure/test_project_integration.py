"""Portable, process-blocked tests of the real-project fixture wiring.
These do not execute a compiler, translator, project CLI or qualification gate.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

qualify = load("spawn_project_fixture", Path(__file__).with_name("qualify.py"))
project = load("project_fixture_adapter", ROOT / "scripts/project.py")


class ProjectIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.destination = Path(self.temp.name)
        self.air = self.destination / "air"
        self.air.mkdir()
        self.profile = dict(name="abi64-le-v1", target_triple="x86_64-linux.5.10-gnu",
            pointer_bits=64, endian="little", abi="gnu", zig_version="0.15.2",
            backend="stage2_llvm", cpu="baseline", features=[], build_mode="ReleaseSafe",
            float_mode="per-instruction", error_set_bits=16, error_layout="type-table",
            export_stage="analyzed-air", error_tracing=False)
        self.direct = {}
        for policy in ("available", "fallible"):
            path = self.destination / (policy + ".lean")
            path.write_text("-- mocked emission " + policy + "\n")
            self.direct[policy] = path
        self.translator = self.destination / "mock-translator"
        self.translator.write_text("offline executable identity only\n")
        self.calls = []

    def record(self, version):
        self.profile["zig_version"] = version
        (self.air / "spawn_failure.threadPair.json").write_text(json.dumps(dict(
            schema=12, zig_version=version, profile=self.profile,
            name="spawn_failure.threadPair", body=[])))

    def fake_run(self, label, argv, **options):
        self.calls.append(label)
        if "project-diagnostics.py" in argv[1]:
            manifest, _, _, evidence = project.collect(Path(argv[3]))
            policy = project.spawn_policy(manifest)
            checks = dict(status="checked", evidence=evidence, proof_status="not_run",
                runtime_outcomes="not_observed", source_correspondence="not_attested",
                root_checks=[dict(status="checked", execution=dict(argv=["--spawn-policy", policy]))])
            Path(argv[argv.index("--out") + 1]).write_text(json.dumps(checks))
            return json.dumps(checks)
        command, manifest_path = argv[2], Path(argv[3])
        if command == "verify":
            artifact = Path(argv[argv.index("--artifact") + 1])
            if options.get("expected") == 2:
                with self.assertRaisesRegex(project.Invalid, options["marker"]):
                    project.verify(manifest_path, artifact)
                return "expected rejection"
            return json.dumps(project.verify(manifest_path, artifact))
        manifest, limits, data, report = project.collect(manifest_path)
        if command == "translate":
            artifact = Path(argv[argv.index("--out") + 1])
            artifact.mkdir()
            def translate(argv, cwd, limits):
                output = Path(argv[argv.index("-o") + 1])
                output.write_bytes(self.direct[project.spawn_policy(manifest)].read_bytes())
                return dict(status="passed", code="TRANSLATION_OK", returncode=0,
                            message="", argv=argv)
            with mock.patch.object(project, "run_translation", side_effect=translate):
                project.translate(manifest, limits, data, report, self.translator, artifact)
            (artifact / "report.json").write_text(json.dumps(report))
        return json.dumps(report)

    def test_both_version_fixtures_policy_receipts_and_restoration(self):
        for version in ("0.15.2", "0.16.0"):
            with self.subTest(version=version):
                self.record(version)
                destination = self.destination / version
                destination.mkdir()
                gate = mock.Mock(run=self.fake_run)
                with mock.patch.object(project, "git_state", return_value={}), \
                     mock.patch.object(subprocess, "Popen", side_effect=AssertionError("process forbidden")):
                    generated = qualify.project_integration(gate, destination, self.air,
                        dict(self.profile, schema=12), self.translator, self.direct)
                    self.assertEqual(generated.read_bytes(), self.direct["fallible"].read_bytes())
                    manifest = destination / "project-inputs/fallible.json"
                    self.assertEqual(project.verify(manifest, generated.parents[1])["status"], "hashes_match")
                self.assertEqual(self.calls[-1], "project-fallible-reject-legacy")
                self.assertEqual(len(self.calls), 13)
                self.calls.clear()
                inventory = qualify.artifacts(destination)
                self.assertIn("project-fallible-artifact/report.json", inventory)
                self.assertEqual(json.loads((destination / "project-inputs/profile.json").read_text()), self.profile)
                self.assertNotIn("spawn_policy", json.loads((destination / "project-inputs/omitted.json").read_text()))

    def test_diagnostic_argv_cannot_contradict_policy(self):
        self.record("0.16.0")
        def wrong_diagnostic(label, argv, **options):
            result = self.fake_run(label, argv, **options)
            if "project-diagnostics.py" in argv[1]:
                checks = json.loads(result)
                checks["root_checks"][0]["execution"]["argv"][-1] = "contradictory"
                Path(argv[argv.index("--out") + 1]).write_text(json.dumps(checks))
                return json.dumps(checks)
            return result
        with mock.patch.object(project, "git_state", return_value={}), \
             mock.patch.object(subprocess, "Popen", side_effect=AssertionError("process forbidden")):
            with self.assertRaisesRegex(RuntimeError, "diagnostic policy"):
                qualify.project_integration(mock.Mock(run=wrong_diagnostic), self.destination,
                    self.air, dict(self.profile, schema=12), self.translator, self.direct)


if __name__ == "__main__":
    unittest.main()
