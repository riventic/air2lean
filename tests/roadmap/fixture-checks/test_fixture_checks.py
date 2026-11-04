#!/usr/bin/env python3
"""scripts/fixture-checks.py: every unit runs on every invocation, no result is reused.

The regression for the false green of a reused pass (docs/ci.md#full-build): a unit whose input
is reached by a path built in code (tests/roadmap/callbacks/mutants.py reaches
`ROADMAP / "asm-effects"`) kept the key of its last pass after that input changed, and the stale
pass was reused while the check failed. Here a synthetic unit reads a file whose path no text of
the unit names; after an edit of that file the second run must run the unit again and fail.
Offline: no toolchain, no Lean.
"""
import contextlib
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
spec = importlib.util.spec_from_file_location("air2lean_fixture_checks", ROOT / "scripts/fixture-checks.py")
fc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fc)


def no_toolchain(kind, version):
    raise fc.Unavailable("no %s Zig %s in this test" % (kind, version))


@contextlib.contextmanager
def offline_runtime_run(fails=None):
    """assumptions.runtime_run without Lake or a Lean toolchain: publishes a record, or fails."""
    os.environ[fc.assumptions.RUNTIME_RUN] = "offline-record"
    try:
        yield
    finally:
        del os.environ[fc.assumptions.RUNTIME_RUN]
    if fails:
        raise fails


@contextlib.contextmanager
def offline_prepared_tool(prepare=lambda: None):
    """assumptions.prepared_tool without Lake: `prepare` stands for the extractor's preparation."""
    prepare()
    yield {}


class NoReuse(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="air2lean fixture-checks ")
        self.addCleanup(temp.cleanup)
        self.temp = Path(temp.name)
        self.cas = self.temp / "cas"
        self.cas.mkdir()
        self.hidden = self.temp / "hidden"
        self.hidden.mkdir()
        # The path is assembled at run time: no text of the unit spells out "hidden/input".
        self.unit = {"name": "synthetic: hidden input", "job": "synthetic", "rows": ["synthetic"],
                     "zig": "0.0.0", "checks": ["tests/roadmap/synthetic/check.sh"],
                     "run": 'f="$HIDDEN_DIR"/in""put\necho "read $f"\n[ "$(cat "$f")" = ok ]\n',
                     "env": {"HIDDEN_DIR": str(self.hidden)}, "runner": fc.HOST, "skipped": [],
                     "error": None, "toolchains": {"patched": [], "stock": []}}
        for patch in (mock.patch.object(fc, "discover", lambda tree: [dict(self.unit)]),
                      mock.patch.object(fc, "resolve", no_toolchain),
                      mock.patch.object(fc.assumptions, "runtime_run", offline_runtime_run),
                      mock.patch.object(fc.assumptions, "prepared_tool", offline_prepared_tool),
                      mock.patch.object(fc, "FIXTURE_BUILD", ["true"]),
                      mock.patch.dict(os.environ, {"AIR2LEAN_CAS_DIR": str(self.cas),
                                                   "AIR2LEAN_FIXTURE_SCHEDULE": str(self.temp / "schedule.json")})):
            patch.start()
            self.addCleanup(patch.stop)

    def run_checks(self, *argv):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = fc.main(["--jobs", "1", "--logs", str(self.temp / "logs"), *argv])
        return status, out.getvalue(), err.getvalue()

    def test_an_edit_outside_the_named_paths_reruns_the_unit(self):
        (self.hidden / "input").write_text("ok\n")
        status, out, err = self.run_checks()
        self.assertEqual(status, 0, out + err)
        (self.hidden / "input").write_text("broken\n")
        status, out, err = self.run_checks()
        self.assertEqual(status, 1, out + err)  # rerun, not the first run's pass
        self.assertIn("1 failed", out)
        self.assertIn("FAILED synthetic: hidden input", err)
        (self.hidden / "input").write_text("ok\n")
        self.assertEqual(self.run_checks()[0], 0)  # and a fixed input passes again
        self.assertEqual(list(self.cas.iterdir()), [])  # no pass is published to the shared store

    def test_the_schedule_orders_and_sizes_but_never_decides(self):
        (self.hidden / "input").write_text("ok\n")
        self.assertEqual(self.run_checks()[0], 0)
        hint = json.loads((self.temp / "schedule.json").read_text())[self.unit["name"]]
        self.assertEqual(sorted(hint), ["elapsed_s", "lean_threads", "peak_rss_kib"])  # no status
        (self.hidden / "input").write_text("broken\n")
        self.assertEqual(self.run_checks()[0], 1)  # a measured unit still runs and fails
        units = [{"name": n} for n in ("short", "long", "new", "bad", "wide")]
        (self.temp / "schedule.json").write_text(json.dumps({
            "short": {"elapsed_s": 1, "lean_threads": 2, "peak_rss_kib": [100 << 10]},
            "long": {"elapsed_s": 9, "lean_threads": 2, "peak_rss_kib": [4000 << 10, 6000 << 10]},
            "bad": {"elapsed_s": 5},  # malformed: unmeasured, not a crash
            "wide": {"elapsed_s": 3, "lean_threads": 1, "peak_rss_kib": [1000 << 10]}}))
        with mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "2"}):
            order, requests = fc.schedule(units, 5000)
        self.assertEqual([units[i]["name"] for i in order], ["new", "bad", "long", "wide", "short"])
        # A peak measured with fewer Lean threads is scaled up to this run's count.
        self.assertEqual(requests, [fc.MEM_FLOOR_MIB, int(6000 * fc.MEM_MARGIN), 5000, 5000,
                                    int(1000 * fc.MEM_MARGIN * 2)])
        with mock.patch.dict(os.environ, {"AIR2LEAN_FIXTURE_SCHEDULE": str(self.temp)}), \
             contextlib.redirect_stderr(io.StringIO()) as err:
            fc.write_hints(units[:1], [{"elapsed_s": 1, "peak_rss_kib": 1}])  # a directory: not written
        self.assertIn("not recorded", err.getvalue())

    def test_the_default_guard_stays_within_the_budget_and_an_enclosing_admission(self):
        # A nested guard above its enclosing admission is refused (build-guard.py `inherited`);
        # one above the machine's budget would take every slot and still exceed it.
        for budget, grant, expected in (
                ("64000", None, fc.GUARD_RSS_MIB), ("64000", {"rss_mib": 22000}, 22000),
                ("64000", {"rss_mib": 11000.0}, 11000), ("64000", {"rss_mib": 64000}, fc.GUARD_RSS_MIB),
                ("64000", {"rss_mib": True}, fc.GUARD_RSS_MIB), ("64000", "not json", fc.GUARD_RSS_MIB),
                ("16000", None, 16000), ("16000", {"rss_mib": 11000}, 11000)):
            value = grant if isinstance(grant, str) else json.dumps(grant)
            with self.subTest(budget=budget, grant=grant), \
                 mock.patch.dict(os.environ, {fc.GUARD.INHERIT: value, "AIR2LEAN_BUILD_MEM_MIB": budget}):
                self.assertEqual(fc.guard_rss_mib(), expected)

    def test_there_is_no_selection_by_key(self):
        # `--base REF` chose the units by the key's files; it is rejected, not ignored.
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as exit_:
            fc.main(["--base", "HEAD"])
        self.assertEqual(exit_.exception.code, 2)

    def test_prepare_resolves_every_units_toolchains_each_time(self):
        self.unit["toolchains"] = {"patched": [], "stock": ["0.16.0"]}
        resolved = []
        with mock.patch.object(fc, "resolve", lambda kind, version: resolved.append((kind, version)) or "zig"):
            for _ in range(2):
                self.assertEqual(self.run_checks("--prepare")[0], 0)
        self.assertEqual(resolved, [("stock", "0.16.0")] * 2)

    def test_a_missing_native_runner_fails_the_unit_naming_it(self):
        # Unit 12 of 2026-11-04: big-endian/check.sh sent the runner's stderr to a file, so a
        # missing qemu-s390x-static failed with exit 127 and no message.
        (self.hidden / "input").write_text("ok\n")
        self.unit["env"].update({"AIR2LEAN_S390X_RUN": "no-such-runner-air2lean -cpu max",
                                 "AIR2LEAN_X86_64_RUN": ""})
        status, out, err = self.run_checks()
        self.assertEqual(status, 1, out + err)
        self.assertIn("missing prerequisite: AIR2LEAN_S390X_RUN=no-such-runner-air2lean -cpu max", err)
        self.unit["runner"] = "s390x-linux"  # a unit for another host runs no native step here
        self.assertEqual(self.run_checks()[0], 0)

    def test_a_unit_that_rebuilds_a_root_module_fails_the_run(self):
        # The race of 2026-10-20: a unit rebuilt root modules in place while others imported them.
        shared = self.temp / "build"
        (shared / "M").mkdir(parents=True)
        (shared / "M" / "A.olean").write_text("a")
        (shared / "M" / "A.trace").write_text("t")
        (self.hidden / "input").write_text("ok\n")
        self.unit["env"]["SHARED"] = str(shared)
        with mock.patch.object(fc, "SHARED", (self.temp / "root-build", shared)):
            self.assertEqual(self.run_checks()[0], 0)
            self.unit["run"] = 'printf t2 > "$SHARED/M/A.trace"\n'  # an up-to-date check: no race
            self.assertEqual(self.run_checks()[0], 0)
            self.unit["run"] = 'rm "$SHARED/M/A.olean"; printf b > "$SHARED/M/A.olean"\n'
            status, out, err = self.run_checks()
        self.assertEqual(status, 1, out + err)
        self.assertIn("build outputs changed while the units ran", err)
        self.assertIn("M/A.olean", err)

    def test_the_extractor_is_prepared_before_the_units(self):
        # The race of 2026-11-04: a unit's audit rebuilt tools/Assurance.olean under the others.
        # Its preparation, which may rebuild it, runs before the units, outside the comparison.
        shared = self.temp / "build"
        (shared / "tools").mkdir(parents=True)
        (shared / "tools" / "Assurance.olean").write_text("a")
        (self.hidden / "input").write_text("ok\n")
        marker = self.temp / "unit-ran"
        self.unit["run"] = 'touch "%s"\n' % marker

        def rebuild():
            self.assertFalse(marker.exists(), "a unit ran before the extractor was prepared")
            (shared / "tools" / "Assurance.olean").unlink()
            (shared / "tools" / "Assurance.olean").write_text("b")

        with mock.patch.object(fc, "SHARED", (shared,)), \
                mock.patch.object(fc.assumptions, "prepared_tool", lambda: offline_prepared_tool(rebuild)):
            status, out, err = self.run_checks()
        self.assertEqual(status, 0, out + err)
        self.assertTrue(marker.exists())
        marker.unlink()

        def fail():
            raise RuntimeError("command failed (1): lake --rehash build AssuranceTools assurance")

        with mock.patch.object(fc.assumptions, "prepared_tool", lambda: offline_prepared_tool(fail)):
            status, out, err = self.run_checks()
        self.assertEqual(status, 1, out + err)
        self.assertIn("FAILED the assurance extractor: command failed", err)
        self.assertFalse(marker.exists(), "a unit ran without a prepared extractor")

    def test_the_fixture_package_is_built_before_the_units(self):
        # The race of 2026-11-04 (L8j): a unit rebuilt AuditClaims in the shared fixture package
        # while five other units' audits walked it (a missing AsmTotal.olean, "imported inputs
        # changed"). Every library is built before the units; a failed build stops the run.
        (self.hidden / "input").write_text("ok\n")
        built, marker = self.temp / "fixtures-built", self.temp / "unit-ran"
        self.unit["run"] = '[ -e "%s" ] && touch "%s"\n' % (built, marker)
        with mock.patch.object(fc, "FIXTURE_BUILD", ["sh", "-c", 'touch "%s"' % built]):
            status, out, err = self.run_checks()
        self.assertEqual(status, 0, out + err)
        self.assertTrue(marker.exists())
        marker.unlink()
        with mock.patch.object(fc, "FIXTURE_BUILD", ["sh", "-c", "echo lake failed; exit 1"]):
            status, out, err = self.run_checks()
        self.assertEqual(status, 1, out + err)
        self.assertIn("FAILED the proof-fixture package:", err)
        self.assertIn("lake failed", (self.temp / "logs" / "shared-build.log").read_text())
        self.assertFalse(marker.exists(), "a unit ran without the fixture package")

    def test_the_units_share_the_runs_toolchain_digest_and_a_change_fails_the_run(self):
        (self.hidden / "input").write_text("ok\n")
        self.unit["run"] = '[ "$AIR2LEAN_TOOLCHAIN_RUNTIME_RUN" = offline-record ]\n'
        self.assertEqual(self.run_checks()[0], 0)
        for error in (ValueError("toolchain runtime changed during the run"), OSError("no lake")):
            with mock.patch.object(fc.assumptions, "runtime_run", lambda: offline_runtime_run(error)):
                status, out, err = self.run_checks()
            self.assertEqual(status, 1, out + err)
            self.assertIn("the toolchain runtime: " + str(error), err)


if __name__ == "__main__":
    unittest.main()
