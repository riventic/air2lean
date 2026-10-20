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
        self.assertEqual(sorted(hint), ["elapsed_s", "peak_rss_kib"])  # measurements, no status
        (self.hidden / "input").write_text("broken\n")
        self.assertEqual(self.run_checks()[0], 1)  # a measured unit still runs and fails
        units = [{"name": n} for n in ("short", "long", "new")]
        (self.temp / "schedule.json").write_text(json.dumps({
            "short": {"elapsed_s": 1, "peak_rss_kib": [100 << 10]},
            "long": {"elapsed_s": 9, "peak_rss_kib": [4000 << 10, 6000 << 10]}}))
        order, requests = fc.schedule(units, 5000)
        self.assertEqual([units[i]["name"] for i in order], ["new", "long", "short"])
        self.assertEqual(requests, [fc.MEM_FLOOR_MIB, int(6000 * fc.MEM_MARGIN), 5000])

    def test_the_default_guard_stays_within_an_enclosing_admission(self):
        # A nested guard above its enclosing admission is refused (build-guard.py `inherited`).
        guard_spec = importlib.util.spec_from_file_location("air2lean_build_guard", ROOT / "scripts/build-guard.py")
        guard = importlib.util.module_from_spec(guard_spec)
        guard_spec.loader.exec_module(guard)
        for grant, expected in ((None, fc.GUARD_RSS_MIB), ({"rss_mib": 22000}, 22000),
                                ({"rss_mib": 11000.0}, 11000), ({"rss_mib": 64000}, fc.GUARD_RSS_MIB),
                                ({"rss_mib": True}, fc.GUARD_RSS_MIB), ("not json", fc.GUARD_RSS_MIB)):
            value = grant if isinstance(grant, str) else json.dumps(grant)
            with self.subTest(grant=grant), mock.patch.dict(os.environ, {guard.INHERIT: value}):
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

    def test_a_unit_that_rebuilds_a_root_module_fails_the_run(self):
        # The race of 2026-10-20: a unit rebuilt root modules in place while others imported them.
        shared = self.temp / "build"
        (shared / "M").mkdir(parents=True)
        (shared / "M" / "A.olean").write_text("a")
        (shared / "M" / "A.trace").write_text("t")
        (self.hidden / "input").write_text("ok\n")
        self.unit["env"]["SHARED"] = str(shared)
        with mock.patch.object(fc, "SHARED", shared):
            self.assertEqual(self.run_checks()[0], 0)
            self.unit["run"] = 'printf t2 > "$SHARED/M/A.trace"\n'  # an up-to-date check: no race
            self.assertEqual(self.run_checks()[0], 0)
            self.unit["run"] = 'rm "$SHARED/M/A.olean"; printf b > "$SHARED/M/A.olean"\n'
            status, out, err = self.run_checks()
        self.assertEqual(status, 1, out + err)
        self.assertIn("build outputs changed while the units ran", err)
        self.assertIn("M/A.olean", err)


if __name__ == "__main__":
    unittest.main()
