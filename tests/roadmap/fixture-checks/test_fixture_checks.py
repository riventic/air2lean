#!/usr/bin/env python3
"""scripts/fixture-checks.py: a unit runs unless a pass of exactly its inputs is recorded.

The regression for the false green of a reused pass (docs/ci.md#full-build): a unit whose input
is reached by a path built in code (tests/roadmap/callbacks/mutants.py reaches
`ROADMAP / "asm-effects"`) kept the key of its last pass after that input changed, and the stale
pass was reused while the check failed. A key now covers everything a unit can read
(`run_inputs`: every file of the checkout, the Lake build outputs, the toolchains, the
environment), not the files its text names. Here a synthetic unit reads a file whose path no
text of the unit names; it stands for a file of the checkout (`run_inputs` is replaced by one
that reads it), and `RunInputs` checks the real `run_inputs` on a scratch checkout.
Offline: no toolchain, no Lean.
"""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
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


class Passes(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="air2lean fixture-checks ")
        self.addCleanup(temp.cleanup)
        self.temp = Path(temp.name)
        self.cas = self.temp / "cas"
        self.cas.mkdir()
        self.hidden = self.temp / "hidden"
        self.hidden.mkdir()
        self.runs = self.temp / "runs"
        # The path is assembled at run time: no text of the unit spells out "hidden/input".
        self.unit = {"name": "synthetic: hidden input", "job": "synthetic", "rows": ["synthetic"],
                     "zig": "0.0.0", "checks": ["tests/roadmap/synthetic/check.sh"],
                     "run": 'echo run >> "$RUNS"\nf="$HIDDEN_DIR"/in""put\necho "read $f"\n[ "$(cat "$f")" = ok ]\n',
                     "env": {"HIDDEN_DIR": str(self.hidden), "RUNS": str(self.runs)}, "runner": fc.HOST,
                     "skipped": [], "error": None, "toolchains": {"patched": [], "stock": []}}
        # The hidden file stands for a file of the checkout: an input of every unit.
        inputs = lambda tree: {"checkout": (self.hidden / "input").read_text()}
        for patch in (mock.patch.object(fc, "discover", lambda tree: [dict(self.unit)]),
                      mock.patch.object(fc, "resolve", no_toolchain),
                      mock.patch.object(fc, "run_inputs", inputs),
                      mock.patch.object(fc, "PASSES", self.temp / "passes"),
                      mock.patch.object(fc, "IN_CI", False),  # these tests also run in CI
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

    def runs_of_unit(self):
        return len(self.runs.read_text().split()) if self.runs.exists() else 0

    def test_an_edit_of_an_input_runs_the_unit_again(self):
        (self.hidden / "input").write_text("ok\n")
        status, out, err = self.run_checks()
        self.assertEqual(status, 0, out + err)
        (self.hidden / "input").write_text("broken\n")
        status, out, err = self.run_checks()
        self.assertEqual(status, 1, out + err)  # rerun, not the first run's pass
        self.assertIn("1 failed", out)
        self.assertIn("FAILED synthetic: hidden input", err)
        self.assertEqual(self.run_checks()[0], 1)  # a failure records no pass
        self.assertEqual(self.runs_of_unit(), 3)
        (self.hidden / "input").write_text("ok\n")
        self.assertEqual(self.run_checks()[0], 0)  # the first run's inputs: its pass, no run
        self.assertEqual(self.runs_of_unit(), 3)
        self.assertEqual(list(self.cas.iterdir()), [])  # no pass is published to the shared store

    def test_a_pass_of_the_same_inputs_is_reused_unless_rerun(self):
        (self.hidden / "input").write_text("ok\n")
        self.assertEqual(self.run_checks("--pending")[0], 1)
        self.assertEqual(self.run_checks()[0], 0)
        status, out, _ = self.run_checks()
        self.assertEqual((status, self.runs_of_unit()), (0, 1))
        self.assertIn("a pass of the same inputs is recorded", out)
        self.assertIn("0 units (0 checks) run, 0 failed, 1 with a recorded pass", out)
        self.assertEqual(self.run_checks("--pending")[0], 0)
        self.assertEqual(self.run_checks("--rerun")[0], 0)
        self.assertEqual(self.runs_of_unit(), 2)
        self.unit["run"] += "true\n"  # another CI step: another key
        self.assertEqual(self.run_checks()[0], 0)
        self.assertEqual(self.runs_of_unit(), 3)

    def test_ci_never_reuses_or_records_a_pass(self):
        (self.hidden / "input").write_text("ok\n")
        self.assertEqual(self.run_checks()[0], 0)  # a local run records its pass
        with mock.patch.object(fc, "IN_CI", True):
            for _ in range(2):
                self.assertEqual(self.run_checks()[0], 0)
            self.assertEqual(self.run_checks("--pending")[0], 1)
        self.assertEqual(self.runs_of_unit(), 3)
        self.assertEqual(len(list((self.temp / "passes").iterdir())), 1)  # only the local one

    def test_no_pass_when_an_input_changes_during_the_run(self):
        (self.hidden / "input").write_text("ok\n")
        self.unit["run"] = 'echo run >> "$RUNS"\nprintf "ok\\n\\n" > "$HIDDEN_DIR/input"\n'
        status, out, _ = self.run_checks()
        self.assertEqual(status, 0)
        self.assertIn("the inputs changed during the run: no pass is recorded", out)
        (self.hidden / "input").write_text("ok\n")
        self.run_checks()
        self.assertEqual(self.runs_of_unit(), 2)
        self.assertFalse((self.temp / "passes").exists())

    def test_a_rerun_of_the_staged_command_starts_from_a_fresh_temp(self):
        # build-guard reruns a unit stopped at its charge with the same argv and env; the first
        # attempt's outputs in RUNNER_TEMP are gone, the staged host-zig links stay.
        stock = self.temp / "stock" / "zig"
        stock.parent.mkdir()
        unit = dict(self.unit, toolchains={"patched": [], "stock": ["9.9.9"]},
                    run='[ ! -e "$RUNNER_TEMP/out" ]\nmkdir "$RUNNER_TEMP/out"\n'
                        '[ -d "$RUNNER_TEMP/host-zig-9.9.9" ]\n')
        with mock.patch.object(fc, "resolve", lambda kind, version: stock if version == "9.9.9"
                               else no_toolchain(kind, version)):
            argv, env = fc.stage(unit, self.temp / "scratch")
        for _ in range(2):
            run = subprocess.run(argv, env=env, capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(sorted(p.name for p in (self.temp / "scratch" / "temp").iterdir()),
                         ["host-zig-9.9.9", "out"])

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

    def test_a_unit_never_measured_is_charged_the_measured_units_typical_request(self):
        # The rule of a Lean module never measured (lean-peaks.py `typical`), not the declared
        # bound: an 11000 MiB charge made every new unit an 11-slot queue head.
        units = [{"name": "u%02d" % k} for k in range(1, 21)] + [{"name": "new"}]
        hints = {u["name"]: {"elapsed_s": 1, "lean_threads": 1, "peak_rss_kib": [(100 * k) << 10]}
                 for k, u in enumerate(units[:-1], 1)}
        (self.temp / "schedule.json").write_text(json.dumps(hints))
        with mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "1"}):
            requests = fc.schedule(units, 5000, elastic=True)[1]
            self.assertEqual(requests[:-1], [max(fc.MEM_FLOOR_MIB, int(100 * k * fc.MEM_MARGIN))
                                             for k in range(1, 21)])
            # The 95th percentile (nearest rank: the 19th of 20), not the largest.
            self.assertEqual(requests[-1], int(1900 * fc.MEM_MARGIN))
            # Of every unit measured, not only those selected (--only): the guess is the machine's.
            self.assertEqual(fc.schedule([units[0], units[-1]], 5000, elastic=True)[1],
                             [requests[0], requests[-1]])
            self.assertEqual(fc.schedule(units, 5000)[1][-1], 5000)  # not elastic: no limit backs it
            with mock.patch.object(fc.GUARD, "PROCESS_MIB", 2000):
                self.assertEqual(fc.schedule(units, 5000, elastic=True)[1][-1], 2000)  # at most the bound
            (self.temp / "schedule.json").write_text("{}")
            self.assertEqual(fc.schedule(units, 5000, elastic=True)[1], [fc.GUARD.PROCESS_MIB] * 21)  # none measured

    def test_a_unit_in_an_elastic_guard_is_a_sub_admission_charged_its_request(self):
        grant = {"lock": "/l/build.lock", "elastic": {"id": "e"}}
        with mock.patch.dict(os.environ, {fc.GUARD.INHERIT: json.dumps(grant)}):
            self.assertEqual(fc.elastic_grant(), grant)
        for value in (json.dumps({"lock": "/l/build.lock"}), "not json", ""):  # plain, malformed, none
            with mock.patch.dict(os.environ, {fc.GUARD.INHERIT: value}):
                self.assertIsNone(fc.elastic_grant())
        with mock.patch.dict(os.environ, {"AIR2LEAN_JOBS": "8", "LEAN_NUM_THREADS": "2"}):
            argv = fc.admitted(["bash", "-c", "check"], 3474, grant)
        options = argv[argv.index("--sub-admission"):argv.index("--")]
        pairs = dict(zip(options[1::2], options[2::2]))
        self.assertEqual((pairs["--charge-mib"], pairs["--rss-mib"], pairs["--lock"]),
                         ("3474", str(fc.GUARD.PROCESS_MIB), "/l/build.lock"))
        # The units' jobs and Lean threads, which the sub-admission's guard sets again.
        self.assertEqual((pairs["--jobs"], pairs["--lean-threads"]), ("8", "2"))
        self.assertEqual(argv[argv.index("--") + 1:], ["bash", "-c", "check"])

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

        # The inputs are the ones just passed (the mock is no input): --rerun runs the unit.
        with mock.patch.object(fc.assumptions, "prepared_tool", lambda: offline_prepared_tool(fail)):
            status, out, err = self.run_checks("--rerun")
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
            status, out, err = self.run_checks("--rerun")
        self.assertEqual(status, 1, out + err)
        self.assertIn("FAILED the proof-fixture package:", err)
        self.assertIn("lake failed", (self.temp / "logs" / "shared-build.log").read_text())
        self.assertFalse(marker.exists(), "a unit ran without the fixture package")

    def test_the_units_share_the_runs_toolchain_digest_and_a_change_fails_the_run(self):
        (self.hidden / "input").write_text("ok\n")
        self.unit["run"] = '[ "$AIR2LEAN_TOOLCHAIN_RUNTIME_RUN" = offline-record ]\n'
        self.assertEqual(self.run_checks()[0], 0)
        shutil.rmtree(self.temp / "passes")
        for error in (ValueError("toolchain runtime changed during the run"), OSError("no lake")):
            with mock.patch.object(fc.assumptions, "runtime_run", lambda: offline_runtime_run(error)):
                status, out, err = self.run_checks()
            self.assertEqual(status, 1, out + err)
            self.assertIn("the toolchain runtime: " + str(error), err)
        # The unit itself passed, but its run failed a shared step: no pass is recorded.
        self.assertFalse((self.temp / "passes").exists())


class RunInputs(unittest.TestCase):
    """`run_inputs` covers every file of a scratch worktree (ignored ones and every `.lake` too),
    its git state, the toolchain, the stock Zig every unit runs and the environment, but not the
    run's own variables; what it cannot read makes the run unkeyable."""

    def test_every_file_git_state_compiler_and_variable_is_an_input(self):
        with tempfile.TemporaryDirectory() as directory:
            root, sysroot, zig = Path(directory) / "wt", Path(directory) / "lean", Path(directory) / "zig"
            for d in (root, sysroot / "bin", zig / "lib"):
                d.mkdir(parents=True)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "tracked").write_text("1")
            (root / ".gitignore").write_text(".lake/\nignored\n")
            subprocess.run(["git", "-C", str(root), "add", "tracked", ".gitignore"], check=True)
            (root / "untracked").write_text("1")
            (root / "ignored").write_text("1")
            build = root / "tests/roadmap/.lake/build/lib/lean"
            build.mkdir(parents=True)
            (build / "M.olean").write_text("1")
            (root / ".lake/assurance").mkdir(parents=True)
            (root / "__pycache__").mkdir()
            (sysroot / "bin/lean").write_text("lean")
            (zig / "zig").write_text("zig")
            (zig / "lib/std.zig").write_text("std")
            outside = Path(directory) / "outside"
            outside.write_text("1")
            unit = {"name": "u", "zig": "0.16.0", "toolchains": {"patched": [], "stock": []}}
            with mock.patch.object(fc, "ROOT", root), \
                    mock.patch.object(fc.assumptions, "lake_env", lambda name: str(sysroot)), \
                    mock.patch.object(fc, "resolve", lambda kind, version: zig / "zig"), \
                    mock.patch.dict(os.environ, {"AIR2LEAN_JOBS": "1"}):
                key = lambda: fc.CAS.digest(fc.run_inputs([unit]))
                first = key()
                (root / "__pycache__/m.pyc").write_text("bytecode")  # bytecode: no input
                for variable in ("AIR2LEAN_JOBS", "PWD", "CLAUDE_CODE_SESSION_ID", "WARP_X", "TERM", "TERM_PROGRAM"):
                    os.environ[variable] = "changed"
                self.assertEqual(key(), first)
                git = lambda *args: subprocess.run(["git", "-C", str(root), *args], check=True)
                for change in (lambda: (root / "tracked").write_text("2"),
                               lambda: (root / "untracked").write_text("2"),
                               lambda: (root / "ignored").write_text("2"),
                               lambda: (root / "new").write_text(""),
                               lambda: (build / "M.olean").write_text("2"),
                               lambda: (root / ".lake/assurance/cache.json").write_text("{}"),
                               lambda: git("add", "untracked"),
                               lambda: (root / "link").symlink_to(outside),
                               lambda: outside.write_text("2"),
                               lambda: (sysroot / "bin/lean").write_text("lean2"),
                               lambda: (zig / "lib/std.zig").write_text("std2"),
                               lambda: os.environ.__setitem__("SOME_NEW_VARIABLE", "1"),
                               lambda: os.environ.__setitem__("TERMINFO", "x")):
                    before = key()
                    change()
                    self.assertNotEqual(key(), before)
                with mock.patch.object(fc.assumptions, "lake_env", lambda name: ""), self.assertRaises(fc.Unkeyable):
                    key()


if __name__ == "__main__":
    unittest.main()
