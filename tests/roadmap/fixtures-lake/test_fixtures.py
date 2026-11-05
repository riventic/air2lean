"""scripts/fixtures.py: module-name ownership and mutant verdicts (docs/build-cache.md#proof-fixtures).

A tiny repository stands in for the real one: a root package `air2lean` with the library `Lib`
and a fixture package `tests/roadmap` that requires it by path. Lake builds its few one-line
modules (seconds), without the shared artifact cache.

- Two libraries with a module of the same name: Lake builds one of them and reports success for
  both (the other is never elaborated), so the build refuses; so it does for a fixture module
  under a root of the root package.
- A mutant is killed only when the module that must fail fails itself: a failed import, a module
  that still builds or a missing expected message is no kill.
"""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import threading
import time
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("air2lean_fixtures", ROOT / "scripts/fixtures.py")
fx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fx)


def without_cache():
    """This environment without the shared artifact cache (the tests' modules stay out of it)."""
    env = {k: v for k, v in os.environ.items() if k != "AIR2LEAN_CAS_DIR" and not k.startswith("LAKE_")}
    return mock.patch.dict(os.environ, env, clear=True)


class Repo(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-fixtures-test.")
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name).resolve()
        shutil.copy(ROOT / "lean-toolchain", self.repo / "lean-toolchain")
        self.write("lakefile.toml", 'name = "air2lean"\n[[lean_lib]]\nname = "Lib"\n')
        self.write("Lib.lean", "def lib : Nat := 1\n")
        self.package = self.repo / "tests/roadmap"
        for patch in (mock.patch.object(fx, "ROOT", self.repo), mock.patch.object(fx, "PACKAGE", self.package),
                      without_cache()):
            patch.start()
            self.addCleanup(patch.stop)

    def write(self, name, text):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def fixtures(self, libs):
        self.write("tests/roadmap/lakefile.toml", 'name = "fixtures"\n[[require]]\nname = "air2lean"\npath = "../.."\n'
                   + "".join(f'[[lean_lib]]\nname = "{n}"\nsrcDir = "{d}"\nglobs = {g}\n' for n, d, g in libs))


class Names(Repo):
    def test_same_module_in_two_libraries(self):
        self.write("tests/roadmap/a/Eval.lean", "def x := 1\n")
        self.write("tests/roadmap/b/Eval.lean", 'def y : Nat := "not a Nat"\n')
        self.fixtures([("A", "a", '["Eval"]'), ("B", "b", '["Eval"]')])
        with self.assertRaises(SystemExit) as raised:
            fx.check_names(self.package)
        self.assertIn("module root Eval is in libraries A and B", str(raised.exception))

    def test_root_package_root(self):
        self.write("tests/roadmap/a/Lib/Extra.lean", "def z := 1\n")
        self.fixtures([("A", "a", '["Lib.+"]')])
        with self.assertRaises(SystemExit) as raised:
            fx.check_names(self.package)
        self.assertIn("module root Lib is a root of the root package", str(raised.exception))

    def test_distinct_roots(self):
        self.write("tests/roadmap/a/A/Eval.lean", "def x := 1\n")
        self.write("tests/roadmap/a/Spec.lean", "def s := 1\n")
        self.write("tests/roadmap/b/B/Eval.lean", "def y := 1\n")
        self.fixtures([("A", "a", '["A.+", "Spec"]'), ("B", "b", '["B.+"]')])
        self.assertEqual(fx.check_names(self.package), {"A": ["A.Eval", "Spec"], "B": ["B.Eval"]})
        self.assertEqual(fx.files(self.repo), ["tests/roadmap/a/A/Eval.lean", "tests/roadmap/a/Spec.lean",
                                               "tests/roadmap/b/B/Eval.lean"])


class Mutant(Repo):
    def mutant(self, base, use, expect=()):
        src = self.repo / "src"
        shutil.rmtree(src, ignore_errors=True)
        (src / "Fix").mkdir(parents=True)
        (src / "Fix/Base.lean").write_text(base)
        (src / "Fix/Use.lean").write_text("import Fix.Base\nimport Lib\n" + use)
        return fx.mutant("t", src, ["Fix.Use"], list(expect))

    def test_kill_in_the_module_itself(self):
        self.assertEqual(self.mutant("def base : Nat := 2\n", "example : base = 1 := by decide\n",
                                     ["proved that the proposition"]), 0)

    def test_failed_import_is_no_kill(self):
        self.assertEqual(self.mutant('def base : Nat := "two"\n', "example : base = 1 := by decide\n"), 1)

    def test_still_builds(self):
        self.assertEqual(self.mutant("def base : Nat := 1\n", "example : base = 1 := by decide\n"), 1)

    def test_expected_message_missing(self):
        self.assertEqual(self.mutant("def base : Nat := 2\n", "example : base = 1 := by decide\n",
                                     ["did not evaluate to"]), 1)


class Audit(unittest.TestCase):
    """Controls of `fixtures.py audit` against this repository's extractor (tools.Assurance,
    built by scripts/assumptions.py): a Lake-built module with a `sorry` or a non-standard axiom
    is rejected, a missing named theorem too; an honest one passes."""

    def build(self, text):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-fixtures-audit-test.")
        self.addCleanup(tmp.cleanup)
        workspace = Path(tmp.name)
        # The repository's toolchain: outside the checkout elan would pick its default one, and CI
        # installs elan with none (`elan-init --default-toolchain none`), so `lake` failed at once.
        shutil.copy(ROOT / "lean-toolchain", workspace / "lean-toolchain")
        (workspace / "lakefile.toml").write_text(
            f'name = "fixtures"\n[[require]]\nname = "air2lean"\npath = "{ROOT}"\n'
            '[[lean_lib]]\nname = "AuditControl"\n')
        (workspace / "AuditControl.lean").write_text(text)
        with without_cache():
            done = fx.lake(workspace, ["build", "AuditControl"], capture=True)
        self.assertEqual(done.returncode, 0, done.stdout)  # a setup failure shows Lake's output
        return workspace / ".lake/build/lib/lean"

    def test_sorry_is_rejected(self):
        lib = self.build("theorem honest : 1 + 1 = 2 := rfl\ntheorem sorry_control : (1 : Nat) = 2 := sorry\n")
        self.assertEqual(fx.audit(["AuditControl"], ["honest"], None, lib), 1)

    def rejects(self, lib, problem):
        """`audit` of AuditControl fails, and `problem` (`NAME (AuditControl): TRUST_CLASS:`) is one
        of its problems."""
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            self.assertEqual(fx.audit(["AuditControl"], [], None, lib), 1)
        self.assertIn(problem, err.getvalue())

    def test_project_axiom_is_rejected(self):
        """Also one that no theorem or named declaration reaches: a violation of an audited module."""
        lib = self.build("axiom control_ax : (1 : Nat) = 2\ntheorem axiom_control : (1 : Nat) = 2 := control_ax\n"
                         "axiom unused_ax : (1 : Nat) = 2\n")
        self.rejects(lib, "unused_ax (AuditControl): unexpected-axiom:")

    def test_definition_is_audited(self):
        """A definition whose value carries a proof (as `AllocFba.FBA.ledger`), used by no theorem."""
        lib = self.build("structure Claim where h : (1 : Nat) + 1 = 2\n"
                         "def good_claim : Claim := ⟨rfl⟩\ndef bad_claim : Claim := ⟨sorry⟩\n")
        self.assertEqual(fx.audit(["AuditControl"], ["good_claim", "bad_claim"], None, lib), 1)
        self.assertEqual(fx.audit(["AuditControl"], [], None, lib), 1)  # the sorry, unnamed

    def test_missing_theorem_is_rejected_and_honest_passes(self):
        lib = self.build("theorem honest : 1 + 1 = 2 := rfl\nstructure Claim where h : (1 : Nat) + 1 = 2\n"
                         "def good_claim : Claim := ⟨rfl⟩\n")
        self.assertEqual(fx.audit(["AuditControl"], ["honest", "gone"], None, lib), 1)
        self.assertEqual(fx.audit(["AuditControl"], ["honest", "good_claim"], None, lib), 0)

    def test_unlabeled_float_theorem_is_rejected(self):
        """As the theorem-universe audit: a theorem over the float model needs its label
        (assurance/float-semantics.json); this one has none."""
        self.rejects(self.build("import ZigLean.Float.Value\n"
                                "theorem float_control (x : Zig.F32) : x.bits = x.bits := rfl\n"),
                     "float_control (AuditControl): unlabeled-numerical-theorem:")


class LakeExtraction(unittest.TestCase):
    """`fixtures.py audit` of a package: Lake builds the extractor's driver on the package
    (scripts/assumptions.py --extract-in), so an unchanged audit replays Lake's stored log and a
    changed audited module is extracted again: a sorry added after a pass is rejected."""

    def test_reuse_is_lakes_trace(self):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-fixtures-extraction-test.")
        self.addCleanup(tmp.cleanup)
        package = Path(tmp.name)
        shutil.copy(ROOT / "lean-toolchain", package / "lean-toolchain")
        (package / "lakefile.toml").write_text(
            f'name = "fixtures"\n[[require]]\nname = "air2lean"\npath = "{ROOT}"\n'
            '[[lean_lib]]\nname = "AuditControl"\n')
        source = package / "AuditControl.lean"
        workspace = package / ".lake/extraction"

        def audit(text):
            source.write_text(text)
            with without_cache():
                done = fx.lake(package, ["build", "AuditControl"], capture=True)
                self.assertEqual(done.returncode, 0, done.stdout)
                return fx.audit(["AuditControl"], ["honest"], None, package=package)

        def drivers():
            # One generated workspace per driver (scripts/assumptions.py lake_extraction).
            return sorted(p.relative_to(workspace) for p in workspace.glob("M*/AssuranceExtraction/*.lean"))

        honest = "theorem honest : 1 + 1 = 2 := rfl\n"
        self.assertEqual(audit(honest), 0)
        first = drivers()
        self.assertEqual(len(first), 1)
        olean = workspace / first[0].parts[0] / ".lake/build/lib/lean/AssuranceExtraction" / (first[0].stem + ".olean")
        # The driver's outputs stay out of the package's build directory (the caller's LEAN_PATH).
        self.assertEqual(list((package / ".lake/build/lib/lean").rglob("M*.olean")), [])
        built = olean.stat().st_mtime_ns
        self.assertEqual(audit(honest), 0)  # unchanged: the same driver, replayed, not rebuilt
        self.assertEqual((drivers(), olean.stat().st_mtime_ns), (first, built))
        self.assertEqual(audit(honest + "theorem later : (1 : Nat) = 2 := sorry\n"), 1)
        self.assertNotEqual(olean.stat().st_mtime_ns, built)  # the import changed: extracted again
        self.assertEqual(drivers(), first)


class LakeKernelReplay(unittest.TestCase):
    """A module's kernel check as a Lake-built receipt (tools/KernelReplay.lean,
    scripts/assumptions.py lake_kernel_replay) on the package's own lookup path, as a fixture
    Unit audit uses it: an unchanged module's receipt is replayed, a changed module is checked
    again, and a module the kernel rejects keeps a failing receipt, built and replayed alike."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-fixtures-replay-test.")
        self.addCleanup(tmp.cleanup)
        self.package = Path(tmp.name).resolve()
        shutil.copy(ROOT / "lean-toolchain", self.package / "lean-toolchain")
        (self.package / "lakefile.toml").write_text(
            f'name = "fixtures"\n[[require]]\nname = "air2lean"\npath = "{ROOT}"\n'
            '[[lean_lib]]\nname = "AuditControl"\n')
        self.workspace = self.package / ".lake/replay"
        spec = importlib.util.spec_from_file_location("air2lean_assumptions", ROOT / "scripts/assumptions.py")
        self.assumptions = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.assumptions)
        self.sysroot = Path(self.assumptions.lake_env("LEAN_SYSROOT")).resolve()
        self.checker = self.assumptions.file_sha256(self.sysroot / "bin/leanchecker")
        self.runtime = self.assumptions.toolchain_runtime_sha256(self.sysroot)

    def replay(self, text, environment=without_cache):
        """AuditControl's receipt, with `text` as its source, built under `environment`."""
        (self.package / "AuditControl.lean").write_text(text)
        with environment():
            done = fx.lake(self.package, ["build", "AuditControl"], capture=True)
            self.assertEqual(done.returncode, 0, done.stdout)
            lean_path = fx.lake(self.package, ["env", "printenv", "LEAN_PATH"], capture=True).stdout.strip()
            found = self.assumptions.lake_kernel_replay(["AuditControl"], self.package, self.checker,
                                                        self.runtime, lean_path)
        self.assertIsNotNone(found)  # the package's own lookup path: receipts are used
        return found["AuditControl"]

    def test_receipts_are_lakes_trace(self):
        workspace = self.workspace
        receipts = workspace / ".lake/build/lib/lean/KernelReplay"

        def audit(text):
            """0 when the receipt passes, 1 when it records a rejection."""
            return 0 if self.replay(text)["status"] == "pass" else 1

        def built():
            # The receipt of AuditControl: the one whose source names it.
            sources = [p for p in workspace.glob("KernelReplay/*.lean")
                       if 'run "AuditControl"\n' in p.read_text()]
            self.assertEqual(len(sources), 1, sources)
            return sources[0].name, (receipts / (sources[0].stem + ".olean")).stat().st_mtime_ns

        honest = "theorem honest : 1 + 1 = 2 := rfl\n"
        self.assertEqual(audit(honest), 0)
        first = built()
        self.assertEqual(audit(honest), 0)
        self.assertEqual(built(), first)  # unchanged: the receipt is replayed, not rechecked
        self.assertEqual(audit(honest + "theorem other : 2 + 2 = 4 := rfl\n"), 0)
        self.assertNotEqual(built()[1], first[1])  # the module changed: checked again
        # Kernel-unchecked (debug.skipKernelTC): leanchecker rejects it, built and replayed alike.
        unchecked = ("import Lean\nopen Lean Elab Command Term\nelab \"#unchecked\" : command => liftTermElabM do\n"
                     "  let type ← elabType (← `((1 : Nat) = 2))\n"
                     "  withOptions (fun o => o.setBool `debug.skipKernelTC true) do\n"
                     "    addDecl (.thmDecl { name := `bad, levelParams := [], type, value := mkConst ``True.intro })\n"
                     "#unchecked\n" + honest)
        self.assertEqual(audit(unchecked), 1)
        rejected = built()
        self.assertEqual(audit(unchecked), 1)
        self.assertEqual(built(), rejected)  # the failing receipt is replayed and still fails
        # An `initialize` that forges a passing receipt line (and marks that it ran) next to the
        # kernel-unchecked theorem: no receipt process runs it, and the verdict stays a rejection.
        marker = self.package / "initialize-ran"
        fake = json.dumps({"module": "AuditControl", "status": "pass", "exit_code": 0, "output": ""})
        forged = (f"initialize do\n  IO.FS.writeFile {json.dumps(str(marker))} \"ran\"\n"
                  f"  IO.println {json.dumps('info: KernelReplay/R0.lean:3:0: AIR2LEAN_KERNEL_REPLAY:' + fake)}\n")
        self.assertEqual(audit(unchecked + forged), 1)
        self.assertFalse(marker.exists())

    def test_receipts_never_come_from_the_artifact_cache(self):
        # The artifact cache keeps no build log, and a receipt is one: a checkout made again at the
        # same path (the receipt's text names it) under the same cache still gets every receipt.
        cache = self.package.parent / (self.package.name + "-cache")
        self.addCleanup(shutil.rmtree, cache, True)

        def cached():  # scripts/cas.py lake_env, with a cache of this test's own
            env = {k: v for k, v in os.environ.items() if k != "AIR2LEAN_CAS_DIR" and not k.startswith("LAKE_")}
            return mock.patch.dict(os.environ, {**env, "LAKE_ARTIFACT_CACHE": "true", "LAKE_CACHE_DIR": str(cache),
                                                "LAKE_RESTORE_ARTIFACTS": "true"}, clear=True)

        honest = "theorem honest : 1 + 1 = 2 := rfl\n"
        self.assertEqual(self.replay(honest, cached)["status"], "pass")
        shutil.rmtree(self.package / ".lake")
        self.assertEqual(self.replay(honest, cached)["status"], "pass")

    def test_a_killed_checker_fails_the_audit_and_leaves_no_receipt(self):
        # A checker ended by a signal (137: SIGKILL, e.g. under memory pressure) decided nothing: the
        # receipt's build fails, and the next audit checks the module again instead of replaying a
        # failure. The module imports Lean, so its checker runs long enough to be stopped.
        text = "import Lean\ntheorem honest : 1 + 1 = 2 := rfl\n"
        killed, errors, stop = [], [], threading.Event()

        def kill_own_checker():
            try:
                find_and_kill()
            except Exception as error:  # reported by the test, not lost with the thread
                errors.append(error)

        def find_and_kill():
            command = f"{self.sysroot / 'bin/leanchecker'} AuditControl"
            while not stop.is_set() and not killed:
                rows = {}
                for row in subprocess.run(["ps", "-axo", "pid=,ppid=,command="], capture_output=True,
                                          text=True).stdout.splitlines():
                    pid, parent, rest = (row.split(None, 2) + [""])[:3]
                    rows[int(pid)] = (int(parent), rest)
                for pid, (parent, rest) in rows.items():
                    ancestor = parent
                    while ancestor not in (0, 1, os.getpid()) and ancestor in rows:
                        ancestor = rows[ancestor][0]
                    if rest == command and ancestor == os.getpid():  # a descendant of this test only
                        os.kill(pid, signal.SIGKILL)
                        killed.append(pid)
                time.sleep(0.05)

        killer = threading.Thread(target=kill_own_checker)
        killer.start()
        try:
            with mock.patch("sys.stderr"), self.assertRaisesRegex(RuntimeError, "receipt build failed"):
                self.replay(text)
        finally:
            stop.set()
            killer.join()
        self.assertEqual(errors, [])
        self.assertTrue(killed)
        self.assertEqual(self.replay(text)["status"], "pass")


class ReplayFreshness(unittest.TestCase):
    """scripts/assumptions.py replay_and_freshness: `leanchecker Lib` checks every olean below
    `Lib` (`checked_modules`), also `Lib.Extra`, which `Lib` does not import. A stale one fails
    the trace check before the compiled inputs are bound, rather than being checked as it is or
    rebuilt by a Lake receipt during the replay (which then failed with "canonical Lake compiled
    inputs changed during kernel replay"). An orphan one (no source) fails there too."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-replay-freshness-test.")
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name).resolve()
        shutil.copy(ROOT / "lean-toolchain", self.repo / "lean-toolchain")
        (self.repo / "lakefile.toml").write_text('name = "air2lean"\n[[lean_lib]]\nname = "Lib"\n')
        (self.repo / "Lib.lean").write_text("def lib : Nat := 1\n")
        (self.repo / "Lib").mkdir()
        self.extra = self.repo / "Lib/Extra.lean"
        self.extra.write_text("def extra : Nat := 1\n")
        spec = importlib.util.spec_from_file_location("air2lean_assumptions", ROOT / "scripts/assumptions.py")
        self.assumptions = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.assumptions)
        for patch in (mock.patch.object(self.assumptions, "ROOT", self.repo),
                      mock.patch.object(self.assumptions, "LAKE_ROOTS", ("Lib",)), without_cache()):
            patch.start()
            self.addCleanup(patch.stop)
        self.build("Lib", "Lib.Extra")

    def build(self, *modules):
        done = fx.lake(self.repo, ["build", *modules], capture=True)
        self.assertEqual(done.returncode, 0, done.stdout)

    def audit(self):
        sysroot = Path(self.assumptions.lake_env("LEAN_SYSROOT")).resolve()
        raw = {"extractor": {"lean_sysroot": str(sysroot),
                             "toolchain_runtime_sha256": self.assumptions.toolchain_runtime_sha256(sysroot)},
               "nodes": [], "modules": ["Lib"]}
        freshness = self.assumptions.replay_and_freshness(raw)
        return raw["kernel_replay"]["status"], freshness["lake_trace_check"]["status"]

    def test_stale_olean_below_an_audited_module_fails_before_the_replay(self):
        self.assertEqual(self.audit(), ("pass", "up-to-date"))
        self.extra.write_text("def extra : Nat := 2\n")  # Lib.Extra's olean is now stale
        olean = self.repo / ".lake/build/lib/lean/Lib/Extra.olean"
        before = olean.read_bytes()
        with mock.patch("sys.stderr"), self.assertRaisesRegex(RuntimeError, "--no-build .*Lib.Extra"):
            self.audit()
        self.assertEqual(olean.read_bytes(), before)  # the audit built nothing
        self.build("Lib.Extra")
        self.assertEqual(self.audit(), ("pass", "up-to-date"))

    def test_orphan_olean_below_an_audited_module_fails_before_the_replay(self):
        self.extra.unlink()  # Lib.Extra's olean has no source any more: Lake cannot build it
        with self.assertRaisesRegex(ValueError, "Lib/Extra.olean: compiled module without a source"):
            self.audit()


if __name__ == "__main__":
    unittest.main()
