#!/usr/bin/env python3
"""Offline harness checks only; actual AIR/Lean/native validation is still required."""
import importlib.util
import json
import os
import shutil
import subprocess
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE/(name+".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


native = load("native_checks")
mutations = load("mutations")


class HarnessTests(unittest.TestCase):
    def setup_air(self, directory):
        names = ["walk", "nested", "fixedCapture", "ranges", "enumStep", "unionWalk"]
        for name in names:
            body = [{"tag": "loop_switch_br", "id": 10, "cases": [{"body": [
                {"tag": "switch_dispatch", "target": 10}]}]}]
            if name == "nested":
                body[0]["cases"][0]["body"].append({"tag": "loop_switch_br", "id": 30,
                    "else": [{"tag": "switch_dispatch", "target": 30}]})
            (directory/(name+".json")).write_text(json.dumps({
                "name": "source."+name, "zig_version": "0.16.0", "body": body}))

    def invoke(self, directory, version="0.16.0"):
        with patch.object(sys, "argv", ["native_checks.py", str(directory), version,
                                         str(directory/"checks.lean")]):
            native.main()

    def test_fresh_inventory_and_semantic_checks(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            self.setup_air(directory)
            self.invoke(directory)
            checks = (directory/"checks.lean").read_text()
            self.assertIn("DispatchNative.walk 255 0", checks)
            self.assertIn("DispatchNative.unionWalk 255", checks)
            self.assertIn("some 128", checks)
            (directory/"walk.json").unlink()
            with self.assertRaises(AssertionError): self.invoke(directory)

    def test_wrong_release_and_missing_nested_target_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            self.setup_air(directory)
            with self.assertRaises(AssertionError): self.invoke(directory, "0.15.2")
            path = directory/"nested.json"
            raw = json.loads(path.read_text())
            raw["body"][0]["cases"][0]["body"][-1]["else"][0]["target"] = 10
            path.write_text(json.dumps(raw))
            with self.assertRaises(AssertionError): self.invoke(directory)

    def test_all_mutation_anchors_and_missing_anchor_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory/"step.lean").write_text("| dispatch1 (v : BitVec 8)\n"
                "modify fun s => { s with dispatchValue1 := dispatchValue }\n"
                "modify fun s => { s with dispatchValue1 := p0 }")
            (directory/"nested.lean").write_text("| dispatch2 (v : BitVec 8)\n"
                "| dispatch3 (v : BitVec 8)\npure (.dispatch3 (0 : BitVec 8))")
            (directory/"blockCapture.lean").write_text("pure (.ret i1)")
            outputs = list(mutations.mutants(directory))
            self.assertEqual([name for name,_ in outputs],
                ["dropped_selector","wrong_initial","wrong_target","dropped_capture"])
            self.assertIn("pure (.dispatch2 (2 : BitVec 8))", outputs[2][1])
            with self.assertRaises(AssertionError): mutations.changed_once("absent", "missing", "x")
            with self.assertRaises(AssertionError): mutations.changed_once("x x", "x", "y")
            output = directory/"mutants"
            argv = ["mutations.py", str(directory), str(output)]
            rejected = SimpleNamespace(returncode=1, stdout="mutant.lean:1:1: error: Tactic `native_decide` evaluated that the proposition\n  False\nis false\n", stderr="")
            with patch.object(sys, "argv", argv), patch.object(mutations.subprocess, "run",
                    return_value=rejected) as run, patch("builtins.print"):
                mutations.main()
            self.assertEqual(run.call_count, 4)
            for call, (name, _) in zip(run.call_args_list, outputs):
                self.assertEqual(call.args[0], ["lake", "env", "lean", "-R", str(output),
                    str(output/(name+".lean"))])
                self.assertEqual(call.kwargs["timeout"], 60)
            for result in [SimpleNamespace(returncode=0, stdout="", stderr=""),
                           SimpleNamespace(returncode=1, stdout="syntax error", stderr="")]:
                with patch.object(sys, "argv", argv), patch.object(mutations.subprocess, "run",
                        return_value=result), self.assertRaises(AssertionError):
                    mutations.main()


FALSE = "mutant.lean:37:45: error: Tactic `native_decide` evaluated that the proposition\n  successful value = some 7\nis false\n"
WARNING = "mutant.lean:1:1: warning: Variable name `value` is not explicitly referenced.\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _value\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n"


# Verbatim mutation subprocess diagnostic from guarded queue19 (Lean 4.34.0).
CAPTURED_DROPPED_SELECTOR = """/var/folders/lv/wxxgndbn2214b00_9yjjg_dh0000gn/T/air2lean-dispatch.6LVLA1/mutants/dropped_selector.lean:29:15: warning: Variable name `dispatchValue` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _dispatchValue

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/var/folders/lv/wxxgndbn2214b00_9yjjg_dh0000gn/T/air2lean-dispatch.6LVLA1/mutants/dropped_selector.lean:44:73: error: Tactic `native_decide` evaluated that the proposition
  successful (ExceptT.map BitVec.toNat (Dispatch.step 0)) = some 7
is false
"""

class ClassifierTests(unittest.TestCase):
    def test_normal_false_assertions(self):
        for output in (FALSE, WARNING+FALSE, FALSE+WARNING+FALSE):
            with self.subTest(output=output):
                self.assertTrue(mutations.is_semantic_rejection(1, output))

    def test_captured_unused_warning_and_false_assertion(self):
        self.assertTrue(mutations.is_semantic_rejection(1, CAPTURED_DROPPED_SELECTOR))
        for output in (
                CAPTURED_DROPPED_SELECTOR.replace("evaluated that", "proved that"),
                CAPTURED_DROPPED_SELECTOR.replace("warning: Variable name", "warning: unknown Variable name"),
                CAPTURED_DROPPED_SELECTOR.replace("  [apply] _dispatchValue", "  [apply] compiler crashed"),
                CAPTURED_DROPPED_SELECTOR + "error: unknown module prefix\n",
                "echo: " + CAPTURED_DROPPED_SELECTOR):
            with self.subTest(output=output):
                self.assertFalse(mutations.is_semantic_rejection(1, output))

    def test_signals(self):
        for status in (-9, 137, 143, 2):
            with self.subTest(status=status):
                self.assertFalse(mutations.is_semantic_rejection(status, FALSE))

    def test_mixed_syntax_and_import_errors(self):
        for error in ("mutant.lean:1:1: error: unexpected token\n",
                      "mutant.lean:1:1: error(lean.unknownIdentifier): unknown module\n",
                      "error: unknown module prefix\n"):
            with self.subTest(error=error):
                self.assertFalse(mutations.is_semantic_rejection(1, FALSE+error))

    def test_oom_and_infrastructure(self):
        for noise in ("Killed\n", "out of memory\n", "OOM\n", "error: maximum memory exceeded\n"):
            for output in (noise+FALSE, FALSE+noise, FALSE+WARNING+"  "+noise):
                with self.subTest(output=output):
                    self.assertFalse(mutations.is_semantic_rejection(1, output))

    def test_source_echo_and_incomplete_refutations(self):
        for output in ("example : False := by native_decide\n",
                       FALSE.split(": error: ")[1], "echo: error: "+FALSE,
                       FALSE.replace("is false", ""),
                       FALSE.replace("  successful value = some 7\n", ""),
                       FALSE.replace("successful value = some 7", "example : False := by native_decide"),
                       FALSE+WARNING+"Hint: example : False := by native_decide\n",
                       FALSE+"mutant.lean:1:1: warning: compiler crashed\n"):
            with self.subTest(output=output):
                self.assertFalse(mutations.is_semantic_rejection(1, output))

    def test_success(self):
        self.assertFalse(mutations.is_semantic_rejection(0, FALSE))


class ModeTests(unittest.TestCase):
    def write_stub(self, path, body):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("#!/usr/bin/env bash\nset -euo pipefail\n"+body)
        path.chmod(0o755)

    def setup_repo(self, directory):
        repo = directory/"repo"
        script = repo/"tests/roadmap/dispatch/check.sh"
        script.parent.mkdir(parents=True)
        shutil.copyfile(HERE/"check.sh", script)
        bins = directory/"stubs"
        self.write_stub(bins/"lake", '''printf '%s\n' "lake $*" >> "$DISPATCH_MOCK_LOG"
if [ "${3:-}" = "--run" ]; then
  output="${@: -1}"
  mkdir -p "$output"
  for name in step fixedCapture blockCapture nested crossed ranges boolLoop fieldCollision plainExit blockDispatch; do
    printf '// mocked generated source\n' > "$output/$name.lean"
  done
fi
''')
        self.write_stub(bins/"python3", '''printf '%s\n' "python3 $*" >> "$DISPATCH_MOCK_LOG"
if [ "$1" = "tests/roadmap/dispatch/native_checks.py" ]; then
  printf '// mocked checks\n' > "$4"
fi
''')
        self.write_stub(bins/"zig", '''printf '%s\n' "zig $*" >> "$DISPATCH_MOCK_LOG"
case "$1" in
  version) echo "$AIR2LEAN_DISPATCH_ZIG_VERSION" ;;
  test) ;;
  build-obj) printf '{}\n' > "$ZIG_AIR_JSON_DIR/fresh.json"
    printf '%s\n' "export-dir $ZIG_AIR_JSON_DIR" >> "$DISPATCH_MOCK_LOG" ;;
  *) exit 2 ;;
esac
''')
        self.write_stub(repo/".lake/build/bin/air2lean", '''printf '%s\n' "translator $*" >> "$DISPATCH_MOCK_LOG"
while [ "$1" != "-o" ]; do shift; done
printf '// mocked translation\n' > "$2"
''')
        work = directory/"work"
        work.mkdir()
        env = dict(os.environ, PATH=str(bins)+os.pathsep+os.environ["PATH"], TMPDIR=str(work),
                   DISPATCH_MOCK_LOG=str(directory/"commands.log"),
                   AIR2LEAN_DISPATCH_ZIG_AIR=str(bins/"zig"),
                   AIR2LEAN_DISPATCH_ZIG_STOCK=str(bins/"zig"), AIR2LEAN_DISPATCH_KEEP_WORK="0")
        return script, env

    def test_phase_modes_and_each_native_profile(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            script, env = self.setup_repo(directory)
            exports = []
            for version, args, synthetic, native_run in [
                    ("0.16.0", [], True, True),
                    ("0.15.2", ["--native-only"], False, True),
                    ("0.14.1", ["--native-only"], False, True),
                    ("0.16.0", ["--synthetic-only"], True, False)]:
                log = Path(env["DISPATCH_MOCK_LOG"])
                log.write_text("")
                result = subprocess.run(["bash", str(script), *args],
                    env=dict(env, AIR2LEAN_DISPATCH_ZIG_VERSION=version),
                    capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
                lines = log.read_text().splitlines()
                self.assertIn("lake build Air2Lean Air2Lean.Check Air2Lean.Emit ZigLean air2lean", lines)
                self.assertEqual(any("Proofs.lean" in line for line in lines), synthetic)
                self.assertEqual(any("Emitter.lean" in line for line in lines), synthetic)
                self.assertEqual(any("mutations.py" in line for line in lines), synthetic)
                self.assertEqual(sum("/generated/" in line and line.startswith("lake env lean -R") for line in lines), 10 if synthetic else 0)
                self.assertEqual(sum(line == "zig version" for line in lines), 2 if native_run else 0)
                for marker in ("zig test", "zig build-obj", "python3 tests/roadmap/dispatch/native_checks.py", "translator "):
                    self.assertEqual(any(line.startswith(marker) for line in lines), native_run)
                self.assertEqual(any("/native.lean" in line and line.startswith("lake env lean -R") for line in lines), native_run)
                exports.extend(line for line in lines if line.startswith("export-dir "))
            self.assertEqual(len(exports), 3)
            self.assertEqual(len(set(exports)), 3, "every native profile needs a fresh AIR directory")

    def test_invalid_and_excess_arguments_rejected_before_tools(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            script, env = self.setup_repo(directory)
            for args in (["--unknown"], [""], ["--native-only", "extra"],
                         ["--synthetic-only", "--native-only"]):
                result = subprocess.run(["bash", str(script), *args], env=env,
                    capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 2, result.stdout+result.stderr)
                self.assertFalse(Path(env["DISPATCH_MOCK_LOG"]).exists())


if __name__ == "__main__":
    unittest.main()
