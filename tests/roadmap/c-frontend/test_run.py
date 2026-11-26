#!/usr/bin/env python3
"""Unit tests of the C front-end harness's record logic (run.py): named gates, the headline
outcome and the function references the export closure follows. No compiler or Lean."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run  # noqa: E402


def entry(**stages):
    return {"stages": stages}


OK = {"status": "ok"}


class Gates(unittest.TestCase):
    def ids(self, e):
        return [g["id"] for g in run.gates(e)]

    def test_goto_demotion_is_gated_by_name(self):
        e = entry(c_native=OK, translate_c={
            "status": "demoted", "demoted_functions": ["run"], "extern_calls": [],
            "warnings": ["f.c:4:17: unable to translate function, demoted to extern", "f.c:6:27: TODO goto"]})
        self.assertEqual(self.ids(e), ["TC-GOTO"])
        self.assertEqual(run.gates(e)[0]["evidence"], "f.c:6:27: TODO goto")
        e["gates"] = run.gates(e)
        self.assertEqual(run.outcome(e), "gated")

    def test_each_translate_c_refusal_has_its_gate(self):
        for gate, warning in (("TC-BITFIELD", "struct demoted to opaque type - has bitfield"),
                              ("TC-VARIADIC-DEF", "TODO unable to translate variadic function, demoted to extern"),
                              ("TC-COMPLEX-SWITCH", "TODO complex switch")):
            e = entry(translate_c={"status": "demoted", "demoted_functions": ["f"], "extern_calls": [],
                                   "warnings": ["f.c:1:1: " + warning]})
            self.assertEqual(self.ids(e), [gate])

    def test_unknown_demotion_is_not_gated(self):
        e = entry(c_native=OK, translate_c={"status": "demoted", "demoted_functions": ["f"], "extern_calls": [],
                                           "warnings": ["f.c:1:1: unable to translate function, demoted to extern"]})
        e["gates"] = run.gates(e)
        self.assertEqual(e["gates"], [])
        self.assertEqual(run.outcome(e), "translate_c")

    def test_a_warning_without_a_demotion_is_no_gate(self):
        e = entry(translate_c={"status": "ok", "demoted_functions": [], "extern_calls": [],
                               "warnings": ["f.c:1:1: TODO goto"]})
        self.assertEqual(self.ids(e), [])

    def test_setjmp_variadic_and_divergence(self):
        e = entry(translate_c={"status": "ok", "demoted_functions": [], "extern_calls": ["longjmp", "setjmp"],
                               "warnings": []},
                  zig_native={"status": "mismatch"},
                  air2lean={"status": "rejected", "diagnostics": [
                      {"message": "f.entry: CALLEE_EXTERN_UNBOUND: extern function 'snprintf' is variadic, outside"}]})
        self.assertEqual(self.ids(e), ["LIBC-SETJMP", "EXT-VARIADIC", "NATIVE-DIVERGENCE"])

    def test_a_demoted_variadic_definition_is_not_a_variadic_extern(self):
        e = entry(translate_c={"status": "demoted", "demoted_functions": ["sum"], "extern_calls": [],
                               "warnings": ["f.c:4:17: TODO unable to translate variadic function, demoted to extern"]},
                  air2lean={"status": "rejected", "diagnostics": [
                      {"message": "f.entry: CALLEE_EXTERN_UNBOUND: extern function 'sum' is variadic, outside"}]})
        self.assertEqual(self.ids(e), ["TC-VARIADIC-DEF"])

    def test_a_compile_error_is_not_a_divergence(self):
        e = entry(translate_c={"status": "ok", "demoted_functions": [], "extern_calls": [], "warnings": []},
                  zig_native={"status": "compile_error"})
        self.assertEqual(self.ids(e), [])

    def test_an_undefined_symbol_is_a_compile_error_with_either_linker(self):
        for log in ("error: undefined symbol: _entry",  # macOS ld64
                    "error: ld.lld: undefined symbol: entry"):  # ELF targets
            self.assertTrue(run.COMPILE_ERROR.search(log), log)
        self.assertIsNone(run.COMPILE_ERROR.search("thread 1 panic: integer overflow"))

    def test_lean_ok_is_never_gated(self):
        checked = {"status": "checked"}
        e = entry(c_native=OK, translate_c=OK, zig_native=OK, air_export=OK, air2lean=checked, lean=OK)
        e["gates"] = [{"id": "TC-GOTO", "evidence": "stale"}]
        self.assertEqual(run.outcome(e), "lean_ok")

    def test_a_demoted_file_is_never_lean_ok(self):
        # A function translate-c demoted to an extern is not in the program the later stages check.
        e = entry(c_native=OK, translate_c={"status": "demoted", "demoted_functions": ["f"], "extern_calls": [],
                                            "warnings": []},
                  zig_native=OK, air_export=OK, air2lean={"status": "checked"}, lean=OK)
        self.assertEqual(run.outcome(e), "translate_c")

    def test_deferred_lean_is_not_ok(self):
        e = entry(c_native=OK, translate_c=OK, zig_native=OK, air_export=OK,
                  air2lean={"status": "checked"}, lean={"status": "deferred"})
        self.assertEqual(run.outcome(e), "lean")


class Closure(unittest.TestCase):
    def test_function_refs_cover_callees_values_and_global_initializers(self):
        doc = {"name": "c_f.entry",
               "body": [{"tag": "call", "callee": {"func": "mem.zeroes__func_0"}, "args": [{"func": "c_f.cb"}]},
                        {"tag": "call", "callee": {"extern": "strlen"}}],
               "globals": [{"name": "c_f.table", "init": {"elems": [{"func": "c_f.other"}]}}]}
        self.assertEqual(run.function_refs(doc, {}), {"mem.zeroes__func_0", "c_f.cb", "c_f.other"})
        # An extern symbol references the function of the compilation that defines it.
        self.assertEqual(run.function_refs(doc, {"strlen": {"compiler_rt.strlen"}, "abs": {"c.stdlib.abs"}}),
                         {"mem.zeroes__func_0", "c_f.cb", "c_f.other", "compiler_rt.strlen"})

    def test_symbol_definitions_are_the_export_table_functions(self):
        with tempfile.TemporaryDirectory() as tmp:
            air = Path(tmp)
            self.assertEqual(run.symbol_definitions(air), {})
            (air / run.EXPORT_TABLE).write_text(json.dumps({"schema": 12, "zig_version": "0.17.1", "exports": [
                {"name": "abs", "linkage": "weak", "visibility": "hidden",
                 "function": {"module": "zigc", "name": "c.stdlib.abs", "cc": "x86_64_sysv"}},
                {"name": "environ", "linkage": "weak", "visibility": "default", "function": None}]}))
            self.assertEqual(run.symbol_definitions(air), {"abs": {"c.stdlib.abs"}})

    def test_module_name_is_not_a_std_file_name(self):
        self.assertEqual(run.module_name("enums"), "c_enums")


if __name__ == "__main__":
    unittest.main()
