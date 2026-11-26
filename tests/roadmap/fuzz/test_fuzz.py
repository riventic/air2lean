#!/usr/bin/env python3
"""Offline Q01 regressions: generator determinism, oracles and shrinker minimality.

Synthetic oracles stand in for the translator and compilers; nothing here runs a tool.
"""
import hashlib
import json
import math
from pathlib import Path
import random
import struct
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import air_fuzz  # noqa: E402
import shrink  # noqa: E402
import softfloat  # noqa: E402
import zig_gen  # noqa: E402


class DeltaDebugging(unittest.TestCase):
    def test_ddmin_is_one_minimal(self):
        calls = []

        def fails(items):
            calls.append(len(items))
            return 3 in items and 11 in items

        self.assertEqual(shrink.ddmin(range(20), fails), [3, 11])

    def test_ddmin_can_remove_everything(self):
        self.assertEqual(shrink.ddmin([1, 2, 3], lambda items: True), [])

    def test_json_shrinks_to_failing_core(self):
        doc = {"a": [1, 2, {"bad": 7, "x": "long string"}], "b": "y", "c": {"d": [None, True]}}

        def fails(value):
            return any(isinstance(n, dict) and n.get("bad") == 7 for _, n in shrink.nodes(value))

        self.assertEqual(shrink.shrink_json(doc, fails), {"bad": 7})

    def test_bytes_shrink_to_failing_token(self):
        data = b'{"schema": 11, "extra": "\\uZZZZ", "name": "f"}'
        self.assertEqual(shrink.shrink_bytes(data, lambda b: b"\\uZ" in b), b"\\uZ")


class AirFuzz(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.corpus = air_fuzz.load_corpus()
        cls.vocab = air_fuzz._vocabulary(cls.corpus)

    def test_generation_is_reproducible(self):
        for seed in range(40):
            first = air_fuzz.generate(seed, self.corpus, self.vocab)
            self.assertEqual(first, air_fuzz.generate(seed, self.corpus, self.vocab))
        distinct = {tuple(air_fuzz.generate(s, self.corpus, self.vocab)[0]) for s in range(40)}
        self.assertGreater(len(distinct), 35)

    def test_legacy_corpus_keeps_its_seeds(self):
        # The mixed corpus (CI's first run, the committed regressions' seeds) is unchanged: the
        # schema-11 in-file seeds first, then every golden file.
        names = [name for name, _ in self.corpus[:3]]
        self.assertEqual(names, ["builtin:ident", "builtin:call", "builtin:global"])
        self.assertTrue(all(docs[0]["schema"] == 11 and docs[0]["zig_version"] == "0.16.0"
                            for _, docs in self.corpus[:3]))
        self.assertEqual(self.vocab[3:], ([], []))

    def test_version_corpus_is_that_versions_air_only(self):
        for version in air_fuzz.supported_versions():
            corpus = air_fuzz.load_corpus(version)
            seeds = corpus[:3]
            self.assertEqual([name for name, _ in seeds], ["builtin:ident", "builtin:call", "builtin:global"])
            for _, docs in corpus:
                for doc in docs:
                    self.assertEqual(doc["zig_version"], version)
                    # Older versions also have legacy schema-11 goldens (no profile).
                    if doc["schema"] == 12:
                        self.assertEqual(doc["profile"]["zig_version"], version)
            self.assertTrue(all(docs[0]["schema"] == 12 for _, docs in seeds))
            # The seeds use the version's schema-12 fields: module, typed callee, full pointer type.
            self.assertEqual(seeds[1][1][0]["body"][1]["callee"]["module"], "root")
            self.assertIn("address_space", seeds[2][1][0]["types"][3])
            sources = {name for name, _ in corpus[3:]}
            self.assertTrue(any(name.startswith("tests/golden/") for name in sources), version)
        corpus = air_fuzz.load_corpus("0.17.1")
        tags, _, _, foreign, others = air_fuzz._vocabulary(corpus, "0.17.1")
        # 0.17's renamed tags come from its exports (fixture manifests too), 0.16's names are foreign.
        self.assertTrue({"bit_cast", "bit_cast_safe", "ptr_cast", "int_cast", "div_ceil"} <= set(tags))
        self.assertTrue({"bitcast", "intcast", "struct_field_val", "bool_and"} <= set(foreign))
        self.assertFalse(set(foreign) & set(tags))
        self.assertEqual(sorted(others), sorted(set(air_fuzz.supported_versions()) - {"0.17.1"}))

    def test_version_generation_is_reproducible_and_uses_the_version_mutations(self):
        corpus = air_fuzz.load_corpus("0.17.1")
        vocab = air_fuzz._vocabulary(corpus, "0.17.1")
        steps = []
        for seed in range(300):
            first = air_fuzz.generate(seed, corpus, vocab)
            self.assertEqual(first, air_fuzz.generate(seed, corpus, vocab))
            steps += first[1]["steps"]
        self.assertTrue(any("zig_version" in step for step in steps))
        foreign = set(vocab[3])
        self.assertTrue(any(step.startswith("doc") and " tag " in step and step.rsplit("-> ", 1)[1] in foreign
                            for step in steps))

    def test_emit_oracle(self):
        header = "-- air2lean-profile: {}\n"
        self.assertIsNone(air_fuzz.classify_emit(0, "", header + "def f := 1\n"))
        self.assertEqual(air_fuzz.classify_emit(
            0, "", header + '(air2lean_emitter_placeholder "unbound inst 3")'), "emit:placeholder")
        # The CLI's fail-closed rejection of a placeholder is still a checker gap, so a finding.
        self.assertEqual(air_fuzz.classify_emit(
            1, "error: EMITTER_PLACEHOLDER: translator bug", air_fuzz.SENTINEL), "emit:placeholder")
        self.assertEqual(air_fuzz.classify_emit(0, "", "garbage"), "emit:bad-output")
        self.assertIsNone(air_fuzz.classify_emit(1, "x.json: offset 3: expected: \"", air_fuzz.SENTINEL))
        self.assertEqual(air_fuzz.classify_emit(1, "", air_fuzz.SENTINEL), "emit:untyped-rejection")
        self.assertEqual(air_fuzz.classify_emit(1, "e", header), "emit:partial-output")
        self.assertEqual(air_fuzz.classify_emit(1, "PANIC at Foo", air_fuzz.SENTINEL), "emit:internal-panic")
        self.assertEqual(air_fuzz.classify_emit(-11, "", ""), "emit:exit--11")
        self.assertEqual(air_fuzz.classify_emit(None, "", ""), "emit:timeout")

    def test_diagnostics_oracle(self):
        def report(status, codes):
            return json.dumps({"kind": "air2lean-check-diagnostics", "status": status,
                               "diagnostics": [{"code": c} for c in codes]})

        self.assertIsNone(air_fuzz.classify_diagnostics(0, report("checked", []), ""))
        self.assertIsNone(air_fuzz.classify_diagnostics(1, report("rejected", ["JSON_SYNTAX"]), ""))
        self.assertEqual(air_fuzz.classify_diagnostics(1, report("checked", []), ""), "diag:status-mismatch")
        self.assertEqual(air_fuzz.classify_diagnostics(1, report("rejected", ["NEW_CODE"]), ""),
                         "diag:unknown-code")
        self.assertEqual(air_fuzz.classify_diagnostics(1, report("rejected", ["PREREQUISITE_SKIPPED"]), ""),
                         "diag:untyped-rejection")
        self.assertEqual(air_fuzz.classify_diagnostics(1, report("rejected", ["EMITTER_PLACEHOLDER"]), ""),
                         "diag:placeholder")
        self.assertIsNone(air_fuzz.classify_diagnostics(1, report("rejected", ["PACKED_LAYOUT"]), ""))
        self.assertEqual(air_fuzz.classify_diagnostics(0, "{", ""), "diag:not-json")
        self.assertEqual(air_fuzz.classify_diagnostics(134, "", ""), "diag:exit-134")

    def test_modes_must_agree_except_for_diagnostic_limits(self):
        self.assertIsNone(air_fuzz.disagreement(1, 1, {"JSON_SYNTAX"}))
        self.assertIsNone(air_fuzz.disagreement(0, 1, {"INPUT_LIMIT"}))
        self.assertEqual(air_fuzz.disagreement(0, 1, {"INPUT_LIMIT", "TYPE_FAILURE"}), "mode-disagreement")
        self.assertEqual(air_fuzz.disagreement(1, 0, set()), "mode-disagreement")
        report = json.dumps({"diagnostics": [{"code": "INPUT_LIMIT"}, {"code": "PREREQUISITE_SKIPPED"}]})
        self.assertEqual(air_fuzz.diagnostic_codes(report), {"INPUT_LIMIT"})
        self.assertEqual(air_fuzz.diagnostic_codes("{"), set())

    def test_case_shrinks_to_minimal_input(self):
        def fake(binary, files, modes=("emit", "diag"), timeout=0):
            for data in files:
                try:
                    doc = json.loads(data)
                except ValueError:
                    continue
                if any(isinstance(n, dict) and n.get("tag") == "bad" for _, n in shrink.nodes(doc)):
                    return "emit:placeholder", {}
            return None, {}

        big = json.loads(json.dumps(self.corpus[0][1][0]))
        big["body"][0]["tag"] = "bad"
        files = [air_fuzz._dump(self.corpus[1][1][0]), air_fuzz._dump(big), b"{"]
        with mock.patch.object(air_fuzz, "evaluate", fake):
            shrunk = air_fuzz.shrink_case("unused", files, "emit:placeholder")
        self.assertEqual([json.loads(f) for f in shrunk], [{"tag": "bad"}])

    def test_committed_regressions_are_well_formed(self):
        cases = sorted(p for p in air_fuzz.REGRESSIONS.iterdir() if p.is_dir())
        self.assertTrue(cases, "expected at least one committed shrunk regression")
        for case in cases:
            meta = json.loads((case / "case.json").read_text())
            self.assertEqual(case.name, air_fuzz.case_name(meta["seed"], meta.get("zig_version")))
            self.assertIn(meta["expected_exit"], (0, 1))
            self.assertTrue(meta["original_failure"])
            self.assertTrue(list(case.glob("[0-9][0-9].json")))


def _program(body, ret=("lit", "u32", 0), funcs=(), globals_=(), profile=None):
    work = {"name": "work", "params": [["p0", "u32"], ["p1", "u32"]], "err": False,
            "body": json.loads(json.dumps(body)), "ret": list(ret)}
    program = {"seed": 0, "globals": [dict(g) for g in globals_], "funcs": list(funcs) + [work]}
    if profile:
        program["profile"] = profile
    return program


LIT = lambda ty, v: ["lit", ty, v]  # noqa: E731
EXT_TYPES = {"ints": ["i7", "u9", "i33"], "floats": ["f32"], "elem": "i7", "len": 3, "fields": {"x": "i7", "y": "u9"},
             "opt": "u9"}


def _ext(body, ret=("lit", "u32", 0), funcs=(), globals_=(), types=EXT_TYPES):
    return {**_program(body, ret, funcs, globals_, "ext"), "types": json.loads(json.dumps(types))}


class ZigGenerator(unittest.TestCase):
    def test_generation_is_deterministic_and_well_typed(self):
        for seed in range(150):
            program = zig_gen.generate(seed)
            self.assertIsNone(zig_gen.typecheck_error(program), seed)
            self.assertEqual(program, zig_gen.generate(seed))
            self.assertEqual(zig_gen.render(program), zig_gen.render(zig_gen.generate(seed)))

    def test_every_feature_is_generated(self):
        seen = set()
        for seed in range(150):
            seen |= zig_gen.features(zig_gen.generate(seed))
        self.assertEqual(seen, set(zig_gen.FEATURES))

    def test_core_profile_is_the_original_subset(self):
        # The heavy differential verified these seeds (docs/fuzzing.md): the core generator must not drift.
        digest = hashlib.sha256()
        for seed in range(40):
            digest.update(zig_gen.render(zig_gen.generate(seed)).encode())
        self.assertEqual(digest.hexdigest(), "719bcb5aae6b56ba6b99942d0afa02e3c08e728e799dcb969bd47c5f5db2149f")
        for seed in range(150):
            self.assertNotIn("profile", zig_gen.generate(seed))
            text = json.dumps(zig_gen.generate(seed))
            for tag in sorted(zig_gen.WIDE_STMT_TAGS) + ['"u16"', '"u64"', '"i64"', '"index"', '"field"']:
                self.assertNotIn(tag if tag.startswith('"') else f'["{tag}"', text)

    def test_wide_profile_is_deterministic_well_typed_and_covers_its_features(self):
        seen = set()
        for seed in range(150):
            program = zig_gen.generate(seed, "wide")
            self.assertEqual(program["profile"], "wide")
            self.assertIsNone(zig_gen.typecheck_error(program), seed)
            self.assertEqual(program, zig_gen.generate(seed, "wide"))
            self.assertEqual(zig_gen.render(program), zig_gen.render(json.loads(json.dumps(program))))
            seen |= zig_gen.features(program)
        self.assertEqual(seen, set(zig_gen.WIDE_FEATURES))

    def test_wide_constructs_are_rejected_in_the_core_profile(self):
        body = [["let_array", "ar1", [LIT("u32", 1)] * 4]]
        self.assertTrue(zig_gen.typecheck(_program(body, profile="wide")))
        self.assertFalse(zig_gen.typecheck(_program(body)))
        self.assertFalse(zig_gen.typecheck(_program([["let", "x1", "u64", LIT("u64", 1)]])))
        self.assertTrue(zig_gen.typecheck(_program([["let", "x1", "u64", LIT("u64", 1)]], profile="wide")))

    def test_typecheck_rejects_invalid_wide_programs(self):
        array = ["let_array", "ar1", [LIT("u32", 1)] * 4]
        bad = [
            [["let_array", "ar1", [LIT("u32", 1)] * 3]],                                     # wrong length
            [array, ["arr_set", "ar1", ["call", "f0", []], "=", LIT("u32", 0)]],            # impure index
            [array, ["arr_set", "ar1", ["var", "g0"], "=", LIT("u32", 0)]],                  # global index
            [array, ["let_slice", "sl2", "ar1", 3, 5]],                                      # bounds
            [array, ["let_slice", "sl2", "ar1", 2, 2], ["sstore", "sl2", LIT("u32", 0), "=", LIT("u32", 1)]],  # empty
            [["arr_set", "nope", LIT("u32", 0), "=", LIT("u32", 0)]],                        # unbound
            [["let_opt", "op1", LIT("bool", True), LIT("u32", 1)],
             ["let", "x2", "u32", ["field", "op1", "x"]]],                                   # not a struct
            [["let_struct", "st1", LIT("u32", 1), LIT("u32", 1)]],                           # y is i32
            [["let_opt", "op1", LIT("bool", True), LIT("u32", 1)],
             ["if_opt", "op1", "o2", [["return", LIT("u32", 1)]], [["return", LIT("u32", 2)]]]],  # unreachable return
            [["defer", [["let_array", "ar1", [LIT("u32", 1)] * 4]]]],                        # wide statement in defer
            [["let", "x1", "u32", ["cast", "widen64", LIT("u32", 1)]]],                      # cast to the wrong type
        ]
        globals_ = [{"name": "g0", "ty": "u32", "init": 0}]
        for body in bad:
            self.assertFalse(zig_gen.typecheck(_program(body, profile="wide", globals_=globals_,
                                                        funcs=[{"name": "f0", "params": [], "err": False, "body": [],
                                                                "ret": LIT("u32", 0)}])), body)

    def test_wide_evaluator_semantics(self):
        W = lambda body, ret=("lit", "u32", 0): _program(body, ret=ret, profile="wide")  # noqa: E731
        ones = [LIT("u32", n) for n in (10, 20, 30, 40)]
        # Element pointers and slices alias the array; indexes wrap modulo the length.
        body = [["let_array", "ar1", ones], ["ptr_elem", "q2", "ar1", LIT("u32", 5)],
                ["store", "q2", "+%=", LIT("u32", 1)],
                ["let_slice", "sl3", "ar1", 1, 3], ["sstore", "sl3", LIT("u32", 3), "=", LIT("u32", 99)]]
        program = W(body, ret=("bin", "+%", ["index", "ar1", LIT("u32", 1)],
                              ["bin", "*%", ["index", "ar1", LIT("u32", 2)], LIT("u32", 1000)]))
        self.assertTrue(zig_gen.typecheck(program))
        # ar1 = 10, 21, 30, 40; sl3 = [21, 30], index 3 % 2 = 1 -> ar1[2] = 99.
        self.assertEqual(zig_gen.evaluate(program)[0], 21 + 99 * 1000)
        # A for loop over a slice reads each element when its iteration starts.
        body = [["let_array", "ar1", ones], ["let_slice", "sl2", "ar1", 0, 3], ["let", "x3", "u32", LIT("u32", 0)],
                ["for_slice", "sl2", "e4", [["set", "x3", "+%=", ["var", "e4"]],
                                            ["arr_set", "ar1", LIT("u32", 2), "=", LIT("u32", 1)]]]]
        self.assertEqual(zig_gen.evaluate(W(body, ret=("var", "x3")))[0], 10 + 20 + 1)
        # Optionals: orelse, a capturing if and a reset to null; the condition decides before the value runs.
        body = [["let_opt", "op1", LIT("bool", False), LIT("u32", 5)], ["let", "x2", "u32", ["orelse", "op1", LIT("u32", 7)]],
                ["set_opt", "op1", LIT("bool", True), LIT("u32", 9)],
                ["if_opt", "op1", "o3", [["set", "x2", "+%=", ["var", "o3"]]], [["set", "x2", "=", LIT("u32", 0)]]]]
        self.assertEqual(zig_gen.evaluate(W(body, ret=("var", "x2")))[0], 7 + 9)
        # Structs copy by value; field pointers and the pointer-taking helper alias the original.
        body = [["let_struct", "st1", LIT("u32", 1), LIT("i32", -1)], ["copy_struct", "st2", "st1"],
                ["ptr_field", "q3", "st1", "x"], ["store", "q3", "=", LIT("u32", 50)],
                ["bump_struct", "st1", LIT("u32", 4294967295)], ["set_field", "st2", "y", "+%=", LIT("i32", 3)]]
        program = W(body, ret=("bin", "+%", ["bin", "*%", ["field", "st1", "x"], LIT("u32", 1000)],
                              ["cast", "i2u", ["bin", "+%", ["field", "st1", "y"], ["field", "st2", "y"]]]))
        self.assertTrue(zig_gen.typecheck(program))
        # st1.x = 50 + (2^32 - 1) = 49; st1.y = -1 + (-1) = -2; st2.y = 2; sum 0.
        self.assertEqual(zig_gen.evaluate(program)[0], (49 * 1000) & 0xFFFFFFFF)
        # Wide integers wrap at their own width; casts truncate or reinterpret.
        body = [["let", "x1", "u64", ["bin", "+%", LIT("u64", 18446744073709551615), LIT("u64", 2)]],
                ["let", "x2", "i64", ["cast", "u2l", ["bin", "-%", LIT("u64", 0), LIT("u64", 1)]]],
                ["let", "x3", "u16", ["cast", "trunc16", LIT("u32", 70000)]]]
        ret = ("bin", "+%", ["bin", "+%", ["cast", "trunc64", ["var", "x1"]], ["cast", "i2u", ["cast", "l2i", ["var", "x2"]]]],
               ["cast", "widen16", ["var", "x3"]])
        self.assertEqual(zig_gen.evaluate(W(body, ret=ret))[0], (1 + 0xFFFFFFFF + (70000 & 0xFFFF)) & 0xFFFFFFFF)

    def test_wide_renderer_follows_zig_local_rules(self):
        body = [["let_array", "ar1", [LIT("u32", n) for n in (1, 2, 3, 4)]], ["let_array", "ar2", [LIT("u32", 0)] * 4],
                ["let_slice", "sl3", "ar2", 1, 3], ["for_slice", "sl3", "e4", []],
                ["let_opt", "op5", LIT("bool", True), LIT("u32", 1)], ["if_opt", "op5", "o6", [], []],
                ["let_struct", "st7", LIT("u32", 1), LIT("i32", 1)], ["ptr_field", "q8", "st7", "y"]]
        source = zig_gen.render(_program(body, profile="wide"))
        self.assertIn("const ar1: [4]u32", source)   # never mutated
        self.assertIn("var ar2: [4]u32", source)     # a slice may write it
        self.assertIn("const sl3: []u32 = ar2[1..3];", source)
        self.assertIn("for (sl3) |_| {", source)     # unused capture
        self.assertIn("const op5: ?u32 = if (true) @as(u32, 1) else null;", source)
        self.assertIn("if (op5) |_| {", source)
        self.assertIn("var st7: P", source)
        self.assertIn("_ = q8;", source)
        self.assertIn("const P = struct { x: u32, y: i32 };", source)
        self.assertIn("fn bumpP(", source)
        self.assertIn("_ = ar1;", source)

    def test_wide_shrinker_is_minimal_for_synthetic_oracle(self):
        def has_slice_loop(program):
            return '"for_slice"' in json.dumps(program)

        seeds = [s for s in range(600) if has_slice_loop(zig_gen.generate(s, "wide"))][:3]
        self.assertTrue(seeds)
        for seed in seeds:
            reduced = zig_gen.shrink(zig_gen.generate(seed, "wide"), has_slice_loop)
            self.assertTrue(zig_gen.typecheck(reduced))
            self.assertEqual(reduced["profile"], "wide")
            # 1-minimal: no well-typed single-step reduction still fails.
            for candidate in zig_gen.candidates(reduced):
                if zig_gen.typecheck(candidate) and zig_gen.size(candidate) < zig_gen.size(reduced):
                    self.assertFalse(has_slice_loop(candidate))
            # The loop needs a slice, and the slice needs an array: nothing else survives.
            [carrier] = [f for f in reduced["funcs"] if f["body"]]
            self.assertEqual([s[0] for s in carrier["body"]], ["let_array", "let_slice", "for_slice"])
            self.assertEqual(carrier["body"][2][3], [])

    def test_typecheck_rejects_invalid_programs(self):
        ret = ["return", LIT("u32", 1)]
        bad = [
            [ret, ["let", "x1", "u32", LIT("u32", 0)]],                     # unreachable code
            [["if", LIT("bool", True), [ret, ["let", "x1", "u32", LIT("u32", 0)]], []]],  # unreachable code in a nested block
            [["break"]],                                                     # break outside a loop
            [["set", "x1", "=", LIT("u32", 0)]],                             # unbound
            [["let", "p0", "u32", LIT("u32", 0)]],                           # shadows a parameter
            [["set", "p0", "=", LIT("u32", 0)]],                             # parameters are immutable
            [["errdefer", []]],                                              # errdefer in a non-error fn
            [["if", LIT("bool", True), [ret], [ret]]],                       # unreachable final return
            [["while", "i1", 9, []]],                                        # unbounded loop
            [["let", "x1", "u8", LIT("u8", 256)]],                           # literal out of range
            [["defer", [["return", LIT("u32", 0)]]]],                        # return inside defer
        ]
        for body in bad:
            self.assertFalse(zig_gen.typecheck(_program(body)), body)
        self.assertTrue(zig_gen.typecheck(_program([["if", LIT("bool", True), [ret], []]])))

    def test_evaluator_semantics(self):
        globals_ = [{"name": "g0", "ty": "u32", "init": 5}]
        # The return value is computed before the defer increments the global.
        body = [["defer", [["set", "g0", "+%=", LIT("u32", 10)]]]]
        program = _program(body, ret=("var", "g0"), globals_=globals_)
        self.assertTrue(zig_gen.typecheck(program))
        self.assertEqual(zig_gen.evaluate(program)[0], 5 ^ 15)
        # errdefer runs only on an error return; catch supplies the fallback.
        fail = {"name": "f0", "params": [["p0", "u32"]], "err": True,
                "body": [["errdefer", [["set", "g0", "+%=", LIT("u32", 1)]]],
                         ["if", ["cmp", "==", ["var", "p0"], LIT("u32", 0)], [["fail"]], []]],
                "ret": ["lit", "u32", 7]}
        program = _program([], ret=("bin", "+%", ["catch", "f0", [["var", "p0"]], LIT("u32", 100)],
                                    ["var", "g0"]), funcs=[fail], globals_=globals_)
        self.assertTrue(zig_gen.typecheck(program))
        # p0 == 0: error -> errdefer bumps g0 to 6; 100 + 6, then ^ g0.
        self.assertEqual(zig_gen.evaluate(program)[0], (100 + 6) ^ 6)
        self.assertEqual(zig_gen.evaluate(program)[1], (7 + 5) ^ 5)
        # swap(&x, &x) aliases; bump through a pointer alias; wrapping casts.
        body = [["let", "x1", "u32", LIT("u32", 4294967295)], ["ptr", "q2", "x1"],
                ["helper", "swap", [["addr", "x1"], ["pvar", "q2"]]],
                ["helper", "bump", [["pvar", "q2"], LIT("u32", 2)]],
                ["let", "x3", "i32", ["cast", "u2i", ["var", "x1"]]]]
        program = _program(body, ret=("cast", "i2u", ["bin", "*%", ["var", "x3"], LIT("i32", -1)]))
        self.assertTrue(zig_gen.typecheck(program))
        self.assertEqual(zig_gen.evaluate(program)[0], 4294967295)
        # A compound assignment loads its target before evaluating its operand.
        bump = {"name": "f0", "params": [], "err": False,
                "body": [["set", "g0", "=", LIT("u32", 100)]], "ret": ["lit", "u32", 1]}
        program = _program([["set", "g0", "+%=", ["call", "f0", []]]], ret=("lit", "u32", 0),
                           funcs=[bump], globals_=globals_)
        self.assertEqual(zig_gen.evaluate(program)[0], 6)

    def test_renderer_follows_zig_local_rules(self):
        body = [["let", "x1", "u32", LIT("u32", 1)], ["let", "x2", "u32", LIT("u32", 2)],
                ["let", "x3", "u32", LIT("u32", 3)], ["set", "x2", "+%=", ["var", "x3"]],
                ["ptr", "q4", "x1"]]
        source = zig_gen.render(_program(body))
        self.assertIn("var x1: u32", source)    # address taken
        self.assertIn("var x2: u32", source)    # assigned
        self.assertIn("const x3: u32", source)  # only read
        self.assertIn("_ = q4;", source)        # unused
        self.assertIn("_ = p0;", source)
        self.assertNotIn("_ = x3;", source)

    def test_shrinker_is_minimal_for_synthetic_oracle(self):
        def has_cast_in_loop(program):
            def walk(node, in_loop):
                if isinstance(node, list) and node[:1] == ["cast"] and node[1] == "u2i" and in_loop:
                    return True
                if isinstance(node, list) and node[:1] == ["while"]:
                    return walk(node[3], True)
                children = node.values() if isinstance(node, dict) else node if isinstance(node, list) else []
                return any(walk(c, in_loop) for c in children)
            return any(walk(f["body"], False) for f in program["funcs"])

        seeds = [s for s in range(400) if has_cast_in_loop(zig_gen.generate(s))][:3]
        self.assertTrue(seeds)
        for seed in seeds:
            reduced = zig_gen.shrink(zig_gen.generate(seed), has_cast_in_loop)
            self.assertTrue(zig_gen.typecheck(reduced))
            self.assertTrue(has_cast_in_loop(reduced))
            # 1-minimal: no well-typed single-step reduction still fails.
            for candidate in zig_gen.candidates(reduced):
                if zig_gen.typecheck(candidate) and zig_gen.size(candidate) < zig_gen.size(reduced):
                    self.assertFalse(has_cast_in_loop(candidate))
            # A global assignment can be the shortest carrier of the cast.
            self.assertLessEqual(len(reduced["globals"]), 1)
            self.assertLess(zig_gen.size(reduced)[0], 300)
            self.assertEqual([f["name"] for f in reduced["funcs"]], ["work"])
            work = reduced["funcs"][0]
            self.assertIn(work["ret"][0], ("lit", "var"))
            [loop] = work["body"]
            self.assertEqual(loop[0], "while")
            self.assertEqual(loop[2], 1)
            [statement] = loop[3]
            # The cast's operand is a leaf (a literal, or a shorter variable reference).
            casts = [e for e in _subexpressions(statement) if e[:2] == ["cast", "u2i"]]
            self.assertEqual(len(casts), 1)
            self.assertIn(casts[0][2][0], ("lit", "var"))

    # --- ext profile -----------------------------------------------------------------------

    def test_ext_profile_is_deterministic_well_typed_and_covers_its_features(self):
        seen, kinds = set(), set()
        for seed in range(300):
            program = zig_gen.generate(seed, "ext")
            self.assertEqual(program["profile"], "ext")
            self.assertIsNone(zig_gen.typecheck_error(program), seed)
            self.assertEqual(program, zig_gen.generate(seed, "ext"))
            seen |= zig_gen.features(program)
            if seed < 40:
                self.assertEqual(zig_gen.render(program), zig_gen.render(json.loads(json.dumps(program))))
            if seed < 100:
                kinds |= {outcome.get("panic", "ok") for outcome in zig_gen.evaluate(program)}
        self.assertEqual(seen, set(zig_gen.EXT_FEATURES))
        # Every safety check of the families is reached, and so are inputs without illegal behaviour.
        self.assertEqual(kinds, {"ok", "divideByZero", "exactDivisionRemainder", "integerOverflow", "shiftRhsTooBig",
                                 "shlOverflow", "integerOutOfBounds", "integerPartOutOfBounds", "outOfBounds",
                                 "unwrapNull", "unwrapError", "reachedUnreachable"})
        self.assertLessEqual(kinds - {"ok"}, set(zig_gen.panic_policy()))

    def test_ext_types_cover_every_width_and_signedness(self):
        seen = set()
        for seed in range(2000):
            seen |= set(zig_gen.Gen(seed, "ext").shape["ints"])
        # u32, i32, u64 and i64 are in every program, so they are not drawn again.
        self.assertEqual({zig_gen.bits(t) for t in seen} | {32, 64}, set(range(1, 129)))
        self.assertEqual({t[0] for t in seen}, {"u", "i"})
        self.assertEqual([zig_gen.shift_type(t) for t in ("u1", "i7", "u8", "u9", "i128")], ["u0", "u3", "u3", "u4", "u7"])
        self.assertEqual([zig_gen.byte_size(t) for t in ("u1", "u8", "i9", "u24", "i33", "u65", "i128")],
                         [1, 1, 2, 4, 8, 16, 16])

    def test_ext_constructs_are_rejected_outside_the_ext_profile(self):
        div = ["let", "x1", "u32", ["div", "/", "u32", LIT("u32", 1), ["var", "p0"], False]]
        self.assertTrue(zig_gen.typecheck(_ext([div])))
        self.assertFalse(zig_gen.typecheck(_program([div], profile="wide")))
        self.assertFalse(zig_gen.typecheck(_program([div])))
        self.assertFalse(zig_gen.typecheck(_program([["let", "x1", "u7", LIT("u7", 1)]], profile="wide")))
        self.assertFalse(zig_gen.typecheck(_program([["unreach_if", LIT("bool", False)]], profile="wide")))
        # A program's own types belong to the ext profile only, and an ext program must have them.
        self.assertFalse(zig_gen.typecheck({**_program([], profile="wide"), "types": EXT_TYPES}))
        self.assertFalse(zig_gen.typecheck(_program([], profile="ext")))

    def test_typecheck_rejects_invalid_ext_programs(self):
        fallible = {"name": "f0", "params": [], "err": True, "body": [], "ret": LIT("u32", 0)}
        heap = lambda body, mode="defer": ["with_alloc", "hp1", 2, LIT("i7", 1), mode, 0, body]  # noqa: E731
        bad = [
            [["let", "x1", "i7", ["div", "/", "i7", LIT("i7", 1), LIT("i7", 1), True]]],        # no `/` for signed
            [["let", "x1", "u9", ["shift", "shrExact", "u9", LIT("u9", 1), LIT("u32", 1), False]]],  # unchecked IB
            [["let", "x1", "u9", ["shift", "<<", "u9", LIT("u9", 1), LIT("u9", 1), True]]],     # the count is a u32
            [["let", "x1", "u32", ["try", "f0", []]]],                                          # work returns no error
            [["let", "x1", "u9", ["conv", "widen", "i7", "u9", LIT("i7", 1)]]],                 # i7 does not fit u9
            [["let", "x1", "u9", ["conv", "trunc", "u32", "i7", LIT("u32", 1)]]],               # result type
            [["let", "x1", "i7", ["conv", "trunc", "u32", "i7", LIT("u32", 1)]]],               # @truncate keeps the sign
            [["let", "x1", "u9", ["neg", "u9", LIT("u9", 1)]]],                                 # no unsigned negation
            [["let", "x1", "f64", LIT("f64", 0)]],                                              # not one of its floats
            [["let", "x1", "f32", LIT("f32", 0x7FC00000)]],                                     # a NaN literal
            [["let", "x1", "f32", LIT("f32", 0)], ["set", "x1", "+%=", LIT("f32", 0)]],         # no wrapping floats
            [["let", "x1", "u32", ["fbits", "f16", LIT("f16", 0)]]],                            # f16 has 16 bits
            [["let", "x1", "u9", ["gscale", "u9", 512, LIT("u9", 1)]]],                         # 512 is no u9
            [["let", "x1", "u9", ["grep", "u9", 4, LIT("u9", 1)]]],                             # at most 3 rounds
            [["defer", [heap([])]]],                                                            # allocation in a defer
            [heap([["return", LIT("u32", 1)]]), ["let", "x2", "u32", LIT("u32", 0)]],           # unreachable code
            [heap([]), ["sstore", "hp1", LIT("u32", 0), "=", LIT("i7", 1)]],                    # out of its scope
            [["with_alloc", "hp1", 9, LIT("i7", 1), "defer", 0, []]],                           # length
            [["with_alloc", "hp1", 2, LIT("i7", 1), "later", 0, []]],                           # free mode
            [["let", "x1", "i7", ["uindex", "nope", LIT("u32", 0)]]],                           # unbound
        ]
        for body in bad:
            self.assertFalse(zig_gen.typecheck(_ext(body, funcs=[fallible])), body)
        # `try` belongs to an error function, outside its defers.
        inner = lambda body: _ext([], funcs=[fallible, {"name": "f1", "params": [], "err": True, "body": body,  # noqa: E731
                                                       "ret": LIT("u32", 0)}])
        self.assertTrue(zig_gen.typecheck(inner([["let", "x1", "u32", ["try", "f0", []]]])))
        self.assertFalse(zig_gen.typecheck(inner([["defer", [["let", "x1", "u32", ["try", "f0", []]]]]])))

    def test_ext_integer_semantics(self):
        def run(expr, ty="i7"):
            program = _ext([["let", "x1", ty, expr]], ret=("lit", "u32", 5))
            self.assertIsNone(zig_gen.typecheck_error(program), expr)
            return zig_gen.evaluate(program)[0]

        def value(expr, ty="i7"):
            program = _ext([], ret=("conv", "bitcast", "i32", "u32", ["conv", "widen", ty, "i32", expr]))
            self.assertIsNone(zig_gen.typecheck_error(program), expr)
            return zig_gen.wrap("i32", zig_gen.evaluate(program)[0]["ok"])

        div = lambda op, a, b, guarded=False, ty="i7": ["div", op, ty, LIT(ty, a), LIT(ty, b), guarded]  # noqa: E731
        # Division by zero, minInt / -1 and an inexact @divExact: a panic, or the dividend when guarded.
        for op in ("divTrunc", "divFloor", "divExact", "rem", "mod"):
            self.assertEqual(run(div(op, 5, 0)), {"panic": "divideByZero"})
            self.assertEqual(value(div(op, 5, 0, True)), 5)
        for op in ("divTrunc", "divFloor", "divExact"):
            self.assertEqual(run(div(op, -64, -1)), {"panic": "integerOverflow"})
            self.assertEqual(value(div(op, -64, -1, True)), -64)
        self.assertEqual(run(div("divExact", 7, 2)), {"panic": "exactDivisionRemainder"})
        self.assertEqual(value(div("divExact", 7, 2, True)), 7)
        self.assertEqual(run(div("/", 5, 0, ty="u9"), "u9"), {"panic": "divideByZero"})
        # Rounding: truncation, floor; @rem takes the dividend's sign, @mod the divisor's; by -1 they are 0.
        self.assertEqual([value(div(op, -7, 2)) for op in ("divTrunc", "divFloor", "rem", "mod")], [-3, -4, -1, 1])
        self.assertEqual([value(div(op, 7, -2)) for op in ("divTrunc", "divFloor", "rem", "mod")], [-3, -4, 1, -1])
        self.assertEqual([value(div(op, -64, -1)) for op in ("rem", "mod")], [0, 0])
        self.assertEqual(value(div("divExact", -6, 3)), -2)
        # Shifts: the count is truncated to Log2Int (u3 for i7), so 7 is too big and 8 is 0; a guard reduces it.
        shift = lambda op, a, n, guarded=False, ty="i7": ["shift", op, ty, LIT(ty, a), LIT("u32", n), guarded]  # noqa: E731
        self.assertEqual(run(shift("<<", 1, 7)), {"panic": "shiftRhsTooBig"})
        self.assertEqual(value(shift("<<", 1, 8)), 1)
        self.assertEqual(value(shift("<<", 1, 7, True)), 1)
        self.assertEqual(value(shift("<<", 1, 6)), -64)             # `<<` discards bits without a check
        self.assertEqual(value(shift(">>", -64, 2)), -16)           # arithmetic for a signed operand
        self.assertEqual(run(shift("shlExact", 1, 6)), {"panic": "shlOverflow"})
        self.assertEqual(value(shift("shlExact", -1, 6)), -64)
        self.assertEqual(value(shift("shlExact", 3, 6, True)), 3)
        self.assertEqual(value(shift("shrExact", 7, 1, True)), 3)
        self.assertEqual(value(shift("<<", 1, 5, ty="u1"), "u1"), 1)  # a u0 count is always 0
        # Checked arithmetic, negation and @intCast.
        self.assertEqual(run(["arith", "+", "i7", LIT("i7", 63), LIT("i7", 1)]), {"panic": "integerOverflow"})
        self.assertEqual(value(["arith", "*", "i7", LIT("i7", -8), LIT("i7", 8)]), -64)
        self.assertEqual(run(["neg", "i7", LIT("i7", -64)]), {"panic": "integerOverflow"})
        self.assertEqual(run(["conv", "intcast", "u32", "i7", LIT("u32", 64)]), {"panic": "integerOutOfBounds"})
        self.assertEqual(value(["conv", "intcast", "u32", "i7", LIT("u32", 63)]), 63)
        self.assertEqual(value(["conv", "bitcast", "u7", "i7", LIT("u7", 127)]), -1)
        self.assertEqual(value(["conv", "trunc", "i33", "i7", LIT("i33", 65)]), -63)
        # Generic functions are instantiated at the operand type.
        self.assertEqual(value(["gcall", "gmix", "i7", [LIT("i7", 9), LIT("i7", 9)]]), zig_gen.wrap("i7", 90))
        self.assertEqual(value(["gcall", "gsel", "i7", [LIT("bool", False), LIT("i7", 1), LIT("i7", 2)]]), 2)
        self.assertEqual(value(["gpair", "i7", "second", LIT("i7", 1), LIT("i7", 2)]), 2)
        self.assertEqual(value(["grep", "i7", 2, LIT("i7", 3)]), zig_gen.wrap("i7", (3 * 3 + 3) * 3 + 3))
        self.assertEqual(value(["gscale", "i7", 5, LIT("i7", 30)]), zig_gen.wrap("i7", 150))

    def test_ext_aggregate_and_error_semantics(self):
        fallible = {"name": "f0", "params": [["p2", "u32"]], "err": True,
                    "body": [["if", ["cmp", "==", ["var", "p2"], LIT("u32", 0)], [["fail"]], []]], "ret": ["var", "p2"]}
        array = ["let_array", "ar1", [LIT("i7", n) for n in (1, 2, 3)]]
        run = lambda body, ret: zig_gen.evaluate(_ext(body, ret=ret, funcs=[fallible]))  # noqa: E731
        widen = lambda e: ("conv", "intcast", "i7", "u32", e)  # noqa: E731
        # An unguarded index panics past the length; the first two inputs are p0 = 0 and 1.
        outcomes = run([array], widen(["uindex", "ar1", ["bin", "+%", ["var", "p0"], LIT("u32", 2)]]))
        self.assertEqual(outcomes[:2], [{"ok": 3}, {"panic": "outOfBounds"}])
        outcomes = run([array, ["let_slice", "sl2", "ar1", 1, 3]], widen(["usindex", "sl2", LIT("u32", 2)]))
        self.assertEqual(outcomes[0], {"panic": "outOfBounds"})
        # `.?` of null, `catch unreachable` of an error and a true `unreachable` condition.
        body = [["let_opt", "op1", ["cmp", "!=", ["var", "p0"], LIT("u32", 0)], LIT("u9", 9)]]
        outcomes = run(body, ("conv", "widen", "u9", "u32", ["unwrap", "op1"]))
        self.assertEqual(outcomes[:2], [{"panic": "unwrapNull"}, {"ok": 9}])
        self.assertEqual(run([], ("cunreach", "f0", [["var", "p0"]]))[:2], [{"panic": "unwrapError"}, {"ok": 1}])
        outcomes = run([["unreach_if", ["cmp", "==", ["var", "p0"], LIT("u32", 1)]]], ("lit", "u32", 4))
        self.assertEqual(outcomes[:2], [{"ok": 4}, {"panic": "reachedUnreachable"}])
        # `try` returns the callee's error: the caller's errdefer runs, and its own caller catches it.
        globals_ = [{"name": "g0", "ty": "u32", "init": 0}]
        caller = {"name": "f1", "params": [["p3", "u32"]], "err": True,
                  "body": [["errdefer", [["set", "g0", "=", LIT("u32", 100)]]]], "ret": ["try", "f0", [["var", "p3"]]]}
        program = _ext([], ret=("catch", "f1", [["var", "p0"]], LIT("u32", 7)), funcs=[fallible, caller], globals_=globals_)
        self.assertIsNone(zig_gen.typecheck_error(program))
        self.assertEqual(zig_gen.evaluate(program)[:2], [{"ok": 7 ^ 100}, {"ok": 1}])

    def test_ext_float_semantics(self):
        f32 = lambda x: struct.unpack("<I", struct.pack("<f", x))[0]  # noqa: E731
        f64 = lambda x: struct.unpack("<Q", struct.pack("<d", x))[0]  # noqa: E731
        types = {**EXT_TYPES, "floats": ["f32", "f64"]}
        bits = lambda fmt, e: zig_gen.evaluate(_ext([], ret=("conv", "trunc", f"u{softfloat.width(fmt)}", "u32",  # noqa: E731
                                                              ["fbits", fmt, e]), types=types))[0]
        # One rounding of the exact result: 0.1 + 0.2 in f64, and the same sum in f32.
        self.assertEqual(bits("f64", ["fbin", "+", LIT("f64", f64(0.1)), LIT("f64", f64(0.2))])["ok"],
                         f64(0.1 + 0.2) & 0xFFFFFFFF)
        self.assertEqual(bits("f32", ["fbin", "+", LIT("f32", f32(0.1)), LIT("f32", f32(0.2))])["ok"],
                         f32(struct.unpack("<f", struct.pack("<f", 0.1))[0] + struct.unpack("<f", struct.pack("<f", 0.2))[0]))
        self.assertEqual(bits("f32", ["fun", "sqrt", LIT("f32", f32(2.0))])["ok"], f32(math.sqrt(2.0)))
        self.assertEqual(bits("f32", ["fconv", "f64", "f32", LIT("f64", f64(1e300))])["ok"], softfloat.inf("f32"))
        self.assertEqual(bits("f32", ["i2f", "u32", "f32", LIT("u32", 16777217)])["ok"], f32(16777216.0))  # ties to even
        self.assertEqual(bits("f32", ["fun", "neg", LIT("f32", 0)])["ok"], 0x80000000)                  # -0.0
        # A NaN is only ever seen as the canonical quiet NaN, and the input is marked.
        nan = bits("f32", ["fbin", "/", LIT("f32", 0), LIT("f32", 0)])
        self.assertEqual(nan, {"ok": softfloat.qnan("f32"), "nan": True})
        # @intFromFloat truncates; outside the type it panics (0 when guarded); a NaN is always 0.
        to_int = lambda x, guarded=False: zig_gen.evaluate(_ext(  # noqa: E731
            [], ret=("conv", "bitcast", "i32", "u32", ["conv", "widen", "i7", "i32", ["f2i", "f32", "i7", x, guarded]]),
            types=types))[0]
        self.assertEqual(to_int(LIT("f32", f32(-64.9))), {"ok": zig_gen.wrap("u32", -64)})
        self.assertEqual(to_int(LIT("f32", f32(64.0))), {"panic": "integerPartOutOfBounds"})
        self.assertEqual(to_int(LIT("f32", f32(64.0)), True), {"ok": 0})
        self.assertEqual(to_int(LIT("f32", softfloat.inf("f32", 1))), {"panic": "integerPartOutOfBounds"})
        self.assertEqual(to_int(["fun", "sqrt", LIT("f32", f32(-1.0))]), {"ok": 0, "nan": True})
        # Comparisons are IEEE: a NaN is unordered and -0 equals +0.
        cmp = lambda op, a, b: zig_gen.evaluate(_ext(  # noqa: E731
            [["let", "x1", "bool", ["cmp", op, a, b]]],
            ret=("gcall", "gsel", "u32", [["var", "x1"], LIT("u32", 1), LIT("u32", 0)]), types=types))[0]["ok"]
        quiet = ["fbin", "/", LIT("f32", 0), LIT("f32", 0)]
        self.assertEqual([cmp(op, quiet, quiet) for op in ("<", "==", "!=", ">=")], [0, 0, 1, 0])
        self.assertEqual(cmp("==", LIT("f32", 0), LIT("f32", 0x80000000)), 1)

    def test_softfloat_rounds_like_the_host(self):
        rng = random.Random(7)
        for fmt, code, word in (("f64", "<d", "<Q"), ("f32", "<f", "<I"), ("f16", "<e", "<H")):
            exp_bits, frac_bits = softfloat.FORMATS[fmt]
            to_float = lambda b: struct.unpack(code, struct.pack(word, b))[0]  # noqa: E731

            def to_bits(x):
                try:
                    return struct.unpack(word, struct.pack(code, x))[0]
                except OverflowError:  # struct refuses to round a finite double to an infinity
                    return softfloat.inf(fmt, x < 0)
            for _ in range(3000):
                bias = (1 << (exp_bits - 1)) - 1
                a, b = ((rng.getrandbits(1) << (exp_bits + frac_bits)) | ((bias + rng.randint(-9, 9)) << frac_bits)
                        | rng.getrandbits(frac_bits) for _ in range(2))
                x, y = to_float(a), to_float(b)
                # The host computes in f64: one more rounding to a narrower format is exact for these.
                self.assertEqual(softfloat.add(fmt, a, b), to_bits(x + y))
                self.assertEqual(softfloat.sub(fmt, a, b), to_bits(x - y))
                self.assertEqual(softfloat.mul(fmt, a, b), to_bits(x * y))
                self.assertEqual(softfloat.div(fmt, a, b), to_bits(x / y))
                self.assertEqual(softfloat.sqrt(fmt, softfloat.fabs(fmt, a)), to_bits(math.sqrt(abs(x))))
                self.assertEqual(softfloat.to_int(fmt, a), int(x))
                self.assertEqual(softfloat.compare(fmt, "<", a, b), x < y)
                self.assertEqual(softfloat.convert(fmt, "f16", a), softfloat.convert("f64", "f16", softfloat.convert(fmt, "f64", a)))
        # Specials: signed zeros, infinities and the invalid operations.
        one, zero, minus_zero, inf = softfloat.from_int("f32", 1), 0, 0x80000000, softfloat.inf("f32")
        self.assertEqual(softfloat.add("f32", minus_zero, minus_zero), minus_zero)
        self.assertEqual(softfloat.add("f32", minus_zero, zero), zero)
        self.assertEqual(softfloat.sub("f32", one, one), zero)
        self.assertEqual(softfloat.div("f32", one, minus_zero), softfloat.inf("f32", 1))
        self.assertEqual(softfloat.sqrt("f32", minus_zero), minus_zero)
        self.assertEqual(softfloat.ceil("f32", softfloat.neg("f32", softfloat.power_of_two("f32", -1))), minus_zero)
        self.assertEqual(softfloat.round_("f32", softfloat.power_of_two("f32", -1)), one)   # ties away from zero
        for invalid in (softfloat.sub("f32", inf, inf), softfloat.mul("f32", inf, zero), softfloat.div("f32", zero, zero),
                        softfloat.sqrt("f32", softfloat.neg("f32", one))):
            self.assertEqual(invalid, softfloat.qnan("f32"))
        self.assertEqual(softfloat.encode("f32", 0, softfloat.decode("f32", 1)[2] / 2), 0)  # half the least subnormal

    def test_ext_allocation_follows_the_fixed_buffer_allocator(self):
        heap = lambda name, count, mode, body, fail=77: ["with_alloc", name, count, LIT("i7", 1), mode, fail, body]  # noqa: E731
        types = {**EXT_TYPES, "elem": "u64"}
        heap64 = lambda name, count, mode, body, fail=77: ["with_alloc", name, count, LIT("u64", 1), mode, fail, body]  # noqa: E731
        run = lambda body, ret=("lit", "u32", 0), types=EXT_TYPES: zig_gen.evaluate(_ext(body, ret=ret, types=types))[0]  # noqa: E731
        # 64 bytes: eight u64 fit, nine do not (two allocations).
        self.assertEqual(run([heap64("hp1", 8, "defer", [])], types=types), {"ok": 0})
        self.assertEqual(run([heap64("hp1", 5, "leak", []), heap64("hp2", 4, "defer", [])], types=types), {"ok": 77})
        # A freed last allocation gives its bytes back; a leak, or a free that is not the last one, does not.
        self.assertEqual(run([heap64("hp1", 5, "end", []), heap64("hp2", 5, "defer", [])], types=types), {"ok": 0})
        self.assertEqual(run([heap64("hp1", 5, "defer", []), heap64("hp2", 5, "defer", [])], types=types), {"ok": 0})
        inner_leak = [heap64("hp1", 3, "end", [heap64("hp2", 2, "leak", [])]), heap64("hp3", 4, "defer", [])]
        self.assertEqual(run(inner_leak, types=types), {"ok": 77})
        # Alignment: one i7 byte, then a u64 at offset 8.
        mixed = [heap("hp1", 1, "leak", []), ["with_create", "hq2", "u64", LIT("u64", 3), "leak", 5, []],
                 heap("hp3", 5, "leak", []), ["with_create", "hq4", "u64", LIT("u64", 3), "leak", 6,
                                              [["with_create", "hq5", "u64", LIT("u64", 3), "leak", 8, []]]]]
        machine = zig_gen.Machine(_ext(mixed))
        self.assertEqual([machine.fba_alloc(1, 1), machine.fba_alloc(8, 8), machine.fba_alloc(5, 1), machine.fba_alloc(8, 8)],
                         [0, 8, 16, 24])
        # The slice is initialized, writable and read through for loops; a `defer` free runs on return.
        body = [heap("hp1", 3, "defer", [["sstore", "hp1", LIT("u32", 4), "+%=", LIT("i7", 5)],
                                         ["for_slice", "hp1", "e2", [["set", "x0", "+%=", ["var", "e2"]]]],
                                         ["if", ["cmp", "==", ["var", "p0"], LIT("u32", 1)], [["return", LIT("u32", 9)]], []]]),
                heap("hp3", 5, "defer", [])]
        program = _ext([["let", "x0", "i7", LIT("i7", 0)]] + body, ret=("conv", "intcast", "i7", "u32", ["var", "x0"]))
        self.assertIsNone(zig_gen.typecheck_error(program))
        self.assertEqual(zig_gen.evaluate(program)[:2], [{"ok": 8}, {"ok": 9}])

    def test_ext_renderer_and_case_files(self):
        body = [["let", "x1", "i7", ["div", "divTrunc", "i7", ["conv", "intcast", "u32", "i7", ["var", "p0"]], LIT("i7", 0), True]],
                ["let", "x2", "f32", ["i2f", "i7", "f32", ["var", "x1"]]],
                ["let", "x3", "u32", ["f2i", "f32", "u32", ["var", "x2"], True]],
                ["with_alloc", "hp4", 2, ["var", "x1"], "end", 7,
                 [["if", ["cmp", "==", ["var", "p0"], LIT("u32", 1)], [["return", ["var", "x3"]]], []]]]]
        program = _ext(body)
        self.assertIsNone(zig_gen.typecheck_error(program))
        source = zig_gen.render(program)
        # Operands of an operation with illegal behaviour are runtime values, whatever they are in the source.
        self.assertIn("var tb2: i7 = @as(i7, 0); _ = &tb2;", source)
        self.assertIn("if (tb2 == 0 or (ta2 == -64 and tb2 == -1)) ta2 else @divTrunc(ta2, tb2)", source)
        self.assertIn("if (ta3 != ta3 or !(@trunc(ta3) >= ", source)
        self.assertIn("var fuzz_fba: std.heap.FixedBufferAllocator", source)
        self.assertIn("const hp4 = fuzz_fba.allocator().alloc(i7, 2) catch return @as(u32, 7);", source)
        # The buffer's alignment is its type's, and `entry` gives the allocator its bytes at run time.
        self.assertIn("var fuzz_buf: [4]u128 = undefined;", source)
        self.assertIn("fuzz_fba = .{ .end_index = 0, .buffer = @as([*]u8, @ptrCast(fuzz_base))[0..64] };", source)
        self.assertNotIn("align(", source)
        self.assertIn("        fuzz_fba.allocator().free(hp4);\n    }\n    return @as(u32, 0);", source)
        self.assertNotIn('test "', source)                # the harness, not a test, runs an ext program
        self.assertIn("fn GPair(comptime T: type) type", source)
        self.assertIn("const P = struct { x: i7, y: u9 };", source)
        with tempfile.TemporaryDirectory() as tmp:
            zig_gen.write_case(program, tmp)
            case = json.loads((Path(tmp) / "expected.json").read_text())
            driver = (Path(tmp) / "driver.zig").read_text()
        self.assertEqual(case["inputs"], [list(pair) for pair in zig_gen.EXT_INPUTS])
        self.assertEqual(case["translate_args"][-2:], ["--allocator-model", "translated"])
        self.assertIn("--closure", case["translate_args"])
        self.assertIn('const fuzz = @import("fuzz_e0.zig");', driver)
        for member in zig_gen.panic_policy():
            if member not in ("doubleFree", "panic", "SIGFPE"):   # not `std.builtin.panic` members
                self.assertIn(f"pub fn {member}(", driver)
        # A program without an allocation needs no allocator code and no translated allocator.
        plain = _ext(body[:3])
        self.assertNotIn("fuzz_fba", zig_gen.render(plain))
        with tempfile.TemporaryDirectory() as tmp:
            zig_gen.write_case(plain, tmp)
            self.assertEqual(json.loads((Path(tmp) / "expected.json").read_text())["translate_args"], [])

    def test_ext_outcomes_are_compared_by_kind(self):
        expected = [{"ok": 5}, {"panic": "divideByZero"}, {"panic": "shiftRhsTooBig"}, {"ok": 1, "nan": True}]
        native = "noise\nFUZZ 0 ok 5\nFUZZ 1 panic divideByZero\nFUZZ 2 panic shiftRhsTooBig\nFUZZ 3 ok 1\n"
        self.assertEqual(zig_gen.verify(expected, native, "native"), [])
        lean = "FUZZ 0 ok 5\nFUZZ 1 fail Zig.Error.divByZero\nFUZZ 2 fail Zig.Error.overflow\nFUZZ 3 fail Zig.Error.unspecified\n"
        self.assertEqual(zig_gen.verify(expected, lean, "lean"), [])
        # Another value, another check, a value where a panic is due, a missing line: all mismatches.
        wrong = "FUZZ 0 ok 6\nFUZZ 1 fail Zig.Error.overflow\nFUZZ 2 ok 0\n"
        errors = zig_gen.verify(expected, wrong, "lean")
        self.assertEqual(len(errors), 4)
        self.assertIn("input 1: expected fail Zig.Error.divByZero, got fail Zig.Error.overflow", errors[1])
        self.assertIn("no outcome line", errors[3])
        # `.unspecified` stands in only for an input that made a NaN; natively a panic's check must be the same one.
        self.assertEqual(len(zig_gen.verify(expected, lean.replace("ok 5", "fail Zig.Error.unspecified"), "lean")), 1)
        self.assertEqual(len(zig_gen.verify(expected, native.replace("shiftRhsTooBig", "shlOverflow"), "native")), 1)
        text = zig_gen.lean_checks("def entry (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do",
                                   "Fuzze1", expected)
        self.assertIn('#eval IO.println s!"FUZZ 3 {outcome ((Fuzze1.entry 305419896#32 2863311530#32).run\' '
                      '(Fuzze1.mem0 .fresh))}"', text)
        self.assertNotIn("#guard", text)

    def test_ext_shrinker_is_minimal_for_synthetic_oracle(self):
        def panics_on_division(program):
            return any(outcome.get("panic") == "divideByZero" for outcome in zig_gen.evaluate(program))

        seeds = [s for s in range(200) if panics_on_division(zig_gen.generate(s, "ext"))][:3]
        self.assertTrue(seeds)
        for seed in seeds:
            reduced = zig_gen.shrink(zig_gen.generate(seed, "ext"), panics_on_division)
            self.assertTrue(zig_gen.typecheck(reduced))
            self.assertTrue(panics_on_division(reduced))
            for candidate in zig_gen.candidates(reduced):
                if zig_gen.typecheck(candidate) and zig_gen.size(candidate) < zig_gen.size(reduced):
                    self.assertFalse(panics_on_division(candidate))
            # One unguarded division is left, in `work` or in a function on the call path to it.
            self.assertLessEqual(len(reduced["funcs"]), 3)
            divisions = [e for f in reduced["funcs"] for e in _subexpressions([f["body"], f["ret"]]) if e[0] == "div"]
            self.assertEqual([e[5] for e in divisions], [False])
            self.assertLess(zig_gen.size(reduced)[0], 460 if len(reduced["funcs"]) == 1 else 900)
        # Guarding an operation is a reduction step of its own.
        program = _ext([["let", "x1", "i7", ["div", "rem", "i7", LIT("i7", 1), LIT("i7", 0), False]]])
        self.assertIn(True, [c["funcs"][-1]["body"][0][3][5] for c in zig_gen.candidates(program)
                             if c["funcs"][-1]["body"] and c["funcs"][-1]["body"][0][3][0] == "div"])

    def test_lean_checks_follow_the_translated_signature(self):
        pure = "def entry (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do"
        memory = "def entry (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do"
        expected = [1, 2, 3, 4]
        text = zig_gen.lean_checks(pure, "Fuzzs1", expected)
        self.assertIn("#guard successful (Fuzzs1.entry 0#32 0#32) == some 1#32", text)
        text = zig_gen.lean_checks(memory, "Fuzzs1", expected)
        self.assertIn(".run' (Fuzzs1.mem0 .fresh)", text)
        with self.assertRaises(ValueError):
            zig_gen.lean_checks("def other", "Fuzzs1", expected)


def _subexpressions(node):
    out = []
    if isinstance(node, list):
        if node and isinstance(node[0], str) and node[0] in zig_gen.EXPR_TAGS:
            out.append(node)
        for child in node:
            out.extend(_subexpressions(child))
    return out


if __name__ == "__main__":
    unittest.main()
