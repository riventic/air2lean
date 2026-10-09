#!/usr/bin/env python3
"""Offline Q01 regressions: generator determinism, oracles and shrinker minimality.

Synthetic oracles stand in for the translator and compilers; nothing here runs a tool.
"""
import json
from pathlib import Path
import sys
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import air_fuzz  # noqa: E402
import shrink  # noqa: E402
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

    def test_emit_oracle(self):
        header = "-- air2lean-profile: {}\n"
        self.assertIsNone(air_fuzz.classify_emit(0, "", header + "def f := 1\n"))
        self.assertEqual(air_fuzz.classify_emit(0, "", header + '(panic! "air2lean: unbound inst 3")'),
                         "emit:placeholder")
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
            self.assertEqual(case.name, f"seed-{meta['seed']}")
            self.assertIn(meta["expected_exit"], (0, 1))
            self.assertTrue(meta["original_failure"])
            self.assertTrue(list(case.glob("[0-9][0-9].json")))


def _program(body, ret=("lit", "u32", 0), funcs=(), globals_=()):
    work = {"name": "work", "params": [["p0", "u32"], ["p1", "u32"]], "err": False,
            "body": json.loads(json.dumps(body)), "ret": list(ret)}
    return {"seed": 0, "globals": [dict(g) for g in globals_], "funcs": list(funcs) + [work]}


LIT = lambda ty, v: ["lit", ty, v]  # noqa: E731


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

    def test_typecheck_rejects_invalid_programs(self):
        ret = ["return", LIT("u32", 1)]
        bad = [
            [ret, ["let", "x1", "u32", LIT("u32", 0)]],                     # unreachable code
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

    def test_lean_checks_follow_the_translated_signature(self):
        pure = "def entry (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do"
        memory = "def entry (p0 : BitVec 32) (p1 : BitVec 32) : Zig.MemM (BitVec 32) := do"
        expected = [1, 2, 3, 4]
        text = zig_gen.lean_checks(pure, "Fuzzs1", expected)
        self.assertIn("#guard successful (Fuzzs1.entry 0#32 0#32) == some 1#32", text)
        text = zig_gen.lean_checks(memory, "Fuzzs1", expected)
        self.assertIn(".run' Fuzzs1.mem0 .fresh", text)
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
