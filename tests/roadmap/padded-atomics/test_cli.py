#!/usr/bin/env python3
"""Padded-width atomics: actual-CLI regressions over hand-written exporter-schema AIR fixtures.

Zig lowers `@cmpxchgStrong`/`@cmpxchgWeak` and `@atomicRmw` `.Max`/`.Min` on an integer
representation with padding bits (`u24`, `u31`, `i40`, `enum(u24)`, a packed struct backed by
`u40`) to an LLVM op on the whole ABI cell, so the padding bits, which the model leaves
undefined, take part in the comparison. These are rejected with `PADDED_ATOMIC` (phase `check`,
category `unsupported_semantics`); every other atomic op, and every op on a type whose width
fills its ABI size, is unchanged. `--self-test` checks the fixture builders without a translator.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
VERSIONS = ("0.14.1", "0.15.2", "0.16.0")


def int_size(bits):
    nbytes = (bits + 7) // 8
    align = 1 if nbytes <= 1 else 2 if nbytes <= 2 else 4 if nbytes <= 4 else 8 if nbytes <= 8 else 16
    return -(-nbytes // align) * align, align


def int_ty(bits, signed=False):
    size, align = int_size(bits)
    return dict(k="int", signed=signed, bits=bits, abi_size=size, abi_align=align)


VOID = dict(k="void", abi_size=0, abi_align=1)
NORETURN = dict(k="noreturn")
BOOL = dict(k="bool", abi_size=1, abi_align=1)


def operand_types(name):
    """The operand type of fixture `name`, followed by the types it refers to (index 4 on)."""
    kind, _, rest = name.partition("_")
    if kind == "bool":
        return [BOOL]
    if kind == "enum":
        bits = int(rest)
        size, align = int_size(bits)
        return [dict(k="enum", name=f"E{bits}", tag=4, exhaustive=False,
                     fields=[dict(name="a", value="0"), dict(name="b", value="1")],
                     abi_size=size, abi_align=align), int_ty(bits)]
    if kind == "packed":
        half = int(rest) // 2
        size, align = int_size(2 * half)
        return [dict(k="struct", name=f"P{2 * half}", layout="packed",
                     fields=[dict(name="lo", ty=4), dict(name="hi", ty=4)],
                     abi_size=size, abi_align=align), int_ty(half)]
    return [int_ty(int(name[1:]), signed=name[0] == "i")]


def document(name, tag, version, extra):
    """`fn(p: *T, a: T, b: T)`: `tag` on `p`; types 0 T, 1 void, 2 noreturn, 3 *T, then ?T."""
    operand = operand_types(name)
    child = operand[0]
    optional_size = -(-(child["abi_size"] + 1) // child["abi_align"]) * child["abi_align"]
    ptr = dict(k="ptr", size="one", const=False, child=0, ptr_align=child["abi_align"],
               volatile=False, allowzero=False, sentinel=False, host_size=0, abi_size=8, abi_align=8)
    types = [child, VOID, NORETURN, ptr, *operand[1:]]
    optional = len(types)
    types.append(dict(k="optional", child=0, abi_size=optional_size, abi_align=child["abi_align"]))
    args = [dict(id=0, tag="arg", ty=3, param=0), dict(id=1, tag="arg", ty=0, param=1),
            dict(id=2, tag="arg", ty=0, param=2)]
    p, a, b = (dict(inst=i) for i in range(3))
    if tag.startswith("cmpxchg"):
        op = dict(id=3, tag=tag, ty=optional, args=[p, a, b], success_order="seq_cst",
                  failure_order="seq_cst")
    elif tag == "atomic_rmw":
        op = dict(id=3, tag=tag, ty=0, args=[p, a], order="seq_cst", **extra)
    elif tag == "atomic_load":
        op = dict(id=3, tag=tag, ty=0, args=[p], order="seq_cst")
    else:
        op = dict(id=3, tag=tag, ty=1, args=[p, a])
    void = dict(ty=1, val="{}")
    body = args + [op, dict(id=4, tag="ret", ty=2, args=[void])]
    return dict(schema=11, zig_version=version, name=name, types=types, params=[3, 0, 0], ret=1,
                body=body, globals=[])


PADDED_WIDTHS = (3, 9, 17, 24, 31, 33, 40, 48, 56, 63, 65, 72)

# (fixture, AIR tag, extra fields, the rejection's `@` builtin or `None` if accepted)
CASES = [
    ("u24", "cmpxchg_strong", {}, "@cmpxchgStrong"),
    ("u24", "cmpxchg_weak", {}, "@cmpxchgWeak"),
    ("u40", "cmpxchg_strong", {}, "@cmpxchgStrong"),
    ("u40", "cmpxchg_weak", {}, "@cmpxchgWeak"),
    ("u48", "cmpxchg_strong", {}, "@cmpxchgStrong"),
    ("u56", "cmpxchg_strong", {}, "@cmpxchgStrong"),
    ("i40", "cmpxchg_strong", {}, "@cmpxchgStrong"),
    ("u31", "cmpxchg_strong", {}, "@cmpxchgStrong"),
    ("u12", "cmpxchg_weak", {}, "@cmpxchgWeak"),
    ("u1", "cmpxchg_strong", {}, "@cmpxchgStrong"),
    ("u72", "cmpxchg_strong", {}, "@cmpxchgStrong"),
    ("enum_24", "cmpxchg_strong", {}, "@cmpxchgStrong"),
    ("packed_40", "cmpxchg_weak", {}, "@cmpxchgWeak"),
    # Every padded width, signed and unsigned, native-probed to disagree with the model on
    # `.Max`/`.Min` (docs/upstream/padded-rmw-minmax.md); the signed ones even with zero padding.
    *[(f"{t}{w}", "atomic_rmw", {"op": op}, f"@atomicRmw .{op}")
      for t in "iu" for w in PADDED_WIDTHS for op in ("Max", "Min")],
    ("u8", "cmpxchg_strong", {}, None),
    ("u16", "cmpxchg_weak", {}, None),
    ("u32", "cmpxchg_strong", {}, None),
    ("u32", "cmpxchg_weak", {}, None),
    ("u64", "cmpxchg_strong", {}, None),
    ("u64", "cmpxchg_weak", {}, None),
    ("i64", "cmpxchg_strong", {}, None),
    ("bool", "cmpxchg_strong", {}, None),
    ("enum_32", "cmpxchg_strong", {}, None),
    ("packed_32", "cmpxchg_weak", {}, None),
    # Power-of-two widths: `.Max`/`.Min` agree with the model, signed and unsigned.
    *[(f"{t}{w}", "atomic_rmw", {"op": op}, None)
      for t in "iu" for w in (8, 16, 32, 64, 128) for op in ("Max", "Min")],
    # The other RMW ops mask their result, or only write the padding: padded widths stay supported.
    *[(f"{t}{w}", "atomic_rmw", {"op": op}, None)
      for t in "iu" for w in (24, 40) for op in ("Xchg", "Add", "Sub", "And", "Nand", "Or", "Xor")],
    ("u40", "atomic_load", {}, None),
    ("u40", "atomic_store_seq_cst", {}, None),
]


def fixtures(version="0.16.0"):
    """name -> (document, expected): `None` accepted, else the rejected builtin."""
    result = {}
    for ty, tag, extra, expected in CASES:
        name = "_".join([ty, tag, *extra.values()]).lower()
        doc = document(ty, tag, version, extra)
        doc["name"] = name
        result[name] = (doc, expected)
    return result


def invoke(binary, *argv):
    return subprocess.run([str(binary), *map(str, argv)], capture_output=True, text=True,
                          timeout=30, check=False)


def diagnostics(binary, air):
    result = invoke(binary, "--diagnostics-json", air)
    assert result.stderr == "", result.stderr
    report = json.loads(result.stdout)
    assert result.returncode == (1 if report["status"] == "rejected" else 0), result
    return report


def write(air, name, doc):
    for old in air.glob("*.json"):
        old.unlink()
    (air / f"{name}.json").write_text(json.dumps(doc))


def assert_padded(report, function, builtin):
    signed_minmax = function[0] == "i" and function.endswith(("_max", "_min"))
    assert report["status"] == "rejected", report
    found = [d for d in report["diagnostics"] if d["code"] == "PADDED_ATOMIC"]
    assert len(found) == 1, (function, report)
    d = found[0]
    assert d["function"] == function, d
    assert (d["phase"], d["category"]) == ("check", "unsupported_semantics"), d
    assert d["anchor"]["id_space"] == "canonical" and d["anchor"]["instruction"] == 3, d
    assert builtin in d["message"] and "power-of-two number of bytes" in d["message"], d
    # A signed `.Max`/`.Min` names its own cause (the native order is wrong even with zero padding).
    assert ("large unsigned value" in d["message"]) == signed_minmax, d
    # The specific code supersedes the generic instruction check, and it is the only blocker.
    assert all(x["code"] == "PADDED_ATOMIC" for x in report["diagnostics"]), report


def check_fixtures(binary, air):
    checks = 0
    for version in VERSIONS:
        for name, (doc, expected) in fixtures(version).items():
            write(air, name, doc)
            report = diagnostics(binary, air)
            if expected is None:
                assert report["status"] == "checked", (version, name, report)
            else:
                assert_padded(report, name, expected)
            checks += 1
    return checks


def check_emission(binary, tmp, air):
    """Ordinary translation fails closed and leaves the output untouched."""
    out = tmp / "Gen.lean"
    for name, (doc, expected) in fixtures().items():
        write(air, name, doc)
        out.write_text("KEEP\n")
        result = invoke(binary, air, "-o", out, "--namespace", "Padded")
        if expected is None:
            assert result.returncode == 0, (name, result.stderr)
            assert out.read_text() != "KEEP\n", name
        else:
            assert result.returncode == 1 and expected in result.stderr, (name, result.stderr)
            assert "padding bits" in result.stderr, (name, result.stderr)
            assert out.read_text() == "KEEP\n", name
    return len(fixtures())


class SelfTest(unittest.TestCase):
    def test_fixture_schema(self):
        for version in VERSIONS:
            for name, (doc, _) in fixtures(version).items():
                self.assertEqual(doc["zig_version"], version)
                self.assertEqual(doc["name"], name)
                ids = [i["id"] for i in doc["body"]]
                self.assertEqual(ids, sorted(set(ids)), name)
                child = doc["types"][0]
                self.assertEqual(doc["types"][3]["ptr_align"], child["abi_align"])

    def test_layouts(self):
        self.assertEqual(int_size(24), (4, 4))
        self.assertEqual(int_size(40), (8, 8))
        self.assertEqual(int_size(72), (16, 16))
        self.assertEqual(int_size(31), (4, 4))
        self.assertEqual(int_size(1), (1, 1))

    def test_each_padded_width_has_a_full_width_control(self):
        expected = {name: e for name, (_, e) in fixtures().items()}
        rejected = {n for n, e in expected.items() if e}
        accepted = {n for n, e in expected.items() if e is None}
        for tag in ("cmpxchg_strong", "cmpxchg_weak"):
            self.assertTrue(any(n.endswith(tag) for n in rejected), tag)
            self.assertTrue(any(n.endswith(tag) for n in accepted), tag)
        self.assertIn("u32_cmpxchg_strong", accepted)
        self.assertIn("u64_cmpxchg_strong", accepted)
        self.assertIn("u24_cmpxchg_strong", rejected)
        self.assertIn("u40_cmpxchg_strong", rejected)

    def test_minmax_rejected_at_every_padded_width_and_accepted_at_full_width(self):
        expected = {name: e for name, (_, e) in fixtures().items()}
        for signedness in "iu":
            for op in ("max", "min"):
                for width in PADDED_WIDTHS:
                    self.assertTrue(expected[f"{signedness}{width}_atomic_rmw_{op}"])
                for width in (8, 16, 32, 64, 128):
                    self.assertIsNone(expected[f"{signedness}{width}_atomic_rmw_{op}"])
        for op in ("xchg", "add", "sub", "and", "nand", "or", "xor"):
            self.assertIsNone(expected[f"i24_atomic_rmw_{op}"])
            self.assertIsNone(expected[f"u40_atomic_rmw_{op}"])

    def test_fixture_names_are_unique(self):
        self.assertEqual(len({f"{t}_{g}_{'_'.join(e.values())}" for t, g, e, _ in CASES}), len(CASES))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path, nargs="?")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        unittest.main(argv=[sys.argv[0]])
        return
    if not args.binary:
        parser.error("provide a root-built translator, or --self-test")
    binary = args.binary.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix="air2lean-padded-atomics-") as tmp:
        tmp = Path(tmp)
        air = tmp / "air"
        air.mkdir()
        checks = check_fixtures(binary, air) + check_emission(binary, tmp, air)
    print(f"padded atomic checks: {checks}")


if __name__ == "__main__":
    main()
