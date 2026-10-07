#!/usr/bin/env python3
"""L08 packed fields: CLI regressions for a root-built translator over hand-written AIR.

The committed air/0.16.0 files are exactly `fixtures.py`'s output; their fresh translation is
PackedFields/Gen.lean byte for byte. Each exporter pointer layout that the model does not compute
(`Check.lean`'s `packedFieldPtr?`) is rejected with the stable code PACKED_LAYOUT, and the
translation leaves its output untouched. `--self-test` checks the fixture builders only.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fixtures as fx  # noqa: E402

GEN = HERE / "PackedFields" / "Gen.lean"
ARGS = ["--namespace", "PackedFields", "--prefix", fx.PREFIX]


def invoke(binary, *argv):
    return subprocess.run([str(binary), *map(str, argv)], capture_output=True, text=True,
                          timeout=60, check=False)


def write(air, documents):
    air.mkdir(exist_ok=True)
    for old in air.glob("*.json"):
        old.unlink()
    for name, document in documents.items():
        (air / name).write_text(json.dumps(document))


def translate(binary, documents, tmp):
    air, out = tmp / "air", tmp / "Gen.lean"
    write(air, documents)
    out.write_text("KEEP\n")
    return invoke(binary, air, "-o", out, *ARGS), out


def one(name, edit=None):
    """The fixture of function `name`, with `edit(types, body)` applied."""
    document = fx.fixtures()[f"{fx.PREFIX}{name}.json"]
    if edit:
        edit(document["types"], document["body"])
    return {f"{fx.PREFIX}{name}.json": document}


def reject(binary, tmp, documents, code, marker):
    result, out = translate(binary, documents, tmp)
    assert result.returncode == 1 and marker in result.stderr, (marker, result.returncode, result.stderr)
    assert out.read_text() == "KEEP\n", "a rejected input replaced the output"
    report = invoke(binary, "--diagnostics-json", tmp / "air")
    assert report.returncode == 1 and report.stderr == "", report
    found = [d for d in json.loads(report.stdout)["diagnostics"] if marker in d["message"]]
    assert found, (marker, report.stdout)
    for d in found:
        assert d["code"] == code, d
        assert (d["phase"], d["category"]) == ("check", "unsupported_semantics" if code == "PACKED_LAYOUT"
                                               else "validation_failure"), d
        assert d["anchor"]["id_space"] == "canonical", d
    return 1


def layout(ty, **changes):
    def edit(types, _body):
        types[ty].update(changes)
    return edit


MISMATCH = "packed layout mismatch"


def check(binary, tmp):
    checks = 0
    result, out = translate(binary, fx.fixtures(), tmp)
    assert result.returncode == 0, result.stderr
    text = out.read_text()
    assert text == GEN.read_text(), "fresh translation differs from PackedFields/Gen.lean"
    # Host width 3 (LLVM) and 4 (x86_64); `inner.c` at byte 1 of the host; `undefined` per bit.
    assert "Zig.storeBits (α := BitVec 4) 3 4 0 i0 (5 : BitVec 4)" in text
    assert "Zig.storeBits (α := BitVec 4) 4 4 0 i0 (9 : BitVec 4)" in text
    assert "let i3 ← pure (i2.add 1)\n    Zig.store (α := BitVec 8) 1 i3 (171 : BitVec 8)" in text
    assert "Zig.storeUndefBits 4 3 4 4 i1" in text
    # The local with an `undefined` field store is a stack block, never a defaulted `Locals` value.
    assert "def localUndef  : Zig.MemM (BitVec 4) := do\n  let s0 ← Zig.allocStack 4 4" in text
    checks += 1

    # Exporter layouts the model does not compute: PACKED_LAYOUT, nothing translated.
    for name, edit, got in [
            ("setA", layout(fx.P_A, bit_offset=1), "host_size 3, bit_offset 1"),
            ("setA", layout(fx.P_A, host_size=2), "host_size 2, bit_offset 0"),
            ("signedS", layout(fx.P_S, bit_offset=15), "host_size 3, bit_offset 15"),
            # A nested bit-pointer keeps its base's host (3), and adds its bit offset (4).
            ("undefField", layout(fx.P_B, host_size=4), "host_size 4, bit_offset 4"),
            ("undefField", layout(fx.P_B, bit_offset=0), "host_size 3, bit_offset 0"),
            # `inner.b` is no byte pointer: bit 4.
            ("undefField", layout(fx.P_B, host_size=0), "a byte pointer"),
            # `inner.c` is a byte pointer or the bit-pointer at bit 8 of the same host.
            ("innerC", layout(fx.P_C, host_size=3, bit_offset=4, ptr_align=4), "host_size 3, bit_offset 4")]:
        checks += reject(binary, tmp, one(name, edit), "PACKED_LAYOUT", got)
    # The other form of `inner.c` is accepted: a bit-pointer at bit 8 of the same host.
    result, _ = translate(binary, one("innerC", layout(fx.P_C, host_size=3, bit_offset=8, ptr_align=4)), tmp)
    assert result.returncode == 0, result.stderr
    checks += 1
    # Every mismatch message names the model's layout.
    result, _ = translate(binary, one("setA", layout(fx.P_A, bit_offset=1)), tmp)
    assert "the model computes host_size 3 or 4, bit_offset 0" in result.stderr, result.stderr
    checks += 1
    # A field past its host integer is a type error.
    checks += reject(binary, tmp, one("setA", layout(fx.P_A, host_size=1, bit_offset=6)),
                     "TYPE_FAILURE", "a bit-pointer field extends beyond its host integer")
    return checks


class SelfTest(unittest.TestCase):
    def test_committed_fixtures(self):
        committed = {p.name: p.read_text() for p in sorted(fx.AIR.glob("*.json"))}
        self.assertEqual(committed, {n: fx.render(d) for n, d in fx.fixtures().items()})

    def test_bit_layout(self):
        types = fx.TYPES
        bits = {fx.U4: 4, fx.U8: 8, fx.I5: 5, fx.BOOL: 1, fx.MODE: 2, fx.INNER: 12}
        offset = 0
        for field in types[fx.REG]["fields"]:
            offset += bits[field["ty"]]
        self.assertEqual(offset, 24)
        self.assertEqual((types[fx.P_S]["bit_offset"], types[fx.P_ON]["bit_offset"],
                          types[fx.P_MODE]["bit_offset"]), (16, 21, 22))
        self.assertEqual(types[fx.P_C]["host_size"], 0)

    def test_ids_ascending(self):
        for name, document in fx.fixtures().items():
            ids = [i["id"] for i in document["body"]]
            self.assertEqual(ids, list(range(len(ids))), name)


def main():
    if sys.argv[1:] == ["--self-test"]:
        unittest.main(argv=[sys.argv[0]])
        return
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else HERE.parents[2] / ".lake/build/bin/air2lean")
    with tempfile.TemporaryDirectory(prefix="air2lean-packed-fields-") as tmp:
        checks = check(binary.resolve(strict=True), Path(tmp))
    print(f"{checks} packed-field CLI checks passed")


if __name__ == "__main__":
    main()
