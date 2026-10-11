#!/usr/bin/env python3
"""CLI regressions for the inline asm effect contract (A01), for a root-built translator.

The retained translation of air/0.16.0 (hand-written AIR in the exporter's schema) is checked
byte for byte, and every operand, alias and clobber form outside the contract is rejected with a
named reason through the CLI and `--diagnostics-json`. Never builds or invokes compilers.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AIR = HERE / "air" / "0.16.0"
GEN = HERE / "AsmEffects" / "Gen.lean"
# The fixture AIR is schema 11 (no target profile): the reference ABI is accepted explicitly.
ARGS = ["--namespace", "AsmEffects", "--prefix", "asm_effects.", "--profile", "legacy-abi64-le"]


def fixtures():
    return {p.name: json.loads(p.read_text()) for p in sorted(AIR.glob("*.json"))}


def translate(binary, documents, directory, extra=()):
    air = directory / "air"
    air.mkdir()
    for name, document in documents.items():
        (air / name).write_text(json.dumps(document))
    out = directory / "Gen.lean"
    out.write_text("sentinel\n")
    result = subprocess.run([str(binary), str(air), "-o", str(out), *ARGS, *extra], text=True,
                            capture_output=True, check=False, timeout=60)
    return result, out


def accept(binary, documents):
    with tempfile.TemporaryDirectory(prefix="air2lean-asm-effects-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 0, result.stderr
        return out.read_text()


def reject(binary, documents, marker):
    """CLI rejection naming `marker`; `--diagnostics-json` reports the same message."""
    with tempfile.TemporaryDirectory(prefix="air2lean-asm-effects-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 1, (marker, result.returncode, result.stderr)
        assert marker in result.stderr, (marker, result.stderr)
        assert out.read_text() == "sentinel\n", "a rejected input replaced the output"
        diagnostics = subprocess.run([str(binary), "--diagnostics-json", str(Path(d) / "air"), "--profile", "legacy-abi64-le"],
                                     text=True, capture_output=True, check=False, timeout=60)
        assert diagnostics.returncode == 1, diagnostics.stderr
        report = json.loads(diagnostics.stdout)
        hits = [e for e in report["diagnostics"] if marker in e["message"]]
        assert hits, (marker, report)
        assert all(e["code"] == "INSTRUCTION_FAILURE" for e in hits), hits
    return 1


def asm_inst(document):
    return next(i for i in document["body"] if i["tag"] == "assembly")


def only(name, edit):
    document = copy.deepcopy(fixtures()[f"asm_effects.{name}.json"])
    edit(asm_inst(document), document)
    return {f"asm_effects.{name}.json": document}


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else ROOT / ".lake/build/bin/air2lean")
    checks = 0

    # Positive: the retained translation, byte for byte, with the effect contract's shape.
    text = accept(binary, fixtures())
    assert text == GEN.read_text(), "fresh translation differs from AsmEffects/Gen.lean"
    for needle in [
        # `+m`: old value loaded, passed after the inputs, new value stored to the same place.
        "    let a1o0 ← Zig.load (BitVec 32) 4 p0\n    let a1 := airAsmFx_2840265087 a1o0\n"
        "    Zig.store (α := BitVec 32) 4 p0 a1\n",
        # `=m`: no read, one store.
        "    let a2 := airAsmFx_2229968081 p1\n    Zig.store (α := BitVec 64) 8 p0 a2\n",
        # Two memory operands: the alias guard first, then reads, call, stores in output order.
        "    Zig.Asm.guard [(p0, 4), (p1, 4)]\n    let a2o0 ← Zig.load (BitVec 32) 4 p0\n"
        "    let a2o1 ← Zig.load (BitVec 32) 4 p1\n    let a2 := airAsmFx_3102165980 a2o0 a2o1\n"
        "    Zig.store (α := BitVec 32) 4 p0 a2.1\n    Zig.store (α := BitVec 32) 4 p1 a2.2\n",
        # `+r` on a local: the input, then the old value.
        "    let a4o0 ← pure ((← get).local2)\n    let a4 := airAsmFx_2072205809 p1 a4o0\n",
        "opaque airAsmFx_1655126372 : Unit\n",
    ]:
        assert needle in text, needle
    assert "opaque airAsm_" not in text, "an effect-form op kept the register-only name"
    checks += 1

    # The register-only goldens keep their exact translation (A03 pins Proofs/Asm/Gen.lean).
    with tempfile.TemporaryDirectory(prefix="air2lean-asm-effects-") as d:
        out = Path(d) / "Gen.lean"
        result = subprocess.run([str(binary), str(ROOT / "tests/golden/asm/air"), "-o", str(out),
                                 "--namespace", "Asm", "--prefix", "asm.", "--profile", "legacy-abi64-le"], text=True,
                                capture_output=True, check=False, timeout=60)
        assert result.returncode == 0, result.stderr
        # check.sh may have rewritten Proofs/Asm/Gen.lean with this host's profile header first
        # (CI's x86_64 job does): compare the translations without it.
        def body(text: str) -> str:
            return "\n".join(l for l in text.split("\n") if not l.startswith("-- air2lean-profile:"))
        fresh = body(out.read_text())
        assert fresh == body((ROOT / "Proofs/Asm/Gen.lean").read_text()), "register-only asm changed"
    checks += 1

    # The same template without the clobber is a register-only op of the same hash: both opaques
    # are emitted (the identity key omits clobbers).
    documents = fixtures()
    plain = copy.deepcopy(documents["asm_effects.barrier.json"])
    plain["name"] = "asm_effects.plain"
    asm_inst(plain)["clobbers"] = []
    documents["asm_effects.plain.json"] = plain
    text = accept(binary, documents)
    assert "opaque airAsmFx_1655126372 : Unit\n" in text and "opaque airAsm_1655126372 : Unit\n" in text
    assert "pure (airAsm_1655126372)" in text and "pure (airAsmFx_1655126372)" in text
    checks += 1

    # "memory" clobber: only the reviewed registry block (empty template, no operands).
    def memory(i, _):
        i["clobbers"] = ["cc", "memory"]
    checks += reject(binary, only("incm", memory), "an asm 'memory' clobber is outside the subset")

    def barrier_nop(i, _):
        i["source"] = "nop"
    checks += reject(binary, only("barrier", barrier_nop), "no reviewed registry entry")

    def barrier_nonvolatile(i, _):
        i["volatile"] = False
    checks += reject(binary, only("barrier", barrier_nonvolatile), "no reviewed registry entry")

    # Read-write or memory output without a location (the expression's own result).
    def rw_result(i, d):
        i["outputs"] = [{"constraint": "+r", "name": "x"}]
        i["ty"] = 0
    checks += reject(binary, only("incm", rw_result), "needs an lvalue operand")

    def mem_result(i, d):
        i["outputs"] = [{"constraint": "=m", "name": "x"}]
        i["ty"] = 0
    checks += reject(binary, only("incm", mem_result), "needs an lvalue operand")

    # Constraints outside the grammar.
    for c in ["=&m", "+&r", "=rm", "=g", "&r"]:
        def bad_out(i, _, c=c):
            i["outputs"][0]["constraint"] = c
        checks += reject(binary, only("incm", bad_out),
                         f"asm output constraint '{c}' is not a register, read-write or memory")
    for c in ["m", "i", "rm", "+r"]:
        def bad_in(i, _, c=c):
            i["inputs"][0]["constraint"] = c
        checks += reject(binary, only("setm", bad_in), f"asm input constraint '{c}' is not a register")

    # A memory operand must be a whole 1/2/4/8 byte integer.
    def odd_width(i, d):
        d["types"].append({"k": "int", "signed": False, "bits": 24, "abi_size": 4, "abi_align": 4})
        d["types"][4] = dict(d["types"][4], child=len(d["types"]) - 1)
    checks += reject(binary, only("incm", odd_width),
                     "is a 24-bit integer, not a whole 1, 2, 4 or 8 byte memory operand")

    # A write through a const pointer.
    def const_ptr(i, d):
        d["types"][4] = dict(d["types"][4], const=True)
    checks += reject(binary, only("incm", const_ptr), "writes through a const pointer")

    # Aliases: the same pointer value (or the same local) for two written outputs.
    def same_ptr(i, _):
        i["outputs"][1]["ref"] = {"inst": 0}
    checks += reject(binary, only("swapm", same_ptr), "two asm outputs write the same location")

    def same_local(i, _):
        i["outputs"] = [{"constraint": "+r", "name": "x", "ref": {"inst": 3}},
                        {"constraint": "=r", "name": "y", "ref": {"inst": 3}}]
    checks += reject(binary, only("addr", same_local), "two asm outputs write the same location")

    # Clobbers: a clobbered register cannot carry an operand (sub-register aliases count).
    def clobber_pin(i, _):
        i["outputs"][0]["constraint"] = "+{eax}"
        i["clobbers"] = ["cc", "rax"]
    checks += reject(binary, only("addr", clobber_pin), "clobber names a register that also carries")

    def clobber_input(i, _):
        i["inputs"][0]["constraint"] = "{rcx}"
        i["clobbers"] = ["cl"]
    checks += reject(binary, only("setm", clobber_input), "clobber names a register that also carries")

    # Two outputs pinned to one register; an input pinned to an early-clobber output's register.
    def two_pins(i, _):
        i["outputs"] = [{"constraint": "={eax}", "name": "a", "ref": {"inst": 0}},
                        {"constraint": "={ax}", "name": "b", "ref": {"inst": 1}}]
        i["clobbers"] = []
    checks += reject(binary, only("swapm", two_pins), "pin the same register")

    def early_pin(i, _):
        i["outputs"][0]["constraint"] = "=&{rdx}"
        i["inputs"][0]["constraint"] = "{edx}"
    checks += reject(binary, only("setm", early_pin), "pins the register of an early-clobber")

    def rw_pin(i, _):
        i["outputs"][0]["constraint"] = "+{rax}"
        i["inputs"][0]["constraint"] = "{eax}"
        i["clobbers"] = []
    checks += reject(binary, only("addr", rw_pin), "pins the register of an early-clobber")

    # A matching input tied to a read-write or memory output.
    def tie_rw(i, _):
        i["inputs"][0]["constraint"] = "0"
    checks += reject(binary, only("addr", tie_rw), "ties to a read-write, memory or early-clobber")
    checks += reject(binary, only("setm", tie_rw), "ties to a read-write, memory or early-clobber")

    print(f"{checks} asm-effect CLI checks passed")


if __name__ == "__main__":
    main()
