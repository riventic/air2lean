#!/usr/bin/env python3
"""L12 global-initialization CLI regressions for a root-built translator.

Every path where a global's initial value can be absent is either represented explicitly or
rejected with a stable diagnostic; it is never replaced by a default. Never builds or invokes
compilers: the fixtures in air/0.16.0 are hand-written AIR in the exporter's schema.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"
GEN = HERE / "GlobalInit" / "Gen.lean"
# The fixtures are schema-11 AIR: translating them needs the explicit legacy profile.
ARGS = ["--namespace", "GlobalInit", "--prefix", "global_init.", "--profile", "legacy-abi64-le"]


def fixtures():
    return {p.name: json.loads(p.read_text()) for p in sorted(AIR.glob("*.json"))}


def translate(binary, documents, directory):
    air = directory / "air"
    air.mkdir()
    for name, document in documents.items():
        (air / name).write_text(json.dumps(document))
    out = directory / "Gen.lean"
    out.write_text("sentinel\n")
    result = subprocess.run([str(binary), str(air), "-o", str(out), *ARGS], text=True,
                            capture_output=True, check=False, timeout=60)
    return result, out


def accept(binary, documents):
    with tempfile.TemporaryDirectory(prefix="air2lean-global-init-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 0, result.stderr
        return out.read_text()


def reject(binary, documents, marker, code="GLOBAL_FAILURE", diagnostic=None):
    """CLI rejection with `marker`; `--diagnostics-json` reports `code` with `diagnostic`."""
    with tempfile.TemporaryDirectory(prefix="air2lean-global-init-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 1, (marker, result.returncode, result.stderr)
        assert marker in result.stderr, (marker, result.stderr)
        assert out.read_text() == "sentinel\n", "a rejected input replaced the output"
        diagnostics = subprocess.run([str(binary), "--diagnostics-json", str(Path(d) / "air"), "--profile", "legacy-abi64-le"],
                                     text=True, capture_output=True, check=False, timeout=60)
        assert diagnostics.returncode == 1, diagnostics.stderr
        report = json.loads(diagnostics.stdout)
        codes = [entry["code"] for entry in report["diagnostics"]]
        assert code in codes, (marker, codes)
        assert any((diagnostic or marker) in entry["message"] for entry in report["diagnostics"]), report
    return 1


def mutate(name, edit):
    """One fixture file with `edit` applied to its first global."""
    documents = fixtures()
    edit(documents[name]["globals"][0], documents[name])
    return documents


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else HERE.parents[2] / ".lake/build/bin/air2lean")
    checks = 0

    # Positive: retained translation, byte-identical, with explicit external initial state.
    text = accept(binary, fixtures())
    assert text == GEN.read_text(), "fresh translation differs from GlobalInit/Gen.lean"
    assert "structure ExternInit where" in text
    assert "def mem0 (σ : Zig.Placement) (ext : ExternInit) : Zig.Mem" in text
    assert text.index("  counter : BitVec 32") < text.index("  limit : BitVec 32"), "block order"
    assert "(Zig.Enc.encode (ext.counter : BitVec 32), 4, .global)" in text
    assert "(Zig.Enc.encode (ext.limit : BitVec 32), 4, .constGlobal)" in text
    # A wholly `undefined` global is explicit undefined bytes.
    assert "(Array.replicate (Zig.Enc.size (BitVec 32)) .undef, 4, .global)" in text
    checks += 1

    # Without an extern global, mem0 takes only the placement (no reserved structure).
    plain = {k: v for k, v in fixtures().items() if "Scratch" in k}
    text = accept(binary, plain)
    assert "ExternInit" not in text and "def mem0 (σ : Zig.Placement) : Zig.Mem :=" in text
    checks += 1

    # An `ExternInit` field never collides with the structure constructor or another field.
    def rename(g, doc):
        g["name"] = "global_init.mk"
    text = accept(binary, mutate("global_init.bump.json", rename))
    assert "  mk_air2lean1 : BitVec 32" in text and "ext.mk_air2lean1" in text
    checks += 1

    bump = "global_init.bump.json"
    scratch = "global_init.readScratch.json"
    extern_cases = [
        ("threadlocal", lambda g, d: g.update(threadlocal=True), "it is `extern` (its instances are defined outside the program)"),
        ("init", lambda g, d: g.update(init=dict(ty=0, val="5")), "the AIR file gives it an initial value"),
        ("unnamed", lambda g, d: (g.pop("name"), g.update(const=True)), "it has no name"),
    ]
    for _, edit, marker in extern_cases:
        checks += reject(binary, mutate(bump, edit), marker)

    # Storage that can hold a pointer or error identity is outside explicit external state.
    def pointer(g, d):
        d["types"].append(dict(k="ptr", size="one", const=False, child=0, ptr_align=4,
                               volatile=False, allowzero=False, sentinel=False, host_size=0,
                               abi_size=8, abi_align=8))
        g["ty"] = len(d["types"]) - 1
    checks += reject(binary, mutate(bump, pointer), "its type can hold a pointer")

    def error_union(g, d):
        d["types"] += [dict(k="error_set", abi_size=2, abi_align=2, errors=["Bad"]),
                       dict(k="error_union", error=len(d["types"]), payload=0, abi_size=8, abi_align=4)]
        g["ty"] = len(d["types"]) - 1
    checks += reject(binary, mutate(bump, error_union), "its type holds error storage")

    # A missing initial value of a non-extern global is rejected, never defaulted.
    checks += reject(binary, mutate(scratch, lambda g, d: g.pop("init")),
                     "the AIR file has no initial value", "STRUCTURE_FAILURE",
                     "global has no initial value")

    # A partly `undefined` initializer is rejected (emission would read it as 0/false).
    def partial(g, d):
        d["types"].append(dict(k="struct", name="global_init.Pair", layout="auto",
                               fields=[dict(name="a", ty=0, offset=0), dict(name="b", ty=0, offset=4)],
                               abi_size=8, abi_align=4))
        g["ty"] = len(d["types"]) - 1
        g["init"] = dict(ty=g["ty"], elems=[dict(ty=0, val="1"), dict(ty=0, undef=True)])
    checks += reject(binary, mutate(scratch, partial), "a partly `undefined` initial value")

    def array(g, d):
        d["types"].append(dict(k="array", len=2, child=0, sentinel=False, abi_size=8, abi_align=4))
        g["ty"] = len(d["types"]) - 1
        g["init"] = dict(ty=g["ty"], elems=[dict(ty=0, undef=True), dict(ty=0, val="2")])
    checks += reject(binary, mutate(scratch, array), "a partly `undefined` initial value")

    def optional(g, d):
        d["types"].append(dict(k="optional", child=0, abi_size=8, abi_align=4))
        g["ty"] = len(d["types"]) - 1
        g["init"] = dict(ty=g["ty"], some=dict(ty=0, undef=True))
    checks += reject(binary, mutate(scratch, optional), "a partly `undefined` initial value")

    # A shared name must agree on `extern` across files: no file may supply a value for it.
    documents = fixtures()
    documents["global_init.readCounter.json"] = copy.deepcopy(documents["global_init.readLimit.json"])
    other = documents["global_init.readCounter.json"]
    other["name"] = "global_init.readCounter"
    other["types"][2]["const"] = False
    other["globals"] = [dict(name="global_init.counter", ty=0, const=False, threadlocal=False,
                             extern=False, init=dict(ty=0, val="0"))]
    with tempfile.TemporaryDirectory(prefix="air2lean-global-init-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 1 and "inconsistent shared global 'global_init.counter'" in result.stderr, result.stderr
        assert out.read_text() == "sentinel\n"
    checks += 1

    print(f"{checks} L12 global-initialization CLI checks passed")


if __name__ == "__main__":
    main()
