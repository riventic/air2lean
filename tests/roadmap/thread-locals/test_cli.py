#!/usr/bin/env python3
"""C02 thread-local storage CLI regressions for a root-built translator.

The retained 0.16.0 and 0.15.2 exports translate to the retained `ThreadLocals/Gen.lean` (the
0.15.2 output differs only in its profile header). Every case the model does not cover is
rejected with a stable diagnostic. Never builds or invokes compilers.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
GEN = HERE / "ThreadLocals" / "Gen.lean"
ARGS = ["--namespace", "ThreadLocals", "--prefix", "thread_locals."]
WORKER = "thread_locals.bumpTwice.json"


def fixtures(version="0.16.0"):
    return {p.name: json.loads(p.read_text()) for p in sorted((HERE / "air" / version).glob("*.json"))}


def translate(binary, documents, directory):
    air = directory / "air"
    air.mkdir()
    for name, document in documents.items():
        (air / name).write_text(json.dumps(document))
    out = directory / "Gen.lean"
    out.write_text("sentinel\n")
    result = subprocess.run([str(binary), str(air), "-o", str(out), *ARGS], text=True,
                            capture_output=True, check=False, timeout=120)
    return result, out


def accept(binary, documents):
    with tempfile.TemporaryDirectory(prefix="air2lean-thread-locals-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 0, result.stderr
        return out.read_text()


def reject(binary, documents, marker, code=None):
    """CLI rejection with `marker`; `--diagnostics-json` reports `code` if given."""
    with tempfile.TemporaryDirectory(prefix="air2lean-thread-locals-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 1, (marker, result.returncode, result.stderr)
        assert marker in result.stderr, (marker, result.stderr)
        assert out.read_text() == "sentinel\n", "a rejected input replaced the output"
        if code is not None:
            diagnostics = subprocess.run([str(binary), "--diagnostics-json", str(Path(d) / "air")],
                                         text=True, capture_output=True, check=False, timeout=120)
            assert diagnostics.returncode == 1, diagnostics.stderr
            report = json.loads(diagnostics.stdout)
            codes = [entry["code"] for entry in report["diagnostics"]]
            assert code in codes, (marker, codes)
    return 1


def body(text):
    """The generated Lean without its profile header."""
    return text.split("\n", 1)[1]


def nav_insts(document):
    return [i for i in document["body"] if i["tag"] == "runtime_nav_ptr"]


def mutate(edit, name=WORKER):
    documents = fixtures()
    edit(documents[name])
    return documents


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else HERE.parents[2] / ".lake/build/bin/air2lean")
    checks = 0

    # Positive: both versions give the retained translation.
    text = accept(binary, fixtures())
    assert text == GEN.read_text(), "fresh 0.16.0 translation differs from ThreadLocals/Gen.lean"
    assert body(accept(binary, fixtures("0.15.2"))) == body(GEN.read_text()), "0.15.2 body differs"
    assert ").mainTls #[0]" in text and "def tlsInit" in text
    assert "Zig.ConcM.tlsThread tlsInit (discard (Zig.ConcM.liftMem (bumpTwice a)))" in text
    assert text.count("Zig.tlsPtr 0") == 6
    checks += 2

    # The old exporter's marker keeps the old rejection.
    def marker(d):
        for i in nav_insts(d):
            del i["global"]
            i["unsupported"] = True
    checks += reject(binary, mutate(marker), "identity and lifetime")

    def no_global(d):
        for i in nav_insts(d):
            del i["global"]
    checks += reject(binary, mutate(no_global), "identity and lifetime")

    def bad_index(d):
        nav_insts(d)[0]["global"] = 7
    checks += reject(binary, mutate(bad_index), "names no global", "GLOBAL_FAILURE")

    def not_threadlocal(d):
        d["globals"][0]["threadlocal"] = False
    checks += reject(binary, mutate(not_threadlocal), "which is not `threadlocal`", "GLOBAL_FAILURE")

    def extern_tls(d):
        d["globals"][0]["extern"] = True
        del d["globals"][0]["init"]
    checks += reject(binary, mutate(extern_tls), "it is `extern`", "GLOBAL_FAILURE")

    def no_init(d):
        del d["globals"][0]["init"]
    checks += reject(binary, mutate(no_init), "the AIR file has no initial value", "STRUCTURE_FAILURE")

    def pointer_type(d):
        d["types"].append(dict(k="ptr", size="one", const=False, child=2, ptr_align=4,
                               volatile=False, allowzero=False, sentinel=False, host_size=0,
                               abi_size=8, abi_align=8))
        d["globals"][0]["ty"] = len(d["types"]) - 1
        d["globals"][0]["init"] = dict(ty=len(d["types"]) - 1, undef=True)
    checks += reject(binary, mutate(pointer_type), "its type can hold a pointer")

    def wrong_child(d):
        d["types"].append(dict(k="int", signed=False, bits=64, abi_size=8, abi_align=8))
        d["globals"][0]["ty"] = len(d["types"]) - 1
        d["globals"][0]["init"] = dict(ty=len(d["types"]) - 1, val="7")
    checks += reject(binary, mutate(wrong_child), "must point to its global's type", "GLOBAL_FAILURE")

    def over_aligned(d):
        ptr = d["types"][nav_insts(d)[0]["ty"]]
        ptr["ptr_align"] = 8
    checks += reject(binary, mutate(over_aligned), "`align(8)` to a `threadlocal` global")

    def volatile(d):
        d["types"][nav_insts(d)[0]["ty"]]["volatile"] = True
    checks += reject(binary, mutate(volatile), "volatile")

    # A constant pointer into a thread-local (0.14.1's form) has one address in every thread.
    def constant_pointer(d):
        nav = nav_insts(d)[0]
        ptr_ty = nav["ty"]
        nav_id = nav["id"]
        for i in d["body"]:
            for k, a in enumerate(i.get("args", [])):
                if a == {"inst": nav_id}:
                    i["args"][k] = {"ty": ptr_ty, "ptr": {"global": 0, "off": 0}}
    checks += reject(binary, mutate(constant_pointer), "a constant pointer to the `threadlocal` global")

    print(f"{checks} C02 thread-local CLI checks passed")


if __name__ == "__main__":
    main()
