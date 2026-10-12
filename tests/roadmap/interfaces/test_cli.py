#!/usr/bin/env python3
"""CLI regressions for open interfaces (docs/interfaces.md). Usage: test_cli.py <air2lean>.

`air/<version>/<program>` are the closures of `export.sh`. Never invokes a compiler."""
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
VERSIONS = ("0.17.0", "0.16.0", "0.15.2", "0.14.1")
ALLOC = json.loads((HERE / "registry-alloc.json").read_text())
RANDOM = json.loads((HERE / "registry-random.json").read_text())


def run(exe, air, out, *extra):
    return subprocess.run([str(exe), str(air), "-o", str(out), "--namespace", "T",
                           "--profile", "abi64-le-v1", *extra],
                          capture_output=True, text=True, timeout=300)


def registry(tmp, value):
    path = Path(tempfile.mkstemp(dir=tmp, suffix=".json")[1])
    path.write_text(json.dumps(value))
    return str(path)


def entry(base, **change):
    value = json.loads(json.dumps(base))
    value["interfaces"][0].update(change)
    value["interfaces"][0] = {k: v for k, v in value["interfaces"][0].items() if v is not None}
    return value


def rejects(result, message):
    assert result.returncode == 1 and message in result.stderr, (message, result.stderr)


def main(exe):
    checks = 0
    translated = ("--allocator-model", "translated")
    with tempfile.TemporaryDirectory(prefix="air2lean-interfaces-") as tmp:
        out = Path(tmp) / "Out.lean"
        for version in VERSIONS:
            lists = HERE / "air" / version / "lists"
            mix = HERE / "air" / version / "mix"
            rnd = HERE / "air" / version / "rnd"
            # Closed: without an interface every call through the vtable is `.illegal`, as before.
            result = run(exe, lists, out, "--prefix", "lists.", *translated)
            assert result.returncode == 0, result.stderr
            closed = out.read_text()
            assert "Ext" not in closed and "extCall" not in closed and "throw .illegal)" in closed
            # Open: the environment's arm, the `Ext` class and its binder, the header record.
            result = run(exe, lists, out, "--prefix", "lists.", *translated,
                         "--model-registry", registry(tmp, ALLOC))
            assert result.returncode == 0, result.stderr
            text = out.read_text()
            assert "\nclass Ext where\n" in text and "def Ext.closed : Ext where" in text
            assert "Zig.callC (Zig.extCall (Ext.call0 " in text and "throw .illegal)" not in text
            assert re.search(r"^def push \[Ext\] ", text, re.M) and "def dispatch [Ext] :" in text
            assert text.splitlines()[1].startswith("-- air2lean-interfaces: ")
            # Every closed arm's chain is kept: the open module only replaces its last arm.
            assert closed.count("if ") == text.count("if ")
            # A closure allocator is tested first; only another pointer calls the environment.
            result = run(exe, mix, out, "--prefix", "mix.", *translated,
                         "--model-registry", registry(tmp, ALLOC))
            assert result.returncode == 0, result.stderr
            assert re.search(r"if i\d+ == \(⟨some \d+, 0⟩ : Zig\.Ptr\) then Zig\.callMC "
                             r"\(heap_FixedBufferAllocator_alloc [^\n]*\) else Zig\.callC "
                             r"\(Zig\.extCall \(Ext\.call0 ", out.read_text()), version
            # The second interface: `std.Random`'s `fillFn`.
            result = run(exe, rnd, out, "--prefix", "rnd.", "--model-registry", registry(tmp, RANDOM))
            assert result.returncode == 0, result.stderr
            assert "Zig.callC (Zig.extCall (Ext.call0 " in out.read_text()
            checks += 4
        # Rejections (fail closed), on the 0.17.0 exports.
        lists = HERE / "air" / "0.17.0" / "lists"
        rnd = HERE / "air" / "0.17.0" / "rnd"
        base = ("--prefix", "lists.", *translated)
        fn = "fn (*anyopaque, usize, mem.Alignment, usize) ?[*]u8"
        cases = [
            (entry(ALLOC, function=fn), "exactly one of 'struct' and 'function'"),
            (entry(ALLOC, struct=None), "exactly one of 'struct' and 'function'"),
            (entry(ALLOC, premise="EXT-04"), "premise must be EXT-05"),
            (entry(ALLOC, contract="not an identifier"), "invalid Lean identifier"),
            (entry(ALLOC, struct="mem.Allocator"), "names no struct of the program with function-pointer fields"),
            (entry(ALLOC, struct=None, function="fn (u8) u8"), "opens no call through a pointer"),
            ({**ALLOC, "interfaces": ALLOC["interfaces"] + [
                {"interface": "alloc", "function": fn, "contract": "C", "premise": "EXT-05"}]},
             "is opened twice"),
            ({**ALLOC, "interfaces": [{**ALLOC["interfaces"][0], "extra": 1}]}, "unsupported field 'extra'"),
        ]
        for value, message in cases:
            rejects(run(exe, lists, out, *base, "--model-registry", registry(tmp, value)), message)
            checks += 1
        # Another program's interface opens nothing here.
        rejects(run(exe, rnd, out, "--prefix", "rnd.", "--model-registry", registry(tmp, ALLOC)),
                "names no struct of the program")
        # The generated proof lemmas and certificates do not take `Ext` (yet): rejected.
        for flag, message in ((["--proof-api"], "does not support open interfaces"),
                              (["--air-certificate", str(Path(tmp) / "C.lean"),
                                "--air-certificate-import", "T"], "cannot be combined with model registries")):
            rejects(run(exe, lists, out, *base, "--model-registry", registry(tmp, ALLOC), *flag), message)
        checks += 3
    print(f"interfaces test_cli: {checks} checks passed")


if __name__ == "__main__":
    main(sys.argv[1])
