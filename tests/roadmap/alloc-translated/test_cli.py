#!/usr/bin/env python3
"""CLI regressions for `--allocator-model translated`, for a root-built translator.

The retained compiler exports (air/0.16.0, provenance.json) are accepted only in translated
mode. Every admission is narrow: mutating one fact of an admitted program into the
neighbouring unsupported case fails closed with a stable message. Never builds or invokes
compilers.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"
TRANSLATED = ["--allocator-model", "translated"]


def load(program):
    return {p.name: json.loads(p.read_text()) for p in sorted((AIR / program).glob("*.json"))}


def run(binary, documents, flags, prefix):
    with tempfile.TemporaryDirectory(prefix="air2lean-alloc-translated-") as d:
        air = Path(d) / "air"
        air.mkdir()
        for name, document in documents.items():
            (air / name).write_text(json.dumps(document))
        out = Path(d) / "Gen.lean"
        result = subprocess.run([str(binary), str(air), "-o", str(out), "--namespace", "T",
                                 "--prefix", prefix, *flags],
                                text=True, capture_output=True, check=False, timeout=120)
        diagnostics = subprocess.run([str(binary), "--diagnostics-json", str(air), *flags],
                                     text=True, capture_output=True, check=False, timeout=120)
        return result, json.loads(diagnostics.stdout), out.exists()


def accept(binary, documents, prefix):
    result, report, written = run(binary, documents, TRANSLATED, prefix)
    assert result.returncode == 0 and written, result.stderr
    assert report["status"] == "checked" and report["diagnostics"] == [], report["diagnostics"][:3]


def reject(binary, documents, marker, prefix, flags=TRANSLATED):
    result, report, _ = run(binary, documents, flags, prefix)
    assert result.returncode == 1, (marker, result.stderr)
    assert marker in result.stderr, (marker, result.stderr)
    assert report["status"] == "rejected"
    assert any(marker in d["message"] for d in report["diagnostics"]), (marker, report["diagnostics"][:5])


def walk(body):
    for inst in body:
        yield inst
        for key in ("body", "then", "else"):
            if isinstance(inst.get(key), list):
                yield from walk(inst[key])
        for case in inst.get("cases", []):
            yield from walk(case.get("body", []))


def find(documents, prefix):
    names = [n for n in documents if n.startswith(prefix)]
    assert len(names) == 1, (prefix, names)
    return documents[names[0]]


def main(binary):
    page, fba = load("page-linux"), load("fba-linux")
    accept(binary, page, "page.")
    accept(binary, fba, "fba.")
    accept(binary, load("page-macos"), "page.")
    accept(binary, load("fba-macos"), "fba.")

    # Std mode (the default and the explicit flag) keeps the built-in allocator model: the
    # same AIR is rejected, never silently retranslated.
    for flags in ([], ["--allocator-model", "std"], ["--allocator-model=std"]):
        result, report, _ = run(binary, fba, flags, "fba.")
        assert result.returncode == 1 and report["status"] == "rejected", flags
    result, _, _ = run(binary, page, [], "page.")
    assert result.returncode == 1

    # Flag spelling.
    for flags, marker in ((["--allocator-model", "both"], "invalid --allocator-model"),
                          (TRANSLATED + TRANSLATED, "duplicate --allocator-model")):
        result, _, _ = run(binary, fba, flags, "fba.")
        assert result.returncode == 1 and marker in result.stderr, (flags, result.stderr)
    result, _, _ = run(binary, fba, ["--allocator-model=translated"], "fba.")
    assert result.returncode == 0, result.stderr

    # A translated function cannot reuse a trusted OS model name.
    clash = dict(page)
    clash["posix.mmap.json"] = dict(find(page, "debug.assert"), name="posix.mmap")
    reject(binary, clash, "conflicts with built-in std model 'posix.mmap'", "page.")

    # posix.mmap's result must admit OutOfMemory, the only error the OS model returns.
    mutated = json.loads(json.dumps(page))
    m = find(mutated, "heap.PageAllocator.map.json")
    for inst in walk(m["body"]):
        if inst.get("tag") == "call" and inst["callee"].get("func") == "posix.mmap":
            error_set = m["types"][m["types"][inst["ty"]]["error"]]
            error_set["errors"] = [e for e in error_set["errors"] if e != "OutOfMemory"]
    reject(binary, mutated, "model callee 'posix.mmap' has an incompatible", "page.")

    # A weak compare-exchange of a pointer value stays outside the subset.
    mutated = json.loads(json.dumps(page))
    m = find(mutated, "heap.PageAllocator.map.json")
    for inst in walk(m["body"]):
        if inst.get("tag") == "cmpxchg_strong":
            inst["tag"] = "cmpxchg_weak"
    reject(binary, mutated, "an atomic op on a type other than an integer", "page.")

    # The integer sentinel: only a nonzero, aligned address is admitted.
    for address, in ((0,), (3,)):
        mutated = json.loads(json.dumps(fba))
        hit = False
        for document in mutated.values():
            for inst in walk(document["body"]):
                for arg in inst.get("args", []):
                    payload = arg.get("payload", {}) if isinstance(arg, dict) else {}
                    pointer = payload.get("ptr") if isinstance(payload, dict) else None
                    if isinstance(pointer, dict) and pointer.get("unsupported") == "int":
                        pointer["off"] = address
                        hit = True
        assert hit
        reject(binary, mutated, "a pointer constant without a global (int)", "fba.")

    # `@returnAddress` must be a usize.
    mutated = json.loads(json.dumps(fba))
    alloc = find(mutated, "mem.Allocator.alloc__anon_")
    alloc["types"].append({"k": "bool", "abi_size": 1, "abi_align": 1})
    for inst in walk(alloc["body"]):
        if inst.get("tag") == "ret_addr":
            inst["ty"] = len(alloc["types"]) - 1
    reject(binary, mutated, "@returnAddress must have type usize", "fba.")
    print("alloc-translated CLI regressions passed")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
