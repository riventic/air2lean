#!/usr/bin/env python3
"""Extern-call binding rejections through the CLI and --diagnostics-json (docs/air-json.md
§Extern calls). Usage: test_cli.py <air2lean>."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"
TRUSTED = HERE / "air" / "0.16.0-trusted"
REGISTRY = json.loads((HERE / "registry.json").read_text())


def load(directory, name):
    return json.loads((directory / f"{name}.json").read_text())


def stage(tmp, source, edits=None, drop=()):
    """A copy of `source` in `tmp`: `edits` maps a file stem to a JSON-editing function."""
    out = Path(tempfile.mkdtemp(dir=tmp))
    for path in source.glob("*.json"):
        if path.stem in drop:
            continue
        data = json.loads(path.read_text())
        if edits and path.stem in edits:
            edits[path.stem](data)
        (out / path.name).write_text(json.dumps(data))
    return out


def translate(exe, air, registry=None, tmp=None):
    argv = [exe, str(air), "-o", str(Path(tmp) / "Out.lean"), "--namespace", "T"]
    if registry is not None:
        path = Path(tempfile.mkstemp(dir=tmp, suffix=".json")[1])
        path.write_text(json.dumps(registry))
        argv += ["--model-registry", str(path)]
    return subprocess.run(argv, capture_output=True, text=True, timeout=60)


def rejects(exe, air, needle, registry=None, tmp=None):
    result = translate(exe, air, registry, tmp)
    assert result.returncode == 1, (needle, result.returncode, result.stderr)
    assert needle in result.stderr, (needle, result.stderr)


def diagnostics(exe, air):
    result = subprocess.run([exe, "--diagnostics-json", str(air)], capture_output=True, text=True,
                            timeout=60)
    assert result.returncode == 1, result.stdout
    return json.loads(result.stdout)["diagnostics"]


def memset_call(data):
    """The (only) instruction that calls the extern `memset`."""
    pending = list(data["body"])
    while pending:
        inst = pending.pop()
        if inst.get("callee", {}).get("extern") == "memset":
            return inst
        pending += inst.get("body", []) + inst.get("then", []) + inst.get("else", [])
        pending += [i for case in inst.get("cases", []) for i in case["body"]]
    raise AssertionError("no memset call")


def first_extern(data):
    return data["externs"][0]


def main(exe):
    with tempfile.TemporaryDirectory() as tmp:
        # Bound to the export fn definitions: accepted (the committed translation, check.sh).
        assert translate(exe, AIR, tmp=tmp).returncode == 0

        # No definition and no model: CALLEE_EXTERN_UNBOUND names the symbol.
        no_def = stage(tmp, AIR, drop={"libc_ref.memset"})
        rejects(exe, no_def, "CALLEE_EXTERN_UNBOUND: extern function 'memset' has no definition", tmp=tmp)
        codes = [(d["code"], d["function"]) for d in diagnostics(exe, no_def)]
        assert ("CALLEE_EXTERN_UNBOUND", "extern_calls.fillSum") in codes, codes
        assert not any(code == "CALLEE_MISSING" for code, _ in codes), codes

        # Variadic externs are outside the subset.
        varargs = stage(tmp, AIR, {"extern_calls.fillSum": lambda d: first_extern(d).update(varargs=True)})
        rejects(exe, varargs, "extern function 'memset' is variadic", tmp=tmp)

        # The definition's calling convention must be the declared one.
        cc = stage(tmp, AIR, {"libc_ref.memset": lambda d: d["export"].update(cc="x86_64_win")})
        rejects(exe, cc, "is declared with calling convention", tmp=tmp)

        # A symbol defined twice in the AIR set is ambiguous.
        twice = stage(tmp, AIR, {"libc_ref.strlen": lambda d: d["export"].update(name="memset")})
        rejects(exe, twice, "is also exported by", tmp=tmp)

        # The definition's signature is checked like any direct call's: here the declared
        # result type (the call's, unused) differs from the definition's.
        def wider_result(d):
            d["types"].append({"k": "int", "signed": False, "bits": 64, "abi_size": 8, "abi_align": 8})
            memset_call(d)["ty"] = len(d["types"]) - 1
        rejects(exe, stage(tmp, AIR, {"extern_calls.fillSum": wider_result}),
                "callee 'libc_ref.memset' has an incompatible result type", tmp=tmp)

        # A call without an externs entry, and a noreturn extern call.
        no_entry = stage(tmp, AIR, {"extern_calls.fillSum": lambda d: d.pop("externs")})
        rejects(exe, no_entry, "extern callee 'memset' has no 'externs' entry", tmp=tmp)
        rejects(exe, stage(tmp, AIR, {"extern_calls.fillSum": lambda d: memset_call(d)["callee"].update(noreturn=True)}),
                "noreturn extern function 'memset'", tmp=tmp)

        # Trusted base: without the registry, abs (library c) is unbound.
        rejects(exe, TRUSTED, "extern function 'abs' (library 'c') has no definition", tmp=tmp)
        assert translate(exe, TRUSTED, REGISTRY, tmp).returncode == 0

        def registry(**changes):
            r = copy.deepcopy(REGISTRY)
            r["models"][0].update(changes)
            return r
        missing = copy.deepcopy(REGISTRY)
        del missing["models"][0]["extern"]
        rejects(exe, TRUSTED, "needs an 'extern' object", missing, tmp)
        rejects(exe, TRUSTED, "is not a premise ID",
                registry(extern={"library": "c", "premise": "posix"}), tmp)
        rejects(exe, TRUSTED, "another library than its registry model's",
                registry(extern={"library": None, "premise": "EXT-03"}), tmp)
        # Never by a Zig declaration name: a non-extern symbol cannot carry `extern`, and a
        # model for the bare name binds nothing.
        rejects(exe, TRUSTED, "is not an extern callee", registry(symbol="trusted.abs"), tmp)
        bare = copy.deepcopy(missing)
        bare["models"][0]["symbol"] = "abs"
        rejects(exe, TRUSTED, "CALLEE_EXTERN_UNBOUND: extern function 'abs'", bare, tmp)

        # A symbol the program defines cannot be bound to a model (the linker picks the definition).
        no_strlen = stage(tmp, AIR, drop={"libc_ref.strlen"})
        template_path = Path(tmp) / "template.json"
        subprocess.run([exe, str(no_strlen), "-o", str(template_path), "--namespace", "T",
                        "--model-registry-template"], check=True, timeout=60)
        template = json.loads(template_path.read_text())
        entry = template["models"][0]
        assert entry["symbol"] == "extern:strlen" and entry["extern"] == {"library": None}, entry
        entry["extern"]["premise"] = "EXT-03"
        for key in ("import", "implementation", "contract", "trust", "termination", "errors",
                    "effects", "dependencies"):
            entry[key] = REGISTRY["models"][0][key]
        rejects(exe, AIR, "is both defined by 'libc_ref.strlen' and bound to registry model", template, tmp)
    print("extern-calls test_cli: ok")


if __name__ == "__main__":
    main(sys.argv[1])
