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


def translate(exe, air, registry=None, tmp=None, flags=()):
    argv = [exe, str(air), "-o", str(Path(tmp) / "Out.lean"), "--namespace", "T", *flags]
    if registry is not None:
        path = Path(tempfile.mkstemp(dir=tmp, suffix=".json")[1])
        path.write_text(json.dumps(registry))
        argv += ["--model-registry", str(path)]
    return subprocess.run(argv, capture_output=True, text=True, timeout=60)


def rejects(exe, air, needle, registry=None, tmp=None, flags=()):
    result = translate(exe, air, registry, tmp, flags)
    assert result.returncode == 1, (needle, result.returncode, result.stderr)
    assert needle in result.stderr, (needle, result.stderr)


def diagnostics(exe, air, flags=()):
    result = subprocess.run([exe, "--diagnostics-json", str(air), *flags], capture_output=True,
                            text=True, timeout=60)
    assert result.returncode == 1, result.stdout
    return json.loads(result.stdout)["diagnostics"]


WEAK = ("--assume-weak-exports",)
# weak_exports.zig as the patched Zig 0.17.1 exports it: the function files and the
# compilation's export table (the exporter's own record of the two `@export` symbols).
WEAK_AIR = HERE / "air" / "0.17.1-weak"


def exporter_table_cases(exe, tmp):
    """The export table that the exporter writes (not a hand-made one)."""
    table = json.loads((WEAK_AIR / "export-table.air2lean").read_text())
    records = {r["name"]: (r["linkage"], r["function"] and r["function"]["name"]) for r in table["exports"]}
    assert records == {"weak_clamp_add": ("weak", "weak_exports.clampAdd"),
                       "strong_twice": ("strong", "weak_exports.twice"),
                       "viaWeak": ("strong", "weak_exports.viaWeak"),
                       "viaStrong": ("strong", "weak_exports.viaStrong")}, records

    def staged(drop=()):
        out = stage(tmp, WEAK_AIR, drop=drop)
        shutil.copyfile(WEAK_AIR / "export-table.air2lean", out / "export-table.air2lean")
        return out
    # The weak definition binds under EXT-07 only; the strong `@export` needs no premise.
    rejects(exe, staged(), "extern function 'weak_clamp_add' has only the weak definition "
            "'weak_exports.clampAdd'", tmp=tmp)
    assert translate(exe, staged(drop={"weak_exports.viaWeak"}), tmp=tmp).returncode == 0
    result = translate(exe, staged(), tmp=tmp, flags=WEAK)
    assert result.returncode == 0, result.stderr
    text = (Path(tmp) / "Out.lean").read_text()
    assert '"admission":"weak-exports"' in text.splitlines()[0].replace(" ", ""), text.splitlines()[0]
    # Without the table neither symbol has a definition; without the definition's AIR it
    # cannot bind.
    rejects(exe, stage(tmp, WEAK_AIR), "has no definition in the program", tmp=tmp, flags=WEAK)
    rejects(exe, staged(drop={"weak_exports.clampAdd"}),
            "is defined by 'weak_exports.clampAdd', which has no AIR in the set", tmp=tmp, flags=WEAK)


def export_table(air, records, version="0.16.0"):
    """Write the compilation's export table (docs/air-json.md §Export table) beside `air`'s
    files. A record is (symbol, linkage, function name or None)."""
    exports = [{"name": name, "linkage": linkage, "visibility": "hidden",
                "function": fn and {"module": "root", "name": fn, "cc": "x86_64_sysv"}}
               for name, linkage, fn in records]
    (air / "export-table.air2lean").write_text(json.dumps(
        {"schema": 12, "zig_version": version, "exports": exports}))
    return air


def by_table(tmp, records, drop=(), keep_export=(), version="0.16.0"):
    """The AIR set with `memset` and `strlen` defined through the export table only (as
    `@export` defines a symbol): the functions' own `export` is removed."""
    def strip(d):
        del d["export"]
    edits = {stem: strip for stem in ("libc_ref.memset", "libc_ref.strlen") if stem not in keep_export}
    return export_table(stage(tmp, AIR, edits, drop), records, version)


def export_table_cases(exe, tmp):
    """`@export` definitions (the export table) and the weak-definition premise EXT-07."""
    strong = [("memset", "strong", "libc_ref.memset"), ("strlen", "strong", "libc_ref.strlen")]
    weak = [("memset", "weak", "libc_ref.memset"), ("strlen", "weak", "libc_ref.strlen")]
    # Without the records the symbols have no definition.
    rejects(exe, by_table(tmp, []), "extern function 'memset' has no definition", tmp=tmp)
    # A strong `@export` binds like an `export fn`; so does a record that repeats one.
    assert translate(exe, by_table(tmp, strong), tmp=tmp).returncode == 0
    assert translate(exe, by_table(tmp, strong, keep_export=("libc_ref.memset", "libc_ref.strlen")),
                     tmp=tmp).returncode == 0
    # A weak definition binds only under EXT-07, which the header then records.
    weak_air = by_table(tmp, weak)
    rejects(exe, weak_air, "extern function 'memset' has only the weak definition 'libc_ref.memset'", tmp=tmp)
    codes = [(d["code"], d["function"]) for d in diagnostics(exe, weak_air)]
    assert ("CALLEE_EXTERN_UNBOUND", "extern_calls.fillSum") in codes, codes
    result = translate(exe, weak_air, tmp=tmp, flags=WEAK)
    assert result.returncode == 0, result.stderr
    assert '"admission":"weak-exports"' in (Path(tmp) / "Out.lean").read_text().replace(" ", "")
    result = subprocess.run([exe, "--diagnostics-json", str(weak_air), *WEAK], capture_output=True,
                            text=True, timeout=60)
    assert result.returncode == 0 and json.loads(result.stdout)["status"] == "checked", result.stdout
    # The premise does not bind what is not one function with AIR: two definitions (a weak one
    # beside the `export fn`, or two weak ones), a symbol that is not a function, a function
    # without AIR in the set.
    both = by_table(tmp, [("memset", "weak", "libc_ref.strlen")] + strong[1:], keep_export=("libc_ref.memset",))
    rejects(exe, both, "has several definitions ('libc_ref.memset', 'libc_ref.strlen') (CALLEE_AMBIGUOUS)",
            tmp=tmp, flags=WEAK)
    rejects(exe, by_table(tmp, weak + [("memset", "weak", "libc_ref.strlen")]),
            "has several definitions", tmp=tmp, flags=WEAK)
    rejects(exe, by_table(tmp, [("memset", "strong", None)] + weak[1:]),
            "is defined by the compilation, but not as a function", tmp=tmp, flags=WEAK)
    rejects(exe, by_table(tmp, weak, drop={"libc_ref.memset"}),
            "is defined by 'libc_ref.memset', which has no AIR in the set", tmp=tmp, flags=WEAK)
    # The calling convention and the signature are checked as for an `export fn`.
    other_cc = by_table(tmp, weak)
    table = json.loads((other_cc / "export-table.air2lean").read_text())
    table["exports"][0]["function"]["cc"] = "x86_64_win"
    (other_cc / "export-table.air2lean").write_text(json.dumps(table))
    rejects(exe, other_cc, "is declared with calling convention", tmp=tmp, flags=WEAK)
    # A variadic extern stays outside the subset.
    variadic = stage(tmp, AIR, {"extern_calls.fillSum": lambda d: first_extern(d).update(varargs=True),
                                "libc_ref.memset": lambda d: d.pop("export")})
    rejects(exe, export_table(variadic, weak), "extern function 'memset' is variadic", tmp=tmp, flags=WEAK)
    # The table is the compilation's: another Zig version's, or a linkage the translator does
    # not know, is rejected.
    rejects(exe, by_table(tmp, weak, version="0.17.1"), "export-table.air2lean is of Zig 0.17.1",
            tmp=tmp, flags=WEAK)
    rejects(exe, by_table(tmp, [("memset", "link_once", "libc_ref.memset")] + weak[1:]),
            "has the unknown linkage 'link_once'", tmp=tmp, flags=WEAK)


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
        rejects(exe, twice, "has several definitions ('libc_ref.memset', 'libc_ref.strlen')", tmp=tmp)
        # ... but only for a call that needs the symbol.
        no_call = stage(tmp, AIR, {"libc_ref.strlen": lambda d: d["export"].update(name="memset")},
                        drop={"extern_calls.fillSum", "extern_calls.greetLen"})
        assert translate(exe, no_call, tmp=tmp).returncode == 0

        # The externs entry must describe each call.
        rejects(exe, stage(tmp, AIR, {"extern_calls.fillSum": lambda d: first_extern(d)["params"].pop()}),
                "does not match its 'externs' entry", tmp=tmp)

        # The declaration must have the definition's signature up to the C-ABI conversion of
        # pointers: here the declared result type (the call's, unused) differs from the
        # definition's.
        def wider_result(d):
            d["types"].append({"k": "int", "signed": False, "bits": 64, "abi_size": 8, "abi_align": 8})
            memset_call(d)["ty"] = first_extern(d)["ret"] = len(d["types"]) - 1
        rejects(exe, stage(tmp, AIR, {"extern_calls.fillSum": wider_result}),
                "extern function 'memset' differs from its definition 'libc_ref.memset' in its "
                "result type", tmp=tmp)
        # ... and a parameter type (a `u64` for `memset`'s `c_int`).
        def wider_param(d):
            d["types"].append({"k": "int", "signed": False, "bits": 64, "abi_size": 8, "abi_align": 8})
            first_extern(d)["params"][1] = len(d["types"]) - 1
        rejects(exe, stage(tmp, AIR, {"extern_calls.fillSum": wider_param}),
                "differs from its definition 'libc_ref.memset' in its parameter 1 type", tmp=tmp)
        # A pointer that differs as the C ABI allows is converted at the call (docs/c-frontend.md
        # §libc boundary): `strlen` declared with translate-c's `[*c]const u8` for the
        # definition's `[*:0]const u8` checks non-null and the sentinel.
        def c_pointer(d):
            d["types"][first_extern(d)["params"][0]].update(size="c", allowzero=True, sentinel=False)
            d["types"][first_extern(d)["params"][0]].pop("sentinel_byte")
        result = translate(exe, stage(tmp, AIR, {"extern_calls.greetLen": c_pointer}), tmp=tmp)
        assert result.returncode == 0, result.stderr
        assert ("libc_ref_strlen (← Zig.callM (Zig.abiPtr ({ nonNull := true, align := 1, sentinel := "
                "some (0 : BitVec 8) } : Zig.AbiPtrReq)") in (Path(tmp) / "Out.lean").read_text()

        # A call without an externs entry, and a noreturn extern call.
        no_entry = stage(tmp, AIR, {"extern_calls.fillSum": lambda d: d.pop("externs")})
        rejects(exe, no_entry, "extern function 'memset' is bound to neither", tmp=tmp)
        other_entry = stage(tmp, AIR, {"extern_calls.fillSum": lambda d: first_extern(d).update(name="bzero")})
        rejects(exe, other_entry, "extern callee 'memset' has no 'externs' entry", tmp=tmp)
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

        export_table_cases(exe, tmp)
        exporter_table_cases(exe, tmp)
    print("extern-calls test_cli: ok")


if __name__ == "__main__":
    main(sys.argv[1])
