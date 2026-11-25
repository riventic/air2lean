#!/usr/bin/env python3
"""The C-ABI conversion at a bound extern call through the CLI and --diagnostics-json
(docs/c-frontend.md §libc boundary): what it converts, and the pairs it leaves rejected.
Usage: test_cli.py <air2lean>."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.17.1"
REJECTED = HERE / "air-reject" / "0.17.1"
FLAGS = ("--allocator-model", "translated", "--assume-weak-exports")


def stage(tmp, source, edits=None):
    """A copy of `source` in `tmp` with its export table: `edits` maps a function name to a
    JSON-editing function."""
    out = Path(tempfile.mkdtemp(dir=tmp))
    for path in source.glob("*.json"):
        data = json.loads(path.read_text())
        if edits and data["name"] in edits:
            edits[data["name"]](data)
        (out / path.name).write_text(json.dumps(data))
    shutil.copyfile(source / "export-table.air2lean", out / "export-table.air2lean")
    return out


def translate(exe, air, tmp, flags=FLAGS):
    out = Path(tmp) / "Out.lean"
    result = subprocess.run([exe, str(air), "-o", str(out), "--namespace", "T", *flags],
                            capture_output=True, text=True, timeout=120)
    return result, out


def rejects(exe, air, needle, tmp, flags=FLAGS):
    result, _ = translate(exe, air, tmp, flags)
    assert result.returncode == 1, (needle, result.returncode, result.stderr)
    assert needle in result.stderr, (needle, result.stderr)


def diagnostics(exe, air):
    result = subprocess.run([exe, "--diagnostics-json", str(air), *FLAGS], capture_output=True,
                            text=True, timeout=120)
    assert result.returncode == 1, result.stdout
    return {(d["code"], d["function"]): d["message"] for d in json.loads(result.stdout)["diagnostics"]}


def calls(data, symbol):
    """The instructions that call the extern `symbol`."""
    pending, found = list(data["body"]), []
    while pending:
        inst = pending.pop()
        if inst.get("callee", {}).get("extern") == symbol:
            found.append(inst)
        pending += inst.get("body", []) + inst.get("then", []) + inst.get("else", [])
        pending += [i for case in inst.get("cases", []) for i in case["body"]]
    assert found, symbol
    return found


def main(exe):
    with tempfile.TemporaryDirectory() as tmp:
        # The translate-c declarations bind to Zig's libc definitions through the conversion:
        # the sentinel and non-null of `[*:0]const c_char` (strcmp, strrchr, memrchr's result),
        # the alignment of `?[*]align(16) u8` (malloc_usable_size).
        result, out = translate(exe, AIR, tmp)
        assert result.returncode == 0, result.stderr
        text = out.read_text()
        for req in ("{ nonNull := true, align := 1, sentinel := some (0 : BitVec 8) }",
                    "Zig.abiPtrOpt ({ nonNull := false, align := 16, sentinel := none }"):
            assert req in text, req
        assert "zigc_c_string_strcmp (← Zig.callM (Zig.abiPtr" in text

        # Zig's libc defines its functions weakly: the binding needs EXT-07.
        rejects(exe, AIR, "extern function 'strcmp' has only the weak definition", tmp,
                flags=("--allocator-model", "translated"))

        # A sentinel the export does not record as a value is not converted.
        def no_sentinel_byte(d):
            for t in d["types"]:
                t.pop("sentinel_byte", None)
        rejects(exe, stage(tmp, AIR, {"c.string.strcmp": no_sentinel_byte}),
                "extern function 'strcmp' differs from its definition 'zigc:c.string.strcmp' in its "
                "parameter 0 type, which the C-ABI conversion does not cover: the target type has a "
                "sentinel without an exported byte value", tmp)

        # A function that calls the definition directly beside the converted extern call: the
        # rename would make the two calls one callee with two signatures.
        def direct_too(d):
            calls(d, "strcmp")[0]["callee"] = {"ty": 10, "func": "c.string.strcmp", "module": "zigc",
                                               "noreturn": False}
        rejects(exe, stage(tmp, AIR, {"abi.cmp_case": direct_too}),
                "which this function also calls without it (CALLEE_AMBIGUOUS)", tmp)

        # A non-pointer difference stays rejected (the conversion is for pointers only).
        def wider_result(d):
            d["types"].append({"k": "int", "signed": False, "bits": 64, "abi_size": 8, "abi_align": 8})
            for inst in calls(d, "strcmp"):
                inst["ty"] = len(d["types"]) - 1
            next(e for e in d["externs"] if e["name"] == "strcmp")["ret"] = len(d["types"]) - 1
        rejects(exe, stage(tmp, AIR, {"abi.cmp_case": wider_result}),
                "in its result type, which the C-ABI conversion does not cover", tmp)

        # The pairs the conversion leaves rejected (rejected.c): a function-pointer parameter
        # (bsearch's comparator), the 4-byte sentinel of wcschr, and a call through a pointer to
        # strcmp, which converts nothing (the indirect call's signature check).
        found = diagnostics(exe, REJECTED)
        search = found[("CALLEE_EXTERN_UNBOUND", "rejected.search")]
        assert "'bsearch' differs from its definition 'zigc:c.stdlib.bsearch' in its parameter 4 type" in search, search
        assert "is a function pointer" in search, search
        wide = found[("CALLEE_EXTERN_UNBOUND", "rejected.has_wide")]
        assert "'wcschr' differs from its definition 'zigc:c.wchar.wcschr'" in wide, wide
        assert "a sentinel without an exported byte value" in wide, wide
        pointer = found[("SIGNATURE_FAILURE", "rejected.via_pointer")]
        assert "callee 'zigc:c.string.strcmp' has an incompatible argument 0 type" in pointer, pointer
    print("extern-abi test_cli: ok")


if __name__ == "__main__":
    main(sys.argv[1])
