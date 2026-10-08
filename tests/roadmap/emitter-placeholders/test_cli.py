#!/usr/bin/env python3
"""MM-6 regressions (docs/architecture-audit/memory-model.md): no emitter placeholder succeeds.

Every input below passed `Check.lean` before the fix and reached an emitter arm that wrote
`panic!` or `pure default`, a successful no-op in the logic, or an arm that wrote plausible but
wrong code (an identity, a wrong item count, a wrong field offset). Each must now be rejected by a
checker rule (exit 1, output untouched, the same rule in `--diagnostics-json`), never by the
post-emission `EMITTER_PLACEHOLDER` backstop, which is for arms nobody has found yet.

usage: test_cli.py [<air2lean binary>]   (default: .lake/build/bin/air2lean)
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
# A real 0.16.0 export of `@reduce(.Or, v == zero)`, hand-edited to `.Add` (trust-chain audit,
# finding 6). Its profile is reused by every synthetic case.
REDUCE = ROOT / "tests/roadmap/architecture-audit/trust-chain/reduce-bool-handedit/air"
BASE = json.loads((REDUCE / "red.anyLane.json").read_text())


def ptr(child, size="one", align=4):
    return {"k": "ptr", "size": size, "const": False, "child": child, "ptr_align": align,
            "volatile": False, "allowzero": False, "sentinel": False, "host_size": 0,
            "abi_size": 8, "abi_align": 8}


U32 = {"k": "int", "signed": False, "bits": 32, "abi_size": 4, "abi_align": 4}
U8 = {"k": "int", "signed": False, "bits": 8, "abi_size": 1, "abi_align": 1}
BOOL = {"k": "bool", "abi_size": 1, "abi_align": 1}
VOID = {"k": "void", "abi_size": 0, "abi_align": 1}
NORET = {"k": "noreturn"}
# Types 0..3 of every case; case-specific types start at 4.
COMMON = [U32, BOOL, VOID, NORET]
F32X4 = {"k": "vector", "len": 4, "child": 5, "abi_size": 16, "abi_align": 16}
F32 = {"k": "float", "bits": 32, "abi_size": 4, "abi_align": 4}
U32X2 = {"k": "vector", "len": 2, "child": 0, "abi_size": 8, "abi_align": 8}
STRUCT = {"k": "struct", "name": "probe.S", "layout": "auto",
          "fields": [{"name": "x", "ty": 0, "offset": 0}], "abi_size": 4, "abi_align": 4}
UNION = {"k": "union", "name": "probe.U", "layout": "extern", "fields": [{"name": "x", "ty": 0}],
         "abi_size": 4, "abi_align": 4}
TAGGED = {"k": "union", "name": "probe.TU", "layout": "auto", "tag": 6,
          "fields": [{"name": "x", "ty": 0}, {"name": "y", "ty": 0}], "abi_size": 8, "abi_align": 4}
TAG = {"k": "enum", "name": "probe.T", "tag": 7, "exhaustive": True,
       "fields": [{"name": "x", "value": "0"}, {"name": "y", "value": "1"}], "abi_size": 1, "abi_align": 1}
U1 = {"k": "int", "signed": False, "bits": 1, "abi_size": 1, "abi_align": 1}


def arg(i, ty, k=None):
    return {"id": i, "tag": "arg", "ty": ty, "param": i if k is None else k}


def ret(i, v):
    return {"id": i, "tag": "ret_safe", "ty": 3, "args": [v]}


VOID_VAL = {"ty": 2, "val": "{}"}


def case(name, params, result, body, extra):
    d = copy.deepcopy(BASE)
    d.update(name=f"probe.{name}", params=params, ret=result, body=body, types=COMMON + extra)
    return d


def one_op(name, params, result, op, extra):
    """`params` args, one instruction `op` (id = len(params)), returning its value."""
    k = len(params)
    body = [arg(i, t) for i, t in enumerate(params)] + [dict(op, id=k)]
    body.append(ret(k + 1, {"inst": k} if result != 2 else VOID_VAL))
    return case(name, params, result, body, extra)


# (name, document, the checker's message): one per emitter arm that the checker did not exclude.
CASES = [
    ("reduce: arithmetic on bool lanes (hand-edited export)", BASE,
     "`@reduce` operator is not defined for the vector's lane type"),
    ("reduce: bitwise on float lanes",
     one_op("reduceFloatAnd", [4], 5, {"tag": "reduce", "ty": 5, "args": [{"inst": 0}], "op": "And"},
            [F32X4, F32]),
     "`@reduce` operator is not defined for the vector's lane type"),
    ("shuffle: lane of a missing second operand",
     one_op("shuffleB", [4], 4, {"tag": "shuffle_one", "ty": 4, "args": [{"inst": 0}],
                                 "mask": [{"a": 0}, {"b": 0}]}, [U32X2]),
     "`@shuffle` mask lane reads a missing second operand or is out of range"),
    ("shuffle: lane out of range (`lanes[i]!` is `default`)",
     one_op("shuffleOob", [4], 4, {"tag": "shuffle_one", "ty": 4, "args": [{"inst": 0}],
                                   "mask": [{"a": 0}, {"a": 5}]}, [U32X2]),
     "`@shuffle` mask lane is out of range"),
    ("is_null_ptr of a non-optional",
     one_op("isNullPtr", [4], 1, {"tag": "is_non_null_ptr", "ty": 1, "args": [{"inst": 0}]}, [ptr(0)]),
     "`is_null_ptr` operand is not a pointer to an optional"),
    ("is_err_ptr of a non-error-union",
     one_op("isErrPtr", [4], 1, {"tag": "is_err_ptr", "ty": 1, "args": [{"inst": 0}]}, [ptr(0)]),
     "an error-union pointer op on a pointer to another type"),
    ("union_init of a struct",
     one_op("unionInitStruct", [0], 4, {"tag": "union_init", "ty": 4, "args": [{"inst": 0}],
                                        "index": 0}, [STRUCT]),
     "`union_init` result is not a union"),
    ("union_init with a field index out of range",
     one_op("unionInitIndex", [0], 4, {"tag": "union_init", "ty": 4, "args": [{"inst": 0}],
                                       "index": 3}, [UNION]),
     "`union_init` field index is out of range"),
    ("set_union_tag of a struct",
     one_op("setTagStruct", [4], 2, {"tag": "set_union_tag", "ty": 2,
                                     "args": [{"inst": 0}, {"ty": 0, "val": "0"}]}, [ptr(5), STRUCT]),
     "`set_union_tag` operand is not a pointer to a union"),
    ("set_union_tag of a union local with a runtime tag",
     case("setTagRuntime", [6], 2, [
         arg(0, 6), {"id": 1, "tag": "alloc", "ty": 4},
         {"id": 2, "tag": "set_union_tag", "ty": 2, "args": [{"inst": 1}, {"inst": 0}]},
         ret(3, VOID_VAL)], [ptr(5), TAGGED, TAG, U1]),
     "`set_union_tag` of a union local needs a constant tag that names a field"),
    ("memset through a many-pointer (no item count)",
     case("memsetMany", [4, 5], 2, [
         arg(0, 4), arg(1, 5),
         {"id": 2, "tag": "memset", "ty": 2, "args": [{"inst": 0}, {"inst": 1}]},
         ret(3, VOID_VAL)], [ptr(5, size="many", align=1), U8]),
     "`memset` destination is not a slice or a pointer to an array"),
    ("optional_payload_ptr_set of a non-optional (emitted as the identity)",
     one_op("optPayloadPtr", [4], 4, {"tag": "optional_payload_ptr_set", "ty": 4,
                                      "args": [{"inst": 0}]}, [ptr(0)]),
     "`optional_payload_ptr` operand is not a pointer to an optional"),
    ("memset through a many-pointer to arrays (the array length is not the item count)",
     case("memsetManyArrays", [4, 5], 2, [
         arg(0, 4), arg(1, 5),
         {"id": 2, "tag": "memset", "ty": 2, "args": [{"inst": 0}, {"inst": 1}]},
         ret(3, VOID_VAL)],
         [ptr(5, size="many", align=1),
          {"k": "array", "len": 4, "child": 6, "abi_size": 4, "abi_align": 1}, U8]),
     "`memset` destination is not a slice or a pointer to an array"),
    ("struct_field_ptr with a field index out of range (offset `getD 0`: the base itself)",
     one_op("fieldPtrIndex", [4], 6, {"tag": "struct_field_ptr", "ty": 6, "args": [{"inst": 0}],
                                      "index": 5}, [ptr(5), STRUCT, ptr(0)]),
     "`struct_field_ptr` field index has no known offset"),
    ("function body without a terminator",
     case("noTerminator", [0], 0, [arg(0, 0)], []),
     "a body ends without a terminator"),
    ("empty block body",
     case("emptyBlock", [0], 0, [arg(0, 0), {"id": 1, "tag": "block", "ty": 0, "body": []},
                                 ret(2, {"inst": 1})], []),
     "a body ends without a terminator"),
    ("empty cond_br branch",
     case("emptyBranch", [1], 0, [arg(0, 1), {"id": 1, "tag": "cond_br", "ty": 3, "args": [{"inst": 0}],
                                              "then": [], "else": [ret(2, {"ty": 0, "val": "1"})]}], []),
     "a body ends without a terminator"),
]


def translate(binary, document, directory):
    air = directory / "air"
    air.mkdir()
    (air / (document["name"] + ".json")).write_text(json.dumps(document))
    out = directory / "Gen.lean"
    out.write_text("sentinel\n")
    result = subprocess.run([str(binary), str(air), "-o", str(out), "--namespace", "Probe",
                             "--prefix", "probe."], text=True, capture_output=True, timeout=60)
    diagnostics = subprocess.run([str(binary), "--diagnostics-json", str(air)], text=True,
                                 capture_output=True, timeout=60)
    return result, out.read_text(), diagnostics


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else ROOT / ".lake/build/bin/air2lean")
    failures = []
    for name, document, message in CASES:
        with tempfile.TemporaryDirectory(prefix="air2lean-placeholders-") as d:
            result, output, diagnostics = translate(binary, document, Path(d))
            report = json.loads(diagnostics.stdout) if diagnostics.stdout.strip() else {}
            hits = [e for e in report.get("diagnostics", []) if message in e["message"]]
            problems = []
            replaced = output != "sentinel\n"
            if result.returncode != 1 or replaced:
                problems.append(f"CLI rc={result.returncode}, output replaced={replaced}")
            if message not in result.stderr:
                problems.append(f"CLI message: {result.stderr.strip()[:300]}")
            if "EMITTER_PLACEHOLDER" in result.stderr + diagnostics.stdout:
                problems.append("reached the emitter backstop instead of a checker rule")
            if diagnostics.returncode != 1 or report.get("status") != "rejected" or not hits:
                problems.append(f"diagnostics rc={diagnostics.returncode}: {diagnostics.stdout[:300]}")
            if problems:
                failures.append(f"{name}: " + "; ".join(problems))
    for failure in failures:
        print("FAIL", failure)
    if failures:
        return 1
    print(f"emitter placeholders: {len(CASES)} formerly fail-open inputs rejected by the checker")
    return 0


if __name__ == "__main__":
    sys.exit(main())
