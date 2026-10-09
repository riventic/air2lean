#!/usr/bin/env python3
"""B1 noreturn variants: CLI rejections for a root-built translator.

Every case edits one function of the committed 0.16.0 export (`air/0.16.0`) or uses the
committed `reject.zig` export (`air-reject/`), then checks that the translation fails with
the expected message and code (CLI and `--diagnostics-json`) and leaves its output untouched:

* an instruction that activates, reads or points to a `noreturn` variant (`set_union_tag`,
  `struct_field_ptr`, `struct_field_val`, `union_init`) and a union constant whose active
  variant is `noreturn`;
* a union whose fields are all `noreturn`, and an untagged union with one;
* layout: an exporter size that differs from the model's (the tag and the inhabited
  payloads, the `noreturn` variant adding no bytes), also for a union inside a struct, and the
  real exports of `reject.zig`: 0.16.0 stores a union with one inhabited variant without a
  tag, alone and inside a struct; 0.15.2 stores the tag (its struct case translates) but
  gives the union alone no layout.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"
PREFIX = "noreturn_variants."
# A value in memory that the model cannot encode: at an escaping local or at an access.
MEMORY = ("MEMORY_FAILURE", "INSTRUCTION_FAILURE")


def invoke(binary, *argv):
    return subprocess.run([str(binary), *map(str, argv)], capture_output=True, text=True,
                          timeout=120, check=False)


def load(name):
    return json.loads((AIR / f"{PREFIX}{name}.json").read_text())


def type_id(document, **match):
    """The id of the first type entry with every `match` item."""
    for index, ty in enumerate(document["types"]):
        if all(ty.get(k) == v for k, v in match.items()):
            return index
    raise AssertionError(f"no type {match} in {document['name']}")


def walk(body):
    for inst in body:
        yield inst
        for key in ("body", "then", "else"):
            if isinstance(inst.get(key), list):
                yield from walk(inst[key])
        for case in inst.get("cases", []):
            yield from walk(case["body"])


def find(document, tag):
    found = next((i for i in walk(document["body"]) if i["tag"] == tag), None)
    assert found, (tag, document["name"])
    return found


def reject(binary, air, codes, marker, prefix=PREFIX):
    """Translating `air` fails with `marker` (a code in `codes`); the output is left untouched."""
    with tempfile.TemporaryDirectory(prefix="air2lean-noreturn-variants-") as tmp:
        out = Path(tmp) / "Gen.lean"
        out.write_text("KEEP\n")
        result = invoke(binary, air, "-o", out, "--namespace", "N", "--prefix", prefix)
        assert result.returncode == 1 and marker in result.stderr, (marker, result.returncode,
                                                                    result.stderr)
        assert out.read_text() == "KEEP\n", "a rejected input replaced the output"
    report = invoke(binary, "--diagnostics-json", air)
    assert report.returncode == 1 and report.stderr == "", report
    found = [d for d in json.loads(report.stdout)["diagnostics"] if marker in d["message"]]
    assert found, (marker, report.stdout)
    for d in found:
        assert d["code"] in codes, d
    return 1


def mutant(binary, name, edit, codes, marker):
    """Reject the export of `name` after `edit(document)`."""
    document = load(name)
    edit(document)
    with tempfile.TemporaryDirectory(prefix="air2lean-noreturn-variants-air-") as tmp:
        (Path(tmp) / f"{PREFIX}{name}.json").write_text(json.dumps(document))
        return reject(binary, tmp, codes, marker)


def set_enum(document, tag, value):
    find(document, tag)["args"][1]["enum"] = value


def to_index(document, tag, new_tag, index):
    inst = find(document, tag)
    inst["tag"] = new_tag
    inst["index"] = index


def union_init(document):
    # `mk` builds `.{ .a = x }` in its result pointer; build `.{ .b = x }` with `union_init`.
    u = type_id(document, k="union", name=f"{PREFIX}U")
    never = type_id(document, k="noreturn")
    document["body"] = [
        {"id": 0, "tag": "arg", "ty": document["params"][0], "param": 0},
        {"id": 1, "tag": "union_init", "ty": u, "args": [{"inst": 0}], "index": 1},
        {"id": 2, "tag": "ret_safe", "ty": never, "args": [{"inst": 1}]},
    ]


def layout(type_match, **changes):
    def edit(document):
        document["types"][type_id(document, **type_match)].update(changes)
    return edit


def only_noreturn(document):
    never = type_id(document, k="noreturn")
    for field in document["types"][type_id(document, k="union", name=f"{PREFIX}U")]["fields"]:
        field["ty"] = never


def check(binary):
    variant = "the noreturn variant 'b' of union 'noreturn_variants.U'"
    checks = 0
    checks += mutant(binary, "mk", lambda d: set_enum(d, "set_union_tag", "1"),
                     ("INSTRUCTION_FAILURE",), f"set_union_tag to {variant}")
    checks += mutant(binary, "mk", lambda d: to_index(d, "struct_field_ptr_index_0",
                                                      "struct_field_ptr", 1),
                     ("INSTRUCTION_FAILURE",), f"a pointer to {variant}")
    checks += mutant(binary, "get", lambda d: to_index(d, "struct_field_val",
                                                       "struct_field_val", 1),
                     ("INSTRUCTION_FAILURE",), f"a read of {variant}")
    checks += mutant(binary, "mk", union_init, ("INSTRUCTION_FAILURE",), f"union_init of {variant}")
    # `setMode`'s `.escape_codes` constant (tag 1) as `windows_api` (tag 2).
    checks += mutant(binary, "setMode",
                     lambda d: find(d, "cond_br")["then"][0]["args"][0]["utag"].update(enum="2"),
                     ("AIR_DECODE",), "union constant with the noreturn variant 'windows_api' active")
    checks += mutant(binary, "get", only_noreturn, ("TYPE_FAILURE",),
                     "union 'noreturn_variants.U' has only noreturn fields")
    checks += mutant(binary, "get",
                     lambda d: d["types"][type_id(d, k="union", name=f"{PREFIX}U")].pop("tag"),
                     ("TYPE_FAILURE",), "union 'noreturn_variants.U' (auto, no tag) has a noreturn field")
    # The model's `U` is 8 bytes, aligned to 4: a `u8` tag at byte 4 after the `u32` payload.
    checks += mutant(binary, "readU", layout(dict(k="union", name=f"{PREFIX}U"), abi_size=12),
                     ("INSTRUCTION_FAILURE",), "size 8 and alignment 4, the compiler 12 and 4")
    # `Io.Terminal.Mode` is its 1-byte tag: `windows_api` adds no payload.
    checks += mutant(binary, "setMode", layout(dict(k="union", name="Io.Terminal.Mode"), abi_size=2),
                     ("INSTRUCTION_FAILURE",), "size 1 and alignment 1, the compiler 2 and 1")
    # Inside `Holder`, whose own size still agrees.
    checks += mutant(binary, "holderRoundTrip",
                     layout(dict(k="union", name="Io.Terminal.Mode"), abi_size=2), MEMORY,
                     "union 'Io.Terminal.Mode' size 1 and alignment 1, the compiler 2 and 1")
    # Real exports of `reject.zig`. 0.16.0 stores `One` without a tag (2 bytes), the model with
    # one (4): rejected alone and inside `Pair`, whose own size agrees. 0.15.2 stores the tag
    # (4 bytes): `Pair` translates, but the export of `memOne` gives `One` no layout, which is
    # rejected, never guessed.
    for version, root, marker in (("0.16.0", "One", "size 4 and alignment 2, the compiler 2 and 2"),
                                  ("0.16.0", "Pair", "size 4 and alignment 2, the compiler 2 and 2"),
                                  ("0.15.2", "One", "has no layout in the AIR file"),
                                  ("0.15.2", "Pair", None)):
        checks += reject_export(binary, version, root, marker)
    return checks


def reject_export(binary, version, root, marker):
    """`mem<root>` and `read<root>` of `reject.zig`'s export for `version`: rejected with
    `marker`, or translated if `marker` is `None`."""
    with tempfile.TemporaryDirectory(prefix="air2lean-noreturn-variants-reject-") as tmp:
        for name in (f"mem{root}", f"read{root}"):
            (Path(tmp) / f"reject.{name}.json").write_bytes(
                (HERE / "air-reject" / version / f"reject.{name}.json").read_bytes())
        if marker is not None:
            return reject(binary, tmp, MEMORY, marker, prefix="reject.")
        result = invoke(binary, tmp, "-o", Path(tmp) / "Gen.lean", "--namespace", "N",
                        "--prefix", "reject.")
        assert result.returncode == 0, (version, root, result.stderr)
        return 1


def main():
    if len(sys.argv) != 2:
        print("usage: test_cli.py TRANSLATOR", file=sys.stderr)
        return 2
    print(f"noreturn-variants CLI: {check(Path(sys.argv[1]))} checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
