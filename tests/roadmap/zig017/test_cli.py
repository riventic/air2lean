#!/usr/bin/env python3
"""Zig 0.17.0 translator regressions on hand-written, 0.17-shaped AIR (not compiler output).

Usage: test_cli.py BINARY [--elaborate]

1. `air/`: every new or renamed 0.17.0 tag that the subset admits translates; with
   `--elaborate` the generated Lean is checked by `lake env lean` together with kernel-checked
   semantic examples (`@divCeil`, `@fromBackingInt`'s enum check, ...).
2. `reject/`: each file fails with exit status 1 and the stable diagnostic in `expect.json`, and
   leaves the output file untouched.
3. Upgrade: the committed 0.16.0 golden AIR of every example, rewritten to 0.17.0 spelling (tag
   renames, the `bitcast` split, `bool_and`/`bool_or` as `bit_and`/`bit_or`, the `safe` build
   mode), translates to the same Lean as the 0.16.0 AIR, apart from the profile's version.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SEMANTICS = """
open Zig017 in
section
example : divCeilU 7#32 2#32 = pure 4#32 := by rfl
example : divCeilU 6#32 3#32 = pure 2#32 := by rfl
example : divCeilU 0#32 5#32 = pure 0#32 := by rfl
example : divCeilU 4294967295#32 2#32 = pure 2147483648#32 := by rfl
example : divCeilU 1#32 0#32 = throw .divByZero := by rfl
example : divCeilI 5#8 3#8 = pure 2#8 := by rfl
example : divCeilI (-5#8) 3#8 = pure (-1#8) := by rfl
example : divCeilI 5#8 (-3#8) = pure (-1#8) := by rfl
example : divCeilI (-5#8) (-3#8) = pure 2#8 := by rfl
example : divCeilI (-6#8) 3#8 = pure (-2#8) := by rfl
example : divCeilI (-128#8) (-1#8) = throw .overflow := by rfl
example : divCeilI 1#8 0#8 = throw .divByZero := by rfl
example : fromBacking 1#8 = pure .green := by rfl
example : fromBacking 3#8 = throw .panic := by rfl
example : toBacking .blue = pure 2#8 := by rfl
example : enumFromInt 2#32 = pure .blue := by rfl
example : enumFromInt 258#32 = throw .panic := by rfl
example : narrow 300#32 = throw .overflow := by rfl
example : widen 200#8 = pure 200#32 := by rfl
example : both true false = pure false := by rfl
example : both false true = pure true := by rfl
example : field { a := 1#16, b := 7#32 } = pure 7#32 := by rfl
example : twice 21#32 = pure 42#32 := by rfl
end
"""


def translate(binary, air, output, namespace, prefix=None, extra=()):
    command = [str(binary), str(air), "-o", str(output), "--namespace", namespace, *extra]
    if prefix:
        command += ["--prefix", prefix]
    return subprocess.run(command, text=True, capture_output=True, check=False, timeout=120)


def positive(binary, elaborate):
    with tempfile.TemporaryDirectory(prefix="air2lean-zig017-") as directory:
        output = Path(directory) / "Gen.lean"
        result = translate(binary, HERE / "air", output, "Zig017", "zig017.")
        assert result.returncode == 0, result.stderr
        text = output.read_text()
        header = json.loads(text.splitlines()[0].removeprefix("-- air2lean-profile: "))
        assert header["profile"]["zig_version"] == "0.17.0", header
        # 0.17.0's `safe` build mode keeps the version-independent profile spelling.
        assert header["profile"]["build_mode"] == "ReleaseSafe", header
        assert "__func_" not in text, "a 0.17.0 instance name leaked into the translation"
        for needle in ("Zig.divCeil false", "Zig.divCeil true", "Zig.Float.divCeil",
                       "Zig.Vec.map2M (fun x0 x1 => Zig.divCeil true x0 x1)",
                       "Zig.enumOf (Color.ofInt?", "(p0 && p1)", "(i2 || p1)", "(p0 &&& p1)",
                       "Zig.load (BitVec 32) 4 i1", "Zig.Float.toBits? p0",
                       # `&v[i]` on a whole-byte lane reads as 0.16.0's element pointer.
                       "(p0.elem 4 (2 : BitVec 64))", "(p0.elem 4 (1 : BitVec 64))",
                       # A `__func_<n>` generic instance gets the stable `__anon_<k>` name.
                       "def double__anon_1"):
            assert needle in text, f"missing {needle!r}"
        checks = 1
        if elaborate:
            checked = Path(directory) / "Zig017Check.lean"
            checked.write_text(text + SEMANTICS)
            run = subprocess.run(["lake", "env", "lean", str(checked)], cwd=ROOT, text=True,
                                 capture_output=True, check=False, timeout=1800)
            assert run.returncode == 0, run.stdout + run.stderr
            checks += SEMANTICS.count("example")
        return checks


def rejections(binary):
    expect = json.loads((HERE / "reject" / "expect.json").read_text())
    files = sorted(p.stem for p in (HERE / "reject").glob("*.json") if p.name != "expect.json")
    assert files == sorted(expect), "every rejection fixture needs exactly one expected diagnostic"
    for name, fragment in sorted(expect.items()):
        with tempfile.TemporaryDirectory(prefix="air2lean-zig017-reject-") as directory:
            air = Path(directory) / "air"
            air.mkdir()
            (air / f"{name}.json").write_text((HERE / "reject" / f"{name}.json").read_text())
            output = Path(directory) / "Gen.lean"
            output.write_text("sentinel\n")
            result = translate(binary, air, output, "Reject")
            assert result.returncode == 1, (name, result.returncode, result.stderr)
            assert fragment in result.stderr, (name, fragment, result.stderr)
            assert output.read_text() == "sentinel\n", f"{name}: rejected input replaced output"
    return len(expect)


def pointer_like(types, ty):
    t = types[ty]
    if t["k"] == "optional":
        t = types[t["child"]]
    return t["k"] == "ptr"


def upgrade_tag(doc, inst, producers):
    """The 0.17.0 spelling of a 0.16.0 instruction (`docs/zig-0.17-delta.md` §(a))."""
    tag, types = inst["tag"], doc["types"]
    renamed = {"intcast": "int_cast", "intcast_safe": "int_cast_safe",
               "struct_field_val": "agg_field_val", "bool_and": "bit_and", "bool_or": "bit_or"}
    if tag in renamed:
        return renamed[tag]
    if tag != "bitcast":
        return tag
    operand = inst["args"][0]
    source = operand.get("ty") if "inst" not in operand else producers.get(operand["inst"])
    if source is None:
        return "bit_cast_safe"
    src, dst = types[source]["k"], types[inst["ty"]]["k"]
    if pointer_like(types, source) and pointer_like(types, inst["ty"]):
        return "ptr_cast"
    if pointer_like(types, inst["ty"]):
        return "ptr_from_int"
    if pointer_like(types, source):
        return "int_from_ptr"
    if src in ("error_set", "error_union") and dst in ("error_set", "error_union"):
        return "error_cast"
    if src == "error_set":
        return "int_from_error"
    if dst == "error_set":
        return "error_from_int"
    return "bit_cast_safe"


def walk(body):
    for inst in body:
        yield inst
        for key in ("body", "then", "else"):
            yield from walk(inst.get(key, []))
        for case in inst.get("cases", []):
            yield from walk(case.get("body", []))


def upgraded(doc):
    doc = copy.deepcopy(doc)
    producers = {i["id"]: i.get("ty") for i in walk(doc["body"])}
    for inst in walk(doc["body"]):
        inst["tag"] = upgrade_tag(doc, inst, producers)
    doc["zig_version"] = "0.17.0"
    if "profile" in doc:
        doc["profile"]["zig_version"] = "0.17.0"
        doc["profile"]["build_mode"] = {"Debug": "debug", "ReleaseSafe": "safe", "ReleaseFast": "fast",
                                        "ReleaseSmall": "small"}[doc["profile"]["build_mode"]]
    return doc


def golden_set(example):
    files = {}
    for directory in (ROOT / "tests/golden" / example / "air", ROOT / "tests/golden/0.16.0" / example / "air",
                      ROOT / "tests/golden/0.16.0" / example / "air-linux"):
        for path in sorted(directory.glob("*.json")) if directory.is_dir() else ():
            files[path.name] = json.loads(path.read_text())
    if len({"profile" in doc for doc in files.values()}) > 1:
        # A golden set that mixes schema-12 and legacy files: compare it on the legacy profile.
        for doc in files.values():
            doc.pop("profile", None)
            doc["schema"] = min(doc["schema"], 11)
    return files


def as_version(doc, version):
    doc = copy.deepcopy(doc)
    doc["zig_version"] = version
    if "profile" in doc:
        doc["profile"]["zig_version"] = version
    return doc


def upgrades(binary):
    compared = 0
    for example in sorted(p.name for p in (ROOT / "tests/golden").iterdir() if (p / "air").is_dir()):
        files = golden_set(example)
        args_file = ROOT / "examples" / example / "translate.args"
        extra = args_file.read_text().split() if args_file.exists() else []
        namespace = example[0].upper() + example[1:]
        with tempfile.TemporaryDirectory(prefix="air2lean-zig017-upgrade-") as directory:
            directory = Path(directory)
            outputs = {}
            for version, rewrite in (("0.16.0", lambda d: as_version(d, "0.16.0")),
                                     ("0.17.0", lambda d: upgraded(as_version(d, "0.16.0")))):
                air = directory / version
                air.mkdir()
                for name, doc in files.items():
                    (air / name).write_text(json.dumps(rewrite(doc)))
                result = translate(binary, air, directory / f"{version}.lean", namespace, f"{example}.", extra)
                outputs[version] = (result.returncode, result.stderr,
                                    (directory / f"{version}.lean").read_text() if result.returncode == 0 else "")
            (old_rc, old_err, old), (new_rc, new_err, new) = outputs["0.16.0"], outputs["0.17.0"]
            if old_rc != 0:
                # The relabelled set is outside the translator's 0.16.0 scope; 0.17.0 must agree.
                assert new_rc == old_rc, (example, old_err, new_err)
                continue
            assert new_rc == 0, (example, new_err)
            old_head, _, old_body = old.partition("\n")
            new_head, _, new_body = new.partition("\n")
            assert new_head == old_head.replace('"zig_version":"0.16.0"', '"zig_version":"0.17.0"'), example
            assert new_body == old_body, f"{example}: 0.17.0 spelling changed the translation"
            compared += 1
    assert compared >= 19, f"only {compared} examples translated"
    return compared


def main():
    binary = Path(sys.argv[1]).resolve(strict=True)
    elaborate = "--elaborate" in sys.argv[2:]
    checks = positive(binary, elaborate)
    checks += rejections(binary)
    checks += upgrades(binary)
    print(f"{checks} Zig 0.17.0 translator checks passed")


if __name__ == "__main__":
    main()
