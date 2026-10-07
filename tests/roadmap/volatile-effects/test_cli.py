#!/usr/bin/env python3
"""L13 volatile/device effects: actual-CLI regressions over exporter-schema AIR fixtures.

Synthetic fixtures use the exporter's pointer schema (`docs/air-json.md`: every `ptr`
type entry carries `volatile`). `--export-dir` instead checks a fresh real export of
`volatile_effects.zig`. `--self-test` checks the fixture builders without a translator.
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
VERSIONS = ("0.14.1", "0.15.2", "0.16.0")

U32 = dict(k="int", signed=False, bits=32, abi_size=4, abi_align=4)
VOID = dict(k="void", abi_size=0, abi_align=1)
NORETURN = dict(k="noreturn")
U8 = dict(k="int", signed=False, bits=8, abi_size=1, abi_align=1)
USIZE = dict(k="int", signed=False, bits=64, abi_size=8, abi_align=8)


def ptr(child, *, volatile, const=False, size="one", align=4):
    abi = 16 if size == "slice" else 8
    return dict(k="ptr", size=size, const=const, child=child, ptr_align=align, volatile=volatile,
                allowzero=False, sentinel=False, host_size=0, abi_size=abi, abi_align=8)


# 0 u32, 1 void, 2 noreturn, 3 *volatile u32, 4 *u32, 5 *const volatile u32,
# 6 []volatile u8, 7 u8, 8 usize, 9 *const u32, 10 []u8, 11 *volatile u8
TYPES = [U32, VOID, NORETURN, ptr(0, volatile=True), ptr(0, volatile=False),
         ptr(0, volatile=True, const=True), ptr(7, volatile=True, size="slice", align=1), U8, USIZE,
         ptr(0, volatile=False, const=True), ptr(7, volatile=False, size="slice", align=1),
         ptr(7, volatile=True, align=1)]


def inst(i, tag, ty, args=(), **extra):
    return dict(id=i, tag=tag, ty=ty, args=list(args), **extra)


def ref(i):
    return dict(inst=i)


def function(name, params, ret, body, version="0.16.0"):
    return dict(schema=11, zig_version=version, name=name, types=copy.deepcopy(TYPES),
                params=params, ret=ret, body=body, globals=[])


def returning(i, value, ty=2):
    return inst(i, "ret", ty, [value])


def fixtures(version="0.16.0"):
    """name -> (document, expected): `None` accepted, else the rejected instruction kind."""
    f = lambda name, params, ret, body: function(name, params, ret, body, version)
    void = dict(ty=1, val="{}")
    return {
        "load_volatile": (f("load_volatile", [3], 0, [
            inst(0, "arg", 3, param=0), inst(1, "load", 0, [ref(0)]), returning(2, ref(1))]), "volatile load"),
        "load_plain": (f("load_plain", [4], 0, [
            inst(0, "arg", 4, param=0), inst(1, "load", 0, [ref(0)]), returning(2, ref(1))]), None),
        "store_volatile": (f("store_volatile", [3, 0], 1, [
            inst(0, "arg", 3, param=0), inst(1, "arg", 0, param=1), inst(2, "store", 1, [ref(0), ref(1)]),
            returning(3, void)]), "volatile store"),
        "store_plain": (f("store_plain", [4, 0], 1, [
            inst(0, "arg", 4, param=0), inst(1, "arg", 0, param=1), inst(2, "store", 1, [ref(0), ref(1)]),
            returning(3, void)]), None),
        "atomic_volatile": (f("atomic_volatile", [3], 0, [
            inst(0, "arg", 3, param=0), inst(1, "atomic_load", 0, [ref(0)], order="seq_cst"),
            returning(2, ref(1))]), "volatile atomic access"),
        "slice_volatile": (f("slice_volatile", [6, 8], 7, [
            inst(0, "arg", 6, param=0), inst(1, "arg", 8, param=1),
            inst(2, "slice_elem_val", 7, [ref(0), ref(1)]), returning(3, ref(2))]), "volatile load"),
        # 0.16.0's `slice_elem_ptr` + `load` pair: canonicalization must keep the volatile load.
        "slice_ptr_volatile": (f("slice_ptr_volatile", [6, 8], 7, [
            inst(0, "arg", 6, param=0), inst(1, "arg", 8, param=1),
            inst(2, "slice_elem_ptr", 11, [ref(0), ref(1)]), inst(3, "load", 7, [ref(2)]),
            returning(4, ref(3))]), "volatile load"),
        # A read-only local copy read through `*const volatile`: never forwarded as a value.
        "local_volatile": (f("local_volatile", [], 0, [
            inst(0, "alloc", 4), inst(1, "store", 1, [ref(0), dict(ty=0, val="5")]),
            inst(2, "bitcast", 5, [ref(0)]), inst(3, "load", 0, [ref(2)]), returning(4, ref(3))]),
            "volatile load"),
        "local_plain": (f("local_plain", [], 0, [
            inst(0, "alloc", 4), inst(1, "store", 1, [ref(0), dict(ty=0, val="5")]),
            inst(2, "bitcast", 9, [ref(0)]), inst(3, "load", 0, [ref(2)]), returning(4, ref(3))]), None),
        # `@volatileCast` away, and `@intFromPtr`, would launder a device pointer.
        "drop_volatile": (f("drop_volatile", [3], 4, [
            inst(0, "arg", 3, param=0), inst(1, "bitcast", 4, [ref(0)]), returning(2, ref(1))]),
            "without `volatile`"),
        "int_from_volatile": (f("int_from_volatile", [3], 8, [
            inst(0, "arg", 3, param=0), inst(1, "bitcast", 8, [ref(0)]), returning(2, ref(1))]),
            "without `volatile`"),
        # Address metadata only, as the committed `layout.asVolatile` export.
        "keep_volatile": (f("keep_volatile", [4], 3, [
            inst(0, "arg", 4, param=0), inst(1, "bitcast", 3, [ref(0)]), returning(2, ref(1))]), None),
        "std_volatile": (f("std_volatile", [6], 1, [
            inst(0, "arg", 6, param=0),
            inst(1, "call", 1, [ref(0)], callee=dict(func="mem.Allocator.free", noreturn=False)),
            returning(2, void)]), "has no volatile contract"),
    }


def invoke(binary, *argv):
    return subprocess.run([str(binary), *map(str, argv)], capture_output=True, text=True,
                          timeout=30, check=False)


def diagnostics(binary, air):
    result = invoke(binary, "--diagnostics-json", air)
    assert result.stderr == "", result.stderr
    report = json.loads(result.stdout)
    assert result.returncode == (1 if report["status"] == "rejected" else 0), result
    return report


def write(air, documents):
    for old in air.glob("*.json"):
        old.unlink()
    for name, document in documents.items():
        (air / f"{name}.json").write_text(json.dumps(document))


def assert_volatile(report, function, marker):
    assert report["status"] == "rejected", report
    found = [d for d in report["diagnostics"] if d["code"] == "VOLATILE_ACCESS" and d["function"] == function]
    assert found, (function, report)
    for d in found:
        assert (d["phase"], d["category"]) == ("check", "unsupported_semantics"), d
        assert d["anchor"]["id_space"] == "canonical" and d["anchor"]["instruction"] is not None, d
        assert marker in d["message"] and "footprint.writes" in d["message"], d
    # The specific code supersedes the generic instruction check for the same instruction.
    anchors = {d["anchor"]["instruction"] for d in found}
    assert not any(d["code"] == "INSTRUCTION_FAILURE" and d["function"] == function and
                   d["anchor"]["instruction"] in anchors for d in report["diagnostics"]), report


def check_fixtures(binary, air):
    checks = 0
    for version in VERSIONS:
        for name, (document, expected) in fixtures(version).items():
            write(air, {name: document})
            report = diagnostics(binary, air)
            if expected is None:
                assert report["status"] == "checked", (version, name, report)
            else:
                assert_volatile(report, name, expected)
            checks += 1
    return checks


def check_emission(binary, tmp, air):
    """Ordinary translation fails closed and leaves the output untouched."""
    out = tmp / "Gen.lean"
    for name, (document, expected) in fixtures().items():
        write(air, {name: document})
        out.write_text("KEEP\n")
        result = invoke(binary, air, "-o", out, "--namespace", "Volatile")
        if expected is None:
            assert result.returncode == 0, (name, result.stderr)
        else:
            assert result.returncode == 1 and expected in result.stderr, (name, result.stderr)
            assert out.read_text() == "KEEP\n", name
    return len(fixtures())


PROFILE_DOCUMENT = Path(__file__).resolve().parents[1] / "models" / "client.json"


def registry_client(nested=False):
    base = json.loads(PROFILE_DOCUMENT.read_text())
    holder = dict(k="struct", name="Regs", layout="extern", fields=[dict(name="reg", ty=2, offset=0)],
                  abi_size=8, abi_align=8)
    types = [U32, NORETURN, ptr(0, volatile=True), VOID, holder]
    param = 4 if nested else 2
    body = [inst(0, "arg", param, param=0),
            inst(1, "call", 3, [ref(0)], callee=dict(func="project.mmioWrite")),
            inst(2, "ret", 1, [ref(1)])]
    return {**{k: base[k] for k in ("schema", "zig_version", "target_endian", "profile")},
            "name": "client", "params": [param], "ret": 3, "types": types, "body": body, "globals": []}


def check_registry(binary, tmp, air):
    """The registry hook: a volatile parameter needs an explicit write footprint."""
    out, registry = tmp / "Gen.lean", tmp / "registry.json"
    base = [binary, air, "-o", out, "--namespace", "VolatileClient"]
    write(air, {"client": registry_client()})
    result = invoke(*base, "--model-registry-template")
    assert result.returncode == 0, result.stderr
    template = json.loads(out.read_text())
    assert template["models"][0]["signature"]["params"][0]["layout"]["volatile"] is True
    template["models"][0].update({
        "import": "Device.Model", "implementation": "Device.mmioWrite", "contract": "Device.mmioWriteSpec",
        "trust": "assumed", "termination": "total", "errors": [], "effects": "tracked",
        "dependencies": [], "footprint": {"reads": [], "writes": [0]}})
    def attempt(models, diagnostic=None):
        registry.write_text(json.dumps(models))
        out.write_text("KEEP\n")
        result = invoke(*base, "--model-registry", registry)
        if diagnostic is None:
            assert result.returncode == 0, result.stderr
            assert "Device.mmioWrite" in out.read_text()
        else:
            assert result.returncode == 1 and diagnostic in result.stderr, result.stderr
            assert out.read_text() == "KEEP\n"
    attempt(template)
    for change in ({"footprint": {"reads": [0], "writes": []}}, {"effects": "preserves", "footprint": None}):
        changed = copy.deepcopy(template)
        changed["models"][0].update(change)
        if changed["models"][0]["footprint"] is None:
            changed["models"][0].pop("footprint")
        attempt(changed, "must be listed in footprint.writes")
    write(air, {"client": registry_client(nested=True)})
    nested = copy.deepcopy(template)
    result = invoke(*base, "--model-registry-template")
    assert result.returncode == 0, result.stderr
    nested["models"][0]["signature"] = json.loads(out.read_text())["models"][0]["signature"]
    nested["models"][0]["footprint"] = {"reads": [], "writes": []}
    attempt(nested, "nested volatile pointer")
    return 4


EXPORT_EXPECTED = {
    "volatile_effects.mmioRead": "volatile load",
    "volatile_effects.mmioWrite": "volatile store",
    "volatile_effects.mmioFixed": "volatile load",
    "volatile_effects.localVolatile": "volatile load",
    "volatile_effects.sliceRead": "volatile load",
    "volatile_effects.dropVolatile": "without `volatile`",
    "volatile_effects.keepVolatile": None,
}


def check_export(binary, export):
    """A fresh real export: the exporter's flag reaches the checker on every access."""
    files = {json.loads(p.read_text())["name"]: p for p in sorted(export.glob("*.json"))}
    assert set(EXPORT_EXPECTED) <= set(files), sorted(files)
    for name, document in files.items():
        if name in EXPORT_EXPECTED:
            ptrs = [t for t in json.loads(document.read_text())["types"] if t.get("k") == "ptr"]
            assert all(isinstance(t.get("volatile"), bool) for t in ptrs), (name, ptrs)
    with tempfile.TemporaryDirectory(prefix="air2lean-volatile-export-") as tmp:
        for name, expected in EXPORT_EXPECTED.items():
            air = Path(tmp) / name
            air.mkdir()
            (air / files[name].name).write_bytes(files[name].read_bytes())
            report = diagnostics(binary, air)
            if expected is None:
                assert report["status"] == "checked", (name, report)
            else:
                assert_volatile(report, name, expected)
    return len(EXPORT_EXPECTED)


class SelfTest(unittest.TestCase):
    def test_fixture_schema(self):
        for version in VERSIONS:
            for name, (document, expected) in fixtures(version).items():
                self.assertEqual(document["zig_version"], version)
                for t in document["types"]:
                    if t["k"] == "ptr":
                        self.assertIsInstance(t["volatile"], bool, name)
                ids = [i["id"] for i in document["body"]]
                self.assertEqual(ids, sorted(set(ids)), name)

    def test_each_rejection_has_plain_or_metadata_control(self):
        expected = {name: e for name, (_, e) in fixtures().items()}
        accepted = {name for name, e in expected.items() if e is None}
        self.assertEqual(accepted, {"load_plain", "store_plain", "local_plain", "keep_volatile"})
        self.assertTrue(all(expected[n.replace("plain", "volatile")] for n in accepted if "plain" in n))

    def test_registry_fixture(self):
        plain, nested = registry_client(), registry_client(nested=True)
        self.assertEqual(plain["types"][plain["params"][0]]["volatile"], True)
        self.assertEqual(nested["types"][nested["params"][0]]["k"], "struct")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path, nargs="?")
    parser.add_argument("--export-dir", type=Path, help="fresh AIR export of volatile_effects.zig")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        unittest.main(argv=[sys.argv[0]])
        return
    if not args.binary:
        parser.error("provide a root-built translator, or --self-test")
    binary = args.binary.resolve(strict=True)
    if args.export_dir:
        print(f"volatile export checks: {check_export(binary, args.export_dir.resolve(strict=True))}")
        return
    with tempfile.TemporaryDirectory(prefix="air2lean-volatile-") as tmp:
        tmp = Path(tmp)
        air = tmp / "air"
        air.mkdir()
        checks = check_fixtures(binary, air) + check_emission(binary, tmp, air) + check_registry(binary, tmp, air)
    print(f"volatile effect checks: {checks}")


if __name__ == "__main__":
    main()
