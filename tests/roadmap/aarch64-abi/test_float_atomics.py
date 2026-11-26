#!/usr/bin/env python3
"""Float atomics on the aarch64 profiles: actual-CLI regressions over exporter-schema AIR fixtures.

The model has no float atomic messages, so the translator rejects every atomic op on a float cell
(`CheckCtx.atomicChild`). The native probe (`atomic_f80.zig`, the `f80atomic` rows of
`expected/<zig>/<triple>-ReleaseSafe.txt`) shows why this must hold for `f80` on both aarch64
profiles: Zig 0.14.1 to 0.16.0 fail to compile every such op, and 0.17.1 compiles `@atomicStore`
and stores the address of the operand instead of its value (`docs/upstream/f80-atomic-store.md`).
Here every float width and every atomic op Sema accepts on a float (load and store at each
ordering, RMW `.Xchg`/`.Add`/`.Sub`/`.Max`/`.Min`) is rejected for each recorded Zig version on
aarch64-linux-gnu and aarch64-macos-none, translation leaves the output untouched, and the same
ops on a `u32` cell are accepted. `--self-test` checks the fixture builders without a translator.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
VERSIONS = ("0.17.1", "0.16.0", "0.15.2", "0.14.1")
# The profiles of the native AIR exports (`tests/golden/<zig>/*/air-linux-aarch64`, `air-darwin`).
PROFILES = {
    "aarch64-linux-gnu": dict(target_triple="aarch64-linux.7.0.14...7.0.14-gnu.2.39", abi="gnu",
                              cpu="generic", features=["fp_armv8", "neon"]),
    "aarch64-macos-none": dict(target_triple="aarch64-macos.27.0.1...27.0.1-none", abi="none",
                               cpu="apple_m1", features=["fp_armv8", "fullfp16", "lse", "neon"]),
}
FLOATS = (16, 32, 64, 80, 128)
# (the `f80atomic` op of the native probe, AIR tag, ordering or RMW op)
OPS = [(f"load_{order}", "atomic_load", order) for order in ("monotonic", "acquire", "seq_cst")] + \
      [(f"store_{order}", f"atomic_store_{order}", None) for order in ("monotonic", "release", "seq_cst")] + \
      [(f"rmw_{op}", "atomic_rmw", op) for op in ("Xchg", "Add", "Sub", "Max", "Min")]
FLOAT_ATOMIC = "a float atomic is outside the subset"
# Zig 0.17.1 gives `f80` (both profiles) and `f128` (aarch64-macos, where it is not `c_longdouble`)
# alignment 8, the model 16 (docs/aarch64-abi.md §Zig 0.17.1): the memory check rejects the cell
# before the atomic check.
LAYOUT = "the memory model gives type 0 size 16 and alignment 16, the compiler 16 and 8"
# An `f80` `.Max`/`.Min` is also an op on an 80-bit representation in a 16-byte cell: the
# padded-width check (`PADDED_ATOMIC`, tests/roadmap/padded-atomics/) rejects it first.
PADDED = "a 80-bit integer representation with padding bits"


def profile(triple, version):
    return dict(name="abi64-le-v1", pointer_bits=64, endian="little", zig_version=version,
                backend="stage2_llvm", build_mode="ReleaseSafe", float_mode="per-instruction",
                error_set_bits=16, error_layout="type-table", error_tracing=False,
                export_stage="analyzed-air", **PROFILES[triple])


def under_aligned(bits, triple, version):
    """The exporter's alignment of `f<bits>` is 8 where the model's is 16."""
    return version == "0.17.1" and (bits == 80 or bits == 128 and triple == "aarch64-macos-none")


def float_align(bits, triple, version):
    """The exporter's size and alignment of `f<bits>`."""
    if bits in (80, 128):
        return 16, 8 if under_aligned(bits, triple, version) else 16
    return bits // 8, bits // 8


def cell_type(kind, triple, version):
    if kind == "u32":
        return dict(k="int", signed=False, bits=32, abi_size=4, abi_align=4)
    bits = int(kind[1:])
    size, align = float_align(bits, triple, version)
    return dict(k="float", bits=bits, abi_size=size, abi_align=align)


def document(kind, op_name, tag, arg, triple, version):
    """`fn(p: *T, a: T)`: the op on `p`; types 0 T, 1 void, 2 noreturn, 3 *T."""
    child = cell_type(kind, triple, version)
    ptr = dict(k="ptr", size="one", const=False, child=0, ptr_align=child["abi_align"],
               volatile=False, allowzero=False, address_space="generic", sentinel=False, host_size=0,
               vector_index=None, abi_size=8, abi_align=8)
    p, a = dict(inst=0), dict(inst=1)
    if tag == "atomic_load":
        op = dict(id=2, tag=tag, ty=0, args=[p], order=arg)
    elif tag == "atomic_rmw":
        op = dict(id=2, tag=tag, ty=0, args=[p, a], op=arg, order="seq_cst")
    else:
        op = dict(id=2, tag=tag, ty=1, args=[p, a])
    body = [dict(id=0, tag="arg", ty=3, param=0), dict(id=1, tag="arg", ty=0, param=1), op,
            dict(id=3, tag="ret", ty=2, args=[dict(ty=1, val="{}")])]
    return dict(schema=12, zig_version=version, target_endian="little",
                profile=profile(triple, version), name=f"{kind}_{op_name}".lower(),
                module="root", types=[child, dict(k="void", abi_size=0, abi_align=1),
                                      dict(k="noreturn"), ptr],
                params=[3, 0], noalias=[], ret=1, body=body, globals=[])


def expected(kind, op, triple, version):
    """`None` if the op is accepted, else the rejection's reason (the first check that fails)."""
    if kind == "u32":
        return None
    if kind == "f80" and op in ("rmw_Max", "rmw_Min"):
        return PADDED
    return LAYOUT if under_aligned(int(kind[1:]), triple, version) else FLOAT_ATOMIC


def fixtures(triple, version):
    """name -> (document, expected) for every float width and op, and the `u32` controls."""
    result = {}
    for kind in [f"f{b}" for b in FLOATS] + ["u32"]:
        for op_name, tag, arg in OPS:
            doc = document(kind, op_name, tag, arg, triple, version)
            result[doc["name"]] = (doc, expected(kind, op_name, triple, version))
    return result


def invoke(binary, *argv):
    return subprocess.run([str(binary), *map(str, argv)], capture_output=True, text=True,
                          timeout=30, check=False)


def write(air, name, doc):
    for old in air.glob("*.json"):
        old.unlink()
    (air / f"{name}.json").write_text(json.dumps(doc))


def check_fixtures(binary, tmp, air):
    checks = 0
    out = tmp / "Gen.lean"
    for triple in PROFILES:
        for version in VERSIONS:
            for name, (doc, reason) in fixtures(triple, version).items():
                where = (triple, version, name)
                write(air, name, doc)
                result = invoke(binary, "--diagnostics-json", air)
                assert result.stderr == "", (where, result.stderr)
                report = json.loads(result.stdout)
                if reason is None:
                    assert result.returncode == 0 and report["status"] == "checked", (where, report)
                else:
                    assert result.returncode == 1 and report["status"] == "rejected", (where, report)
                    found = [d for d in report["diagnostics"] if reason in d["message"]]
                    assert len(found) == 1, (where, report)
                    assert found[0]["function"] == name and found[0]["phase"] == "check", (where, found)
                # Ordinary translation fails closed and leaves the output untouched.
                out.write_text("KEEP\n")
                result = invoke(binary, air, "-o", out, "--namespace", "FloatAtomics")
                if reason is None:
                    assert result.returncode == 0 and out.read_text() != "KEEP\n", (where, result.stderr)
                else:
                    assert result.returncode == 1 and reason in result.stderr, (where, result.stderr)
                    assert out.read_text() == "KEEP\n", where
                checks += 1
    return checks


class SelfTest(unittest.TestCase):
    def test_every_float_and_op_is_rejected_and_u32_accepted(self):
        for triple in PROFILES:
            for version in VERSIONS:
                cases = fixtures(triple, version)
                self.assertEqual(len(cases), (len(FLOATS) + 1) * len(OPS))
                for name, (doc, reason) in cases.items():
                    self.assertEqual(doc["name"], name)
                    self.assertEqual(doc["types"][3]["ptr_align"], doc["types"][0]["abi_align"])
                    self.assertEqual(reason is None, name.startswith("u32_"), name)

    def test_first_reason(self):
        for kind, op, triple, version, reason in (
                ("f80", "store_seq_cst", "aarch64-linux-gnu", "0.17.1", LAYOUT),
                ("f80", "store_seq_cst", "aarch64-macos-none", "0.17.1", LAYOUT),
                ("f128", "rmw_Add", "aarch64-macos-none", "0.17.1", LAYOUT),
                ("f128", "rmw_Add", "aarch64-linux-gnu", "0.17.1", FLOAT_ATOMIC),
                ("f80", "store_seq_cst", "aarch64-linux-gnu", "0.16.0", FLOAT_ATOMIC),
                ("f64", "load_acquire", "aarch64-macos-none", "0.17.1", FLOAT_ATOMIC),
                ("f80", "rmw_Max", "aarch64-linux-gnu", "0.16.0", PADDED),
                ("f80", "rmw_Min", "aarch64-macos-none", "0.17.1", PADDED)):
            self.assertEqual(expected(kind, op, triple, version), reason, (kind, op, triple, version))

    def test_ops_are_the_native_probe_ops_sema_accepts(self):
        """Each AIR op is a probed `f80atomic` op; the probed `cmpxchg` never reaches AIR (Sema)."""
        spec = importlib.util.spec_from_file_location(
            "aarch64_abi", Path(__file__).resolve().parents[3] / "scripts/aarch64-abi.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        ops = {op for op, _, _ in OPS}
        self.assertEqual(set(driver.F80_OPS) - ops, {"cmpxchg_strong", "cmpxchg_weak"})
        self.assertLessEqual(ops, set(driver.F80_OPS))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path, nargs="?")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        unittest.main(argv=[sys.argv[0]])
        return
    if not args.binary:
        parser.error("provide a root-built translator, or --self-test")
    binary = args.binary.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix="air2lean-float-atomics-") as tmp:
        tmp = Path(tmp)
        air = tmp / "air"
        air.mkdir()
        checks = check_fixtures(binary, tmp, air)
    print(f"float atomic checks: {checks}")


if __name__ == "__main__":
    main()
