#!/usr/bin/env python3
"""`@mulAdd` per target, Zig version and CPU: actual-CLI regressions over exporter-schema AIR.

An `f16` `@mulAdd` is lowered in four ways (`F16MulAdd` in `Air2Lean/Air/Dialect.lean`,
docs/floats.md §Targets): the `f16` instruction on an aarch64 CPU with `fullfp16`; an `f32`
multiply-add rounded to `f16` (LLVM up to Zig 0.16.0, compiler_rt's `__fmah`, the self-hosted
x86_64 backend); from Zig 0.17.1 an `f64` multiply-add rounded to `f16` (an instruction on aarch64
and s390x, the `fma` routine on x86_64); and on wasm32 an `f64` multiplication and addition. The
native rows are the `fma` and `cpu` rows of `expected/<zig>/<triple>-ReleaseSafe.txt`, which
`Model.lean` checks against the same rule (`Dialect.f16MulAdd`); here the term that the translator
emits is checked for every qualified target, recorded version, `fullfp16` setting and float mode,
and an aarch64 profile without the float instructions (`fp_armv8`) is rejected. `--self-test`
checks the expected table without a translator.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
VERSIONS = ("0.17.1", "0.16.0", "0.15.2", "0.14.1")
MODES = ("ieee", "compiler-rt")
LLVM, SELF_HOSTED = "stage2_llvm", "stage2_x86_64"
# name -> (profile fields, the row's `f16` rule from Zig 0.17.1 without an `f16` instruction)
TARGETS = {
    "x86_64-linux": (dict(target_triple="x86_64-linux-gnu", abi="gnu", cpu="x86_64", features=[]),
                     "f64-routine"),
    "aarch64-linux": (dict(target_triple="aarch64-linux.7.0.14...7.0.14-gnu.2.39", abi="gnu",
                           cpu="generic", features=["fp_armv8", "neon"]), "f64-instruction"),
    "aarch64-macos": (dict(target_triple="aarch64-macos.27.0.1...27.0.1-none", abi="none",
                           cpu="apple_m1", features=["fp_armv8", "fullfp16", "lse", "neon"]),
                      "f64-instruction"),
    "s390x-linux": (dict(target_triple="s390x-linux-gnu", abi="gnu", cpu="arch8", features=[],
                         endian="big", name="abi64-be-v1"), "f64-instruction"),
    "mips64-linux": (dict(target_triple="mips64-linux-muslabi64", abi="muslabi64", cpu="mips64r2",
                          features=[], endian="big", name="abi64-be-v1"), "f32"),
    "wasm32-wasi": (dict(target_triple="wasm32-wasi-musl", abi="musl", cpu="lime1", features=[],
                         pointer_bits=32), "f64-mul-add"),
}
AARCH64 = ("aarch64-linux", "aarch64-macos")
A, B, C = "p0", "p1", "p2"


def profile(target, version, backend=LLVM, features=None):
    fields = dict(name="abi64-le-v1", pointer_bits=64, endian="little", zig_version=version,
                  backend=backend, build_mode="Debug" if backend == SELF_HOSTED else "ReleaseSafe",
                  float_mode="per-instruction",
                  error_set_bits=16, error_layout="type-table", error_tracing=False,
                  export_stage="analyzed-air")
    fields.update(TARGETS[target][0])
    if features is not None:
        fields["features"] = features
    return fields


def document(bits, prof):
    """`fn(a: fN, b: fN, c: fN) fN { return @mulAdd(fN, a, b, c); }`: types 0 fN, 1 noreturn."""
    body = [dict(id=i, tag="arg", ty=0, param=i) for i in range(3)] + [
        dict(id=3, tag="mul_add", ty=0, args=[dict(inst=0), dict(inst=1), dict(inst=2)]),
        dict(id=4, tag="ret", ty=1, args=[dict(inst=3)])]
    return dict(schema=12, zig_version=prof["zig_version"], target_endian=prof["endian"],
                profile=prof, name=f"mul_add_f{bits}", module="root",
                types=[dict(k="float", bits=bits, abi_size=bits // 8, abi_align=bits // 8),
                       dict(k="noreturn")],
                params=[0, 0, 0], noalias=[], ret=0, body=body, globals=[])


def rule(target, version, backend, features):
    """The `f16` rule (`Dialect.f16MulAdd`)."""
    if target in AARCH64 and "fullfp16" in features:
        return "f16"
    if version != "0.17.1" or backend == SELF_HOSTED:
        return "f32"
    return TARGETS[target][1]


def expected(bits, target, version, mode, backend=LLVM, features=None):
    """The emitted term (`FCtx.mulAddExpr`)."""
    features = TARGETS[target][0]["features"] if features is None else features
    rt = "" if mode == "ieee" else "Rt017" if version == "0.17.1" else "Rt"
    fused = f"pure (Zig.Float.fma{rt}Fused {A} {B} {C})"
    reference = f"Zig.Float.fma{rt}Chk {A} {B} {C}"
    a, b, c = (f"(Zig.Float.conv .f64 {x})" for x in (A, B, C))
    wide = f"{a} {b} {c}"
    kind = rule(target, version, backend, features) if bits == 16 else "f16"
    if kind == "f16":
        return fused if target in AARCH64 else reference
    if kind == "f32":
        return reference
    if kind == "f64-mul-add":
        return f"pure (Zig.Float.conv .f16 (Zig.Float.add (Zig.Float.mul {a} {b}) {c}))"
    if target in AARCH64:
        return f"pure (Zig.Float.conv .f16 (Zig.Float.fma{rt}Fused {wide}))"
    routine = rt if kind == "f64-routine" else ""
    return f"Zig.Float.conv .f16 <$> Zig.Float.fma{routine}Chk {wide}"


def cases():
    """(bits, target, version, mode, backend, features or None for the target's own)."""
    result = []
    for version in VERSIONS:
        for mode in MODES:
            for target in TARGETS:
                for bits in (16, 32, 64):
                    result.append((bits, target, version, mode, LLVM, None))
            for target in AARCH64:
                own = TARGETS[target][0]["features"]
                result.append((16, target, version, mode, LLVM, sorted(set(own) ^ {"fullfp16"})))
            if version != "0.14.1":  # the self-hosted backend's Debug profile (from 0.15.2)
                result.append((16, "x86_64-linux", version, mode, SELF_HOSTED, None))
    return result


def invoke(binary, *argv):
    return subprocess.run([str(binary), *map(str, argv)], capture_output=True, text=True,
                          timeout=30, check=False)


def write(air, doc):
    for old in air.glob("*.json"):
        old.unlink()
    (air / f"{doc['name']}.json").write_text(json.dumps(doc))


def check_cases(binary, tmp, air):
    out = tmp / "Gen.lean"
    checks = 0
    for bits, target, version, mode, backend, features in cases():
        where = (bits, target, version, mode, backend, features)
        write(air, document(bits, profile(target, version, backend, features)))
        # The self-hosted backend's modes are not all qualified (docs/build-modes.md): opt in.
        extra = ["--allow-unqualified-build-mode"] if backend == SELF_HOSTED else []
        result = invoke(binary, air, "-o", out, "--namespace", "MulAdd", "--float-semantics", mode,
                        *extra)
        assert result.returncode == 0, (where, result.stderr)
        line = f" ← {expected(bits, target, version, mode, backend, features)}\n"
        assert out.read_text().count(line) == 1, (where, line, out.read_text())
        checks += 1
    # Without the float instructions every float op is a compiler_rt call: outside the rules.
    for target in AARCH64:
        for version in VERSIONS:
            soft = [f for f in TARGETS[target][0]["features"] if f != "fp_armv8"]
            write(air, document(16, profile(target, version, features=soft)))
            out.write_text("KEEP\n")
            result = invoke(binary, air, "-o", out, "--namespace", "MulAdd")
            assert result.returncode == 1, (target, version, result.stderr)
            assert "needs the CPU feature fp_armv8" in result.stderr, (target, version, result.stderr)
            assert out.read_text() == "KEEP\n", (target, version)
            checks += 1
    return checks


class SelfTest(unittest.TestCase):
    def test_f16_rules(self):
        for target, version, backend, features, want in (
                ("aarch64-macos", "0.14.1", LLVM, ["fp_armv8", "fullfp16"], "f16"),
                ("aarch64-linux", "0.17.1", LLVM, ["fp_armv8", "fullfp16"], "f16"),
                ("aarch64-linux", "0.16.0", LLVM, ["fp_armv8"], "f32"),
                ("aarch64-macos", "0.16.0", LLVM, ["fp_armv8"], "f32"),
                ("aarch64-linux", "0.17.1", LLVM, ["fp_armv8"], "f64-instruction"),
                ("aarch64-macos", "0.17.1", LLVM, ["fp_armv8"], "f64-instruction"),
                ("x86_64-linux", "0.16.0", LLVM, [], "f32"),
                ("x86_64-linux", "0.17.1", LLVM, [], "f64-routine"),
                ("x86_64-linux", "0.17.1", SELF_HOSTED, [], "f32"),
                ("s390x-linux", "0.17.1", LLVM, [], "f64-instruction"),
                ("mips64-linux", "0.17.1", LLVM, [], "f32"),
                ("wasm32-wasi", "0.17.1", LLVM, [], "f64-mul-add"),
                ("wasm32-wasi", "0.15.2", LLVM, [], "f32")):
            self.assertEqual(rule(target, version, backend, features), want, (target, version))

    def test_terms(self):
        wide = "(Zig.Float.conv .f64 p0) (Zig.Float.conv .f64 p1) (Zig.Float.conv .f64 p2)"
        for args, want in (
                ((16, "aarch64-linux", "0.17.1", "ieee"),
                 f"pure (Zig.Float.conv .f16 (Zig.Float.fmaFused {wide}))"),
                ((16, "aarch64-linux", "0.17.1", "compiler-rt"),
                 f"pure (Zig.Float.conv .f16 (Zig.Float.fmaRt017Fused {wide}))"),
                ((16, "aarch64-linux", "0.16.0", "compiler-rt"), "Zig.Float.fmaRtChk p0 p1 p2"),
                ((16, "aarch64-macos", "0.17.1", "ieee"), "pure (Zig.Float.fmaFused p0 p1 p2)"),
                ((32, "aarch64-linux", "0.16.0", "ieee"), "pure (Zig.Float.fmaFused p0 p1 p2)"),
                ((16, "x86_64-linux", "0.17.1", "compiler-rt"),
                 f"Zig.Float.conv .f16 <$> Zig.Float.fmaRt017Chk {wide}"),
                ((16, "x86_64-linux", "0.17.1", "ieee"), f"Zig.Float.conv .f16 <$> Zig.Float.fmaChk {wide}"),
                ((16, "s390x-linux", "0.17.1", "compiler-rt"),
                 f"Zig.Float.conv .f16 <$> Zig.Float.fmaChk {wide}"),
                ((16, "mips64-linux", "0.17.1", "compiler-rt"), "Zig.Float.fmaRt017Chk p0 p1 p2"),
                ((64, "x86_64-linux", "0.17.1", "compiler-rt"), "Zig.Float.fmaRt017Chk p0 p1 p2")):
            self.assertEqual(expected(*args), want, args)

    def test_cases_cover_every_target_version_mode_and_fullfp16(self):
        seen = {(target, version, mode) for _, target, version, mode, _, _ in cases()}
        self.assertEqual(len(seen), len(TARGETS) * len(VERSIONS) * len(MODES))
        flipped = [c for c in cases() if c[5] is not None]
        self.assertEqual(len(flipped), len(AARCH64) * len(VERSIONS) * len(MODES))
        for _, target, _, _, _, features in flipped:
            self.assertNotEqual("fullfp16" in features, "fullfp16" in TARGETS[target][0]["features"])


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
    with tempfile.TemporaryDirectory(prefix="air2lean-mul-add-") as tmp:
        tmp = Path(tmp)
        air = tmp / "air"
        air.mkdir()
        checks = check_cases(binary, tmp, air)
    print(f"mulAdd checks: {checks}")


if __name__ == "__main__":
    main()
