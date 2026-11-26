#!/usr/bin/env python3
"""`@mulAdd` on x86_64 CPUs with and without a multiply-add instruction: the checker's verdict on
the compiler exports of `mul_add.zig` (exports.json: `-mcpu=baseline`, `haswell`,
`sapphirerapids`; Zig 0.17.1, 0.16.0, 0.15.2, 0.14.1).

The model states one lowering per target (`Dialect.mulAddModel`): on x86_64, compiler_rt's
routines. `CheckCtx.checkMulAdd` admits a `@mulAdd` only when the profile's backend and CPU
compute it that way (`Dialect.mulAddLowering?`):

* baseline: every function translates;
* `haswell` (`fma`): `f32`, `f64` and the `f32` vector are `vfmadd…` and are rejected; an `f16`
  goes through `f32` up to 0.16.0 (the model's rule, admitted) and through an `f64` instruction
  from 0.17.1 (rejected);
* `sapphirerapids` (also `avx512fp16`): an `f16` is the `f16` instruction, rejected at every
  version;
* `f80` and `f128` are compiler_rt's routines at every CPU.

The verdict does not depend on `--float-semantics`. `native.sh` runs the `f32` witness.
`tests/roadmap/aarch64-abi/test_mul_add.py` has the rule for every target, backend and feature
set on written profiles. `--self-test` checks the table without a translator.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
VERSIONS = ("0.17.1", "0.16.0", "0.15.2", "0.14.1")
MODES = ("ieee", "compiler-rt")
CPUS = ("baseline", "haswell", "sapphirerapids")
# function -> the float format of its `@mulAdd`
FUNCTIONS = {"fma16": 16, "fma32": 32, "fma64": 64, "fma80": 80, "fma128": 128, "fmaVec": 32}


def rejected(bits, cpu, version):
    if cpu == "baseline" or bits > 64:
        return False
    if bits == 16:
        return cpu == "sapphirerapids" or version == "0.17.1"
    return True


def features(version, cpu):
    """The profile's CPU features (the same for every function of one export)."""
    doc = json.loads((HERE / "air" / version / cpu / "mul_add.fma32.json").read_text())
    return doc["profile"]["features"]


def check(binary):
    checks = 0
    with tempfile.TemporaryDirectory(prefix="air2lean-mul-add-lowering-") as tmp:
        tmp = Path(tmp)
        air, out = tmp / "air", tmp / "Gen.lean"
        for version in VERSIONS:
            for cpu in CPUS:
                # The exports are what the test says they are.
                has = features(version, cpu)
                assert ("fma" in has, "avx512fp16" in has) == \
                    (cpu != "baseline", cpu == "sapphirerapids"), (version, cpu)
                for function, bits in FUNCTIONS.items():
                    for mode in MODES:
                        where = (version, cpu, function, mode)
                        shutil.rmtree(air, ignore_errors=True)
                        air.mkdir()
                        shutil.copy(HERE / "air" / version / cpu / f"mul_add.{function}.json", air)
                        out.write_text("KEEP\n")
                        result = subprocess.run(
                            [binary, air, "-o", out, "--namespace", "MulAdd", "--prefix", "mul_add.",
                             "--float-semantics", mode], capture_output=True, text=True)
                        checks += 1
                        if rejected(bits, cpu, version):
                            assert result.returncode == 1, (where, result.stderr)
                            assert f"`@mulAdd` on f{bits} is outside the subset for this profile" \
                                in result.stderr, (where, result.stderr)
                            assert "multiply-add instruction" in result.stderr, (where, result.stderr)
                            assert out.read_text() == "KEEP\n", where
                        else:
                            assert result.returncode == 0, (where, result.stderr)
                            assert "Zig.Float.fma" in out.read_text(), where
    return checks


class SelfTest(unittest.TestCase):
    def test_table(self):
        for args, want in (((32, "baseline", "0.16.0"), False), ((16, "baseline", "0.17.1"), False),
                           ((32, "haswell", "0.16.0"), True), ((64, "haswell", "0.17.1"), True),
                           ((16, "haswell", "0.16.0"), False), ((16, "haswell", "0.17.1"), True),
                           ((16, "sapphirerapids", "0.14.1"), True),
                           ((80, "haswell", "0.17.1"), False), ((128, "sapphirerapids", "0.16.0"), False)):
            self.assertEqual(rejected(*args), want, args)

    def test_exports_exist(self):
        for version in VERSIONS:
            for cpu in CPUS:
                for function in FUNCTIONS:
                    self.assertTrue((HERE / "air" / version / cpu / f"mul_add.{function}.json").is_file())


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
    print(f"mul-add-lowering checks: {check(args.binary.resolve(strict=True))}")


if __name__ == "__main__":
    main()
