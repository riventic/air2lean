# `@mulAdd` lowering per CPU

The model states one lowering of `@mulAdd` per target (`docs/floats.md` §Targets): on x86_64,
compiler_rt's routines. A CPU with a multiply-add instruction computes it differently, and the
checker admits the op only where the profile's backend and CPU compute it as the model states
(`CheckCtx.checkMulAdd`, `Dialect.mulAddLowering?`, `Dialect.mulAddModel` in
`Air2Lean/Check.lean`).

- `mul_add.zig`: one `@mulAdd` per float format and one on `@Vector(4, f32)`. `exports.json`
  declares its compiler exports for x86_64-linux at `-mcpu=baseline`, `haswell` (`fma`) and
  `sapphirerapids` (`fma`, `avx512fp16`) with Zig 0.17.1, 0.16.0, 0.15.2 and 0.14.1
  (`air/<version>/<cpu>/`, pinned by `exports.lock.json`).
- `test_cli.py`: the verdict on every export, function and float mode. Baseline: accepted.
  `haswell`: `f32`, `f64` and the vector rejected; `f16` accepted up to 0.16.0 (through `f32`,
  the model's rule) and rejected from 0.17.1 (an `f64` instruction where the model states the
  routine). `sapphirerapids`: `f16` rejected at every version. `f80`, `f128`: accepted.
- `witness.zig`, `native.sh`, `expected/<version>.txt`: the native `f32` witness. With stock Zig
  0.14.1–0.16.0 `@mulAdd(0x3f800001, 0x3f7fffff, 0x28000001)` is `0x3f800000` at
  `-mcpu=baseline` and `0x3f800001` at `-mcpu=haswell`; with 0.17.1 both are `0x3f800001`.

The rule on written profiles for every target, backend and feature set (s390x, `fma4`, an
unrecorded backend, the self-hosted backend) is in `tests/roadmap/aarch64-abi/test_mul_add.py`.

```sh
lake build air2lean
python3 tests/roadmap/mul-add-lowering/test_cli.py --self-test
python3 tests/roadmap/mul-add-lowering/test_cli.py .lake/build/bin/air2lean
python3 -B scripts/fixture-exports.py check mul-add-lowering     # verify: a fresh export
# The native witness: build on any host, run on x86_64-linux with FMA (docs/rosetta.md).
AIR2LEAN_ROSETTA=1 AIR2LEAN_ZIG_NATIVE=<stock zig> bash tests/roadmap/mul-add-lowering/native.sh --build DIR
docker run --rm --platform linux/amd64 -v DIR:DIR -v "$PWD":/repo:ro alpine:3 \
  sh -c 'apk add -q bash diffutils && bash /repo/tests/roadmap/mul-add-lowering/native.sh --run DIR'
```
