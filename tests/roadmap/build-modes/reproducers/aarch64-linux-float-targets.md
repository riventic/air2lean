# aarch64-linux float lowering: native observations

The aarch64-linux translation follows its own float rules (`docs/floats.md` §Targets,
`Target.qualified` in `Air2Lean/Air/Dialect.lean`), and the aarch64-linux build-mode runs test the
committed aarch64-linux translations (`tests/golden/0.16.0/<ex>/Gen-linux-aarch64.lean`, through
`scripts/check-tree.py create --host-goldens 0.16.0`), so no example is left out of them. The
rules that differ from aarch64-macos were measured with
[`aarch64-linux-float-probe.zig`](aarch64-linux-float-probe.zig), built with stock Zig 0.14.1,
0.15.2 and 0.16.0 `aarch64-linux` (`-mcpu=baseline`) for `aarch64-linux-gnu` and
`aarch64-linux-musl`, each without and with `-lc`, in ReleaseSafe, ReleaseFast and Debug, and run
in a native `linux/arm64` container (Ubuntu 24.04, Apple-silicon Docker VM, no emulation). The
three modes agree on every line.

    for v in 0.14.1 0.15.2 0.16.0; do for t in aarch64-linux-gnu aarch64-linux-musl; do
      for lc in "" -lc; do zig-$v build-exe -OReleaseSafe -mcpu=baseline -target $t $lc \
        -femit-bin=p aarch64-linux-float-probe.zig && ./p; done; done; done

| Case | Result | Model rule |
|---|---|---|
| `f16` `@mulAdd(0x3e00, 0x3c01, 0x8001)` | `0x3e02` everywhere (one `f32` `fmadd`, then rounded to `f16`); a fused `f16` `fmadd` gives `0x3e01` | the `generic` baseline has no `fullfp16`: `FloatRules.aarch64 (fusedF16 := false)`, `Float.fma`'s `f16` rule |
| `f128` `@sqrt(2)` | `…bcd000000000000000` (`f64` precision) on 0.14.1/0.15.2 except musl with `-lc`; correctly rounded on 0.16.0 and on musl with `-lc` | `long double` is `f128`: LLVM calls `sqrtl`; compiler_rt's unless a static libc defines it |
| `f128` `@mulAdd(0.25, 0.25, 2^16383)` | NaN (compiler_rt `fmaq`) everywhere except musl with `-lc` (`2^16383`, musl `fmal`) | the same libcall routing (`fmal`) |
| `f128` `@sin(1)`, `@exp(1)` | compiler_rt (`f64` precision before 0.16.0) except musl with `-lc` | opaque (`docs/floats.md` §Transcendental functions) |
| `f128` `@max(-0, +0)` | `-0` on 0.14.1 without musl `-lc`, `+0` otherwise | group D: `.unspecified` |
| `0/0` | positive quiet NaN in every format (`7e00`, `7fc00000`, `7ff8…`, `f80` `7fffc…`, `f128` `7fff8…`) | any NaN (`Float.Allowed`) |
| NaN operand `+ 1` | the operand's payload and sign with the quiet bit set, in every format | any NaN |

glibc and musl differ only where a static libc can define the `long double` routine: with glibc
(`gnu`), the `-lc` builds still resolve `sqrtl`, `fmal`, `sinl`, … to compiler_rt (whose static
definitions take precedence over the shared `libm`), and musl without `-lc` links no libc. The AIR
profile records no `link_libc`, so the checker rejects these `f128` ops unless
`--assume-no-libc` (premise MTH-05) and qualifies the `gnu` ABI only.
