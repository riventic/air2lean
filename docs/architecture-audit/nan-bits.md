# Soundness finding: NaN bits observed through memory

Class: SOUNDNESS. Status: fixed (this branch). Found during batch D (L07/L08), where the Zig 0.17
packed and logical-cast paths got undefined NaN bits (`Zig.Packed.mask`); the memory paths of
every version kept the model's canonical NaN bits.

## Finding

Zig leaves the sign and payload of a NaN that an operation makes unspecified, and targets
differ: `0.0 / 0.0` is `0xffc00000` (`f32`) on x86_64 and `0x7fc00000` on aarch64, and both
propagate a NaN operand's payload (`docs/floats.md` §NaN). The model returns one canonical
quiet NaN (`Float.nan`, `0x7fc00000`) for every NaN result. `Float.toBits?` already made a
scalar `@bitCast` of a NaN `.unspecified`, but the float memory encoding (`Enc (Float fmt)`)
wrote the canonical bits as defined bytes. Every path that reads those bytes as an integer then
proved the canonical pattern:

- a store and a load through a pointer of another type (`*const u32` of an `f32`);
- an `extern union` written through its float field and read through its integer field;
- a Zig ≤0.16 `@bitCast` of an array, `extern struct` or vector holding a float (a memory
  reinterpretation, `Zig.reprCast`), and a vector in memory (`Vec` float encoding);
- `@memcpy` of the float's bytes into an integer.

## Counterexample

`tests/roadmap/nan-bits/nan_bits.zig` (abridged; operands are run-time values):

```zig
var g32: f32 = 0;

pub fn storeLoad(a: f32, b: f32) u32 {
    g32 = a / b;
    return @as(*const u32, @ptrCast(&g32)).*;
}

pub fn sumBits(a: f32, b: f32) u32 {
    g32 = a + b;
    return @as(*const u32, @ptrCast(&g32)).*;
}
```

`native.zig` calls them with volatile-loaded operands (`storeLoad(0, 0)`,
`sumBits(@bitCast(0x7fc00123), 1)`), so no compiler folds the operations. Native outputs with
stock Zig 0.14.1, 0.15.2, 0.16.0 and 0.17.0, ReleaseSafe and Debug, x86_64-linux-musl in a
Docker `linux/amd64` container and aarch64-linux-musl in a `linux/arm64` container (aarch64-macos
on the host gives the aarch64 values), against the model before the fix (`origin/codex/roadmap-batch-d`
37e5b06a, the 0.16.0 export; 0.14.1 and 0.15.2 give the same results, and 0.17.0 too except
`arrayCast` and `vectorCast`, which its logical `@bitCast` already made `.unspecified`):

| case | x86_64 | aarch64 | model before | model after |
|---|---|---|---|---|
| `storeLoad` (`f32` 0/0) | `0xffc00000` | `0x7fc00000` | `0x7fc00000` | `.unspecified` |
| `storeLoad64` (`f64` 0/0) | `0xfff8000000000000` | `0x7ff8000000000000` | `0x7ff8000000000000` | `.unspecified` |
| `sumBits` (payload NaN + 1) | `0x7fc00123` | `0x7fc00123` | `0x7fc00000` | `.unspecified` |
| `unionView` (`extern union`) | `0xffc00000` | `0x7fc00000` | `0x7fc00000` | `.unspecified` |
| `arrayCast` (`[2]f32` → `u64`) | `0x3f800000ffc00000` | `0x3f8000007fc00000` | `0x3f8000007fc00000` | `.unspecified` |
| `vectorCast` (`@Vector(2, f32)` → `u64`) | `0x3f800000ffc00000` | `0x3f8000007fc00000` | `0x3f8000007fc00000` | `.unspecified` |
| `structView` (`extern struct` read as `u64`) | `0x7ffc00000` | `0x77fc00000` | `0x77fc00000` | `.unspecified` |
| `copyBytes` (`@memcpy` into a `u32`) | `0xffc00000` | `0x7fc00000` | `0x7fc00000` | `.unspecified` |
| `finiteBits` (1/3) | `0x3eaaaaab` | `0x3eaaaaab` | `0x3eaaaaab` | `0x3eaaaaab` |
| `constStore` (NaN constant stored) | `0x7fa00002` | `0x7fa00002` | `0x7fa00002` | `0x7fa00002` |
| `constGlobal` (NaN constant initializer) | `0x7fa00001` | `0x7fa00001` | `0x7fa00001` | `0x7fa00001` |
| `reloadIsNaN` (stored NaN read as a float) | `1` | `1` | `1` | `.unspecified` |

Before the fix, `result (storeLoad z z) = some (.ok 0x7fc00000)` was a kernel-checkable
theorem (`decide +kernel` on the closed term), and x86_64 refutes it. `sumBits` is refuted on
both targets: the model's canonical NaN is never the propagated payload. Every case that
compiled through the memory model was affected; the scalar `@bitCast` and the Zig 0.17 logical
casts of arrays and vectors (`Zig.Packed.toBits?`) were not.

## Fix

One mechanism, the defined-bit masks that batch D introduced for packed values:

- `Float.detMask` (`ZigLean/Mem/Enc.lean`): a float's determined bits, none for a NaN. It is the
  float's `Zig.Packed.mask` (`ZigLean/PackedRepr.lean`) and the mask of its memory encoding.
- `Enc (Float fmt)` writes `maskedBytes v.bits v.detMask` (moved with `Byte.defBits`,
  `Byte.ofDefBits` and `lowMask8` from `ZigLean/Packed.lean` to `ZigLean/Mem/Enc.lean`), so a
  NaN's bytes are undefined; so do the big-endian `floatEncOf` and both vector encodings
  (`Vec` float instance, `Vec.floatEncOf`). An integer read of them is `.unspecified`.
- A NaN constant has determined bits, which the compiler stores exactly. The translator writes
  them over the encoding for a store (to memory or a byte local), a scalar `@memset` item and a global initializer
  (`Air2Lean/Memory.lean`'s `nanConstParts`, `Emit.lean`'s `FCtx.nanConstBytes?`), at any depth
  where the exporter gives the byte offset.

A stored NaN read back as a float is now `.unspecified` as well (`reloadIsNaN`): the bytes do
not say which NaN they hold, and undefined bytes could also be an infinity. This is an
over-approximation (native code reads a NaN), documented in `docs/floats.md` §NaN in memory.
Target-exact NaN payloads of operations remain F04.

## Regressions

- `tests/roadmap/nan-bits/` (`check.sh`, run in CI): the committed exports of all four versions,
  their translations, the kernel-checked `Model.lean` (`storeLoad_nan`, …, `constGlobal_ok`;
  `storeLoad_no_value`/`sumBits_no_value`: no integer at all, so neither the canonical nor a
  native pattern, is a result), and the model's lines against the recorded native outputs of
  both targets, with `unspecified` matching any value. `check.sh --native V` rebuilds the native
  program and compares it with the recorded outputs.
- `ZigLean/EndianLemmas.lean`: `floatEncOf_nan_int` (every integer read of a stored NaN's bytes is
  `.unspecified`, at both byte orders and every width that fits), `floatEncOf_decode_encode_nan`,
  and `floatEncOf_decode_encode` (a float that is not a NaN reads back exactly).
