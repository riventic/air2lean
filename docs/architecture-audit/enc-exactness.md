# Encode/decode exactness of the memory model

Status: audit complete; BUG-1 and BUG-2 fixed (branch `codex/enc-exactness-2`); two rows OPEN
(below). Handoff `~/.cache/air2lean/handoffs/codex__enc-exactness-2.md`.

Rule: every value <-> bytes pair is either exact (`decode (encode v) = v`, and `encode` writes only
bits the compiler determines) or explicitly unspecified (`.unspecified`, or `.illegal` as a
documented over-approximation). The model never writes a canonical value the compiler does not
guarantee, and never decodes a value from bits that native code treats as poison.

## Verdicts

Evidence: compiler source (`src/codegen/llvm.zig`, 0.17.0 `src/codegen/llvm/FuncGen.zig`
`load`/`store`), native probes `tests/roadmap/enc-exactness/` (x86_64-linux-musl in Docker
`linux/amd64`, aarch64-linux-musl in `linux/arm64`, aarch64-macos on the host; ReleaseSafe and
Debug; 0.14.1, 0.15.2, 0.16.0, 0.17.0).

| Pair | Where | Verdict |
|---|---|---|
| `uN`/`iN`, `N = 8 * intSize N` | `Enc (BitVec n)` | exact |
| `uN`/`iN` with padding bits, ≤0.16 LLVM | `Enc (BitVec n)`/`intEncOf` | exact: `loadTruncate` loads the ABI integer and truncates (padding ignored); `store iN` leaves the padding unspecified (model: undefined; observed: a `u24` store leaves byte 3 untouched) |
| same, 0.17.0 LLVM, and the self-hosted x86_64 backend (Debug x86_64 from 0.15.2) | was `Enc (BitVec n)` | **BUG-1, fixed** (§BUG-1) |
| `bool` | `Enc Bool` | 0.17.0: exact (`store` zext `i8`). ≤0.16: `store i1`, bits 1–7 unspecified by LangRef, observed 0 on both targets: OPEN (candidate: `.part 1` encoding) |
| out-of-range `bool`/exhaustive enum byte | `Enc Bool`, enum instances | `.illegal` (Zig: illegal behaviour) |
| floats (non-NaN) | `Enc (Float fmt)` | exact; NaN bits undefined (`Float.detMask`, `nan-bits.md`); `f80` bytes 10–15 padding undefined |
| `*T` | `Enc Ptr` | exact (symbolic `ptrFrag`); integer reads expose the address at load (MM-11) |
| `?*T`, `[*c]T`, `*allowzero T` | `Enc (Option Ptr)`, `nullablePtrEnc` | exact (null = 8 zero bytes) |
| `?T` | `Enc (Option α)` | exact; null payload undefined; flag ≠ 0/1 is `.illegal` (over-approximation: native tests `≠ 0`) |
| `[]T`, `?[]T` | `Enc Slice`, `Enc (Option Slice)` | exact; null length undefined |
| `[n]T`, `@Vector(n, T)` | `Enc (Vector α n)`, `Vec.packedEnc` | exact (items' rules; vector lanes bit-packed, padding undefined) |
| `E`, `?E`, `E!T` (all widths) | `errBytes`, `ErrWidth.lean` | exact (symbolic `errFrag`); numeric views of error storage are rejected by `Check.lean`. 0.17.0 writes a `?E` code sign-extended into its padding bits (probe: code 78 at 7 bits stores `0xce`) while an `E` load is `trunc nuw`: OPEN, upstream row for #131 |
| `extern union`, `packed union` | `Raw`, `PackedU` | exact (bytes / defined-bit masks) |
| packed struct | `Packed`, `Packed.encodeOf` | exact (backing integer; 0.17.0 load is a plain `trunc`) |
| `std.mem.Allocator`, `std.Io`, `std.Thread` | `Alloc.lean`, `Call.lean`, `Thread.lean` | **BUG-2, fixed**: the model wrote bytes the target does not have (16 zero bytes; the thread number as a `u64`); `model-handle-bytes.md` |

## BUG-1: integers with padding bits on 0.17.0 and the self-hosted x86_64 backend

Zig 0.17.0 (LLVM) stores a `uN`/`iN` whose bit width is not its ABI size zero- or sign-extended
to the whole ABI integer (`FuncGen.store`) and loads it with `trunc nuw`/`trunc nsw`
(`FuncGen.load`): poison unless the padding bits are that extension. The self-hosted x86_64
backend (Debug on x86_64 from 0.15.2) stores the extension too and loads the whole ABI integer.
The model used the ≤0.16 encoding at every version (padding undefined at a store, ignored at a
load), so it read a value where native code has none.

Counterexample (`tests/roadmap/enc-exactness/enc_exactness.zig`):

```zig
var w16: u16 = 0;
pub fn i10ZeroPad(x: u16) i16 {
    w16 = x;
    return @as(*const i10, @ptrCast(&w16)).*;
}
```

`i10ZeroPad(0x0200)`: the old 0.17.0 model returned `-512` (sign bit 9 set, padding ignored).
Native: `512` on 0.17.0 ReleaseSafe aarch64 and on Debug x86_64 0.15.2–0.17.0 (the self-hosted
backend reads the whole `u16`), `-512` on 0.17.0 ReleaseSafe x86_64 (`trunc nsw` poison, folded
differently per target). The same holds for `u24` with a set padding bit (`u24SetPad(0x01000005)`:
old model `5`, Debug x86_64 `0x1000005`) and an `enum(u24)` tag.

Fix: `Zig.intEncExt o signed n` (`ZigLean/Endian.lean`): a store writes the extension of the
whole ABI integer, a load needs every bit defined and the padding equal to the extension of the
value bits, else `.unspecified`. `intEncExt_decode_encode` (`ZigLean/EndianLemmas.lean`) is its
round trip. The translator binds it wherever such an integer is stored or loaded
(`Dialect.intExtOrder?`: from 0.17.0, and on a `stage2_x86_64` profile at every version;
`emitStorageEnc` for scalars, optionals, arrays, error unions and futures; the enum instances for
an `enum(uN)` tag). Up to 0.16.0 with LLVM the encoding stays `intEncOf`.

The encoding is chosen per backend, three-valued (`Dialect.intPadding`): `loose` (LLVM up to
0.16.0: `intEncOf`), `extended` (LLVM from 0.17.0, self-hosted x86_64: `intEncExt`) and `unknown`
(a legacy schema-11 profile, whose backend is `unverified`, and any other backend). No encoding
is sound for `unknown`: `intEncOf` is wrong where the backend reads the whole ABI integer (the
counterexample above), `intEncExt` is wrong where it writes undefined padding (LLVM ≤ 0.16 then
reads a value the model calls `.unspecified`, and a store's padding bytes differ). So
`Check.checkPaddedStorage` rejects, on an `unknown` backend, every pointer to a storage type that
holds such an integer (fail closed; a bit-pointer accesses its whole host integer and is exempt).
Counterexample of the old behaviour: `enc_exactness.i10ZeroPad` under `--profile legacy-abi64-le`
was translated with the LLVM ≤ 0.16 encoding; a Debug x86_64 build of the same source returns
`512`, the model `-512`. Now it is rejected (`check.sh`: the fixture relabelled legacy and as
`stage2_aarch64`, every version). The committed fixtures that were schema-11 with such integers
(the `layout` goldens, `bitops/qualified`, `packed-fields`, `padded-atomics`, `flow-time`) were
refreshed to schema-12 exports or LLVM profiles; their normalized AIR and translations are
unchanged.

## Regression rows

`tests/roadmap/enc-exactness/` (`README.md`): `Rows.lean`, one kernel-checked row per value kind
(exact round trip, undetermined bits `.unspecified`); `check.sh`, the fixture translated for all
four versions, its kernel-checked results (`Model.lean`) and its model lines against the recorded
native outputs of both targets, including the model-handle row `allocatorWordIsZero` of
`model-handle-bytes.md`.
