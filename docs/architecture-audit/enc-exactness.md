# Encode/decode exactness of the memory model

Status: WIP (parked 2026-10-12; resumes on top of the one proof framework). Branch
`codex/enc-exactness`, handoff `~/.cache/air2lean/handoffs/codex__enc-exactness.md`.

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
| same, 0.17.0 LLVM, and the self-hosted x86_64 backend (Debug x86_64 from 0.15.2) | was `Enc (BitVec n)` | **BUG-1, fixed**: the store writes the zero/sign extension of the whole ABI integer; the load is `trunc nuw`/`trunc nsw` (poison unless the padding is that extension; the self-hosted backend loads the whole integer). Old model: bytes of `u16 0x0200` read as `i10` = `-512`; native 0.17.0 ReleaseSafe aarch64 `512` (no `i10`), Debug x86_64 0.15.2–0.17.0 `512`. Fix: `Zig.intEncExt o signed n` (`ZigLean/Endian.lean`), bound by the translator (`Dialect.intExtOrder?`, `emitStorageEnc`, enum instances) |
| `bool` | `Enc Bool` | 0.17.0: exact (`store` zext `i8`). ≤0.16: `store i1`, bits 1–7 unspecified by LangRef, observed 0 on both targets: OPEN (candidate: `.part 1` encoding) |
| out-of-range `bool`/exhaustive enum byte | `Enc Bool`, enum instances | `.illegal` (Zig: illegal behaviour) |
| floats (non-NaN) | `Enc (Float fmt)` | exact; NaN bits undefined (`Float.detMask`, PR #174); `f80` bytes 10–15 padding undefined |
| `*T` | `Enc Ptr` | exact (symbolic `ptrFrag`); integer reads expose the address at load (MM-11) |
| `?*T`, `[*c]T`, `*allowzero T` | `Enc (Option Ptr)`, `nullablePtrEnc` | exact (null = 8 zero bytes) |
| `?T` | `Enc (Option α)` | exact; null payload undefined; flag ≠ 0/1 is `.illegal` (over-approximation: native tests `≠ 0`) |
| `[]T`, `?[]T` | `Enc Slice`, `Enc (Option Slice)` | exact; null length undefined |
| `[n]T`, `@Vector(n, T)` | `Enc (Vector α n)`, `Vec.packedEnc` | exact (items' rules; vector lanes bit-packed, padding undefined) |
| `E`, `?E`, `E!T` (all widths) | `errBytes`, `ErrWidth.lean` | exact (symbolic `errFrag`); numeric views of error storage are rejected by `Check.lean`. 0.17.0 writes a `?E` code sign-extended into its padding bits (probe: code 78 at 7 bits stores `0xce`) while an `E` load is `trunc nuw`: upstream row for #131 |
| `extern union`, `packed union` | `Raw`, `PackedU` | exact (bytes / defined-bit masks) |
| packed struct | `Packed`, `Packed.encodeOf` | exact (backing integer; 0.17.0 load is a plain `trunc`) |
| `std.mem.Allocator`, `std.Io` (16 zero bytes), `std.Thread` (model tid) | `Alloc.lean`, `Call.lean`, `Thread.lean` | **BUG-2, fixed (fail closed)**: invented bytes; a pointer cast exposing them (`asBytes(&allocator)`) read 0 where native reads the `vtable` address. `Check.lean` `hasOpaqueModelStorage` rejects such casts |

## Regression rows

`tests/roadmap/enc-exactness/Rows.lean`: one kernel-checked row per value kind (exact round trip,
undetermined bits `.unspecified`). `check.sh`: the fixture translated for all four versions, its
model lines against the recorded native outputs, and the negative `opaque_bytes.zig`.
