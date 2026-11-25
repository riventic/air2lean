# Packed representations and logical casts (L07, L08)

One mechanism serves packed fields, bit-pointers and Zig 0.17's logical `@bitCast`: the class
`Zig.Packed α n`, a type's `n`-bit logical representation (`ZigLean/Packed.lean`), with the
instances of `ZigLean/PackedRepr.lean` for floats, packed unions, arrays and vectors.

- A packed struct or union field can be an integer, `bool`, float, enum, packed struct, packed
  union, or (Zig 0.14.1 and 0.15.2 only) a vector of these (`packedBits`).
- `Packed.mask` gives the determined bits of a value. A NaN has none, because the model's
  canonical NaN stands for every NaN. Undefined bits of a packed union's bytes are not
  determined either.
- Wherever bits become observable, an undetermined bit is undefined and never the model's
  choice:
  - `Packed.toBits?` (`@bitCast`) throws `.unspecified`;
  - a bit-pointer store (`storeBits`) leaves the field undefined;
  - a packed struct's memory image (`Packed.encodeOf`) has undefined bits there.
- A Zig 0.17 `@bitCast` of any type with a logical bit representation is
  `Packed.toBits?` followed by `Packed.ofBits?`. This covers nested arrays, arrays and vectors of
  floats, enums, packed structs and packed unions, and packed unions themselves. An enum item
  without a name is `.illegal`: Zig 0.17 checks only a scalar enum result.
- Up to 0.16, a packed struct or union and another packable scalar of the same bit size
  (`packedScalarCast`) cast through the same class. A packed union in an array or `extern`
  representation cast is its bytes (`Zig.reprCast`).
- `Packed.bitCast_roundtrip` states the round-trip condition. The source's bits must all be
  determined and must give the source back. The destination must take every bit pattern as
  itself.

| File | Role |
|---|---|
| `packed_casts.zig` | Packed-union and float fields through bit-pointers; packed unions, floats, float arrays and vectors in `@bitCast`. Compiles with the same results on 0.14.1, 0.15.2, 0.16.0 and 0.17.1 |
| `logical017.zig` | 0.17 logical casts: nested arrays, arrays and vectors of floats, enums, packed structs and unions, packed union ↔ `[4]u4`. Each is a compile error or a different memory reinterpretation before 0.17 |
| `vector_fields.zig` | A vector as a packed-struct field (0.14.1 and 0.15.2; 0.16 made it a compile error) |
| `auto_items.zig` | 0.14.1 and 0.15.2 check only the outer types of a `@bitCast`. An array of `auto` structs or tagged unions is then a memory reinterpretation with the compiler's layout (`ZigVersion.bitCastAutoItems`) |
| `sentinel_arrays.zig` | A sentinel-terminated array in a memory cast (0.14.1, 0.15.2, 0.16.0): `@bitSizeOf` counts the sentinel, which is one more item of the source's bytes and of the result. `sentInit`: 0.14.1 does not store the sentinel of an array initialized at run time, so its byte is undefined there |
| `void_casts.zig`, `void017.zig` | Zero-bit casts: `[4]void`, `[0]u8` and `u0` in every version; `void` itself in 0.17. Sema folds them, so their exports hold no `bitcast` |
| `air-handwritten/<version>/void_cast/` | The `bitcast` of zero-bit types as an instruction (0.16.0 memory cast, 0.17.1 logical cast), written by hand because no compiler emits it; retained translations `PackedCasts/<version>/VoidCast.lean`, results in `ModelVoidCast.lean` |
| `reject_lanes.zig` | Rejected: a lane pointer into a vector field of a packed struct, which 0.14.1 and 0.15.2 miscompile ([upstream draft](../../../docs/upstream/packed-vector-lane-ptr.md)) |
| `reject_sentinel.zig` | Rejected on 0.17.1: a sentinel-terminated array in a logical cast. Comptime evaluation, the LLVM backend and the self-hosted x86_64 backend give three different results ([upstream draft](../../../docs/upstream/bitcast-sentinel-array.md)) |
| `reject_items.zig` | Rejected on 0.14.1 and 0.15.2 (compile errors from 0.16.0): arrays of tuples, of error sets or error unions, and of optionals in a cast |
| `reject/expected.txt` | Every function of the rejected sources with the text its diagnostic must contain; each is translated alone |
| `expected/wrong.txt` | Results of wrong models (the sentinel left out of the bits, the sentinel forced to the type's, `void` with bits, bytes swapped). The comparison with the model's lines and with the native output must reject each one |
| `compile-errors/` | Casts that Sema rejects, with `expected.txt` per version. An `auto` struct, tuple or tagged union fails on every version. Arrays of `auto` structs and tagged unions fail from 0.16.0, and an `extern` struct from 0.17.0 |
| `air/<version>/<source>/` | Patched-compiler exports (x86_64-linux, baseline, ReleaseSafe), declared in `exports.json` and pinned by `exports.lock.json` (`scripts/fixture-exports.py`) |
| `PackedCasts/<version>/<Source>.lean` | Their retained translations (`<version>` as a name: `V0_17_1`; `<Source>` one of `PackedCasts`, `Logical017`, `VectorFields`, `AutoItems`, `SentinelArrays`, `VoidCasts`, `Void017`) |
| `PackedCasts/<version>/{Model,ModelLogical,ModelVector,ModelAuto,ModelSentinel,ModelVoid,ModelVoid017}.lean` | Kernel-checked results (`decide +kernel`) of the translations, then `main` prints `native.zig`'s lines. Each is written for the newest version of its source; the older versions' modules are that one with the version renamed (`scripts/fixtures.py instance ... --write` after an edit) |
| `PackedCasts/Show.lean` | The models' formatting of results as `native.zig` prints them |
| `native.zig`, `expected/<version>.txt` | The native program and its output (stock Zig, x86_64-linux-musl ReleaseSafe and Debug print the same) |

```sh
lake build ZigLean Air2Lean air2lean
bash tests/roadmap/packed-casts/check.sh                       # every version: translate, compare, prove, model = observed, rejection
AIR2LEAN_ZIG_NATIVE=<stock zig V> bash tests/roadmap/packed-casts/check.sh --native V
AIR2LEAN_ZIG_NATIVE=<stock zig V> bash tests/roadmap/packed-casts/check.sh --compile-errors V
python3 -B scripts/fixture-exports.py verify packed-casts   # fresh exports equal air/ (export: rewrite)
```

`--native` runs in Docker `linux/amd64`. Set `AIR2LEAN_X86_64_RUN` to change the runner; empty
runs on the host. A model line `unspecified` (a NaN's bits, tagged-union padding, the sentinel
0.14.1 leaves unwritten) matches any native value. Every other line must be equal, and each
wrong model of `expected/wrong.txt` must fail the comparison.

## Scope

- **Pointer fields.** Allowed in 0.14.1 and 0.15.2 packed structs and rejected: the model's
  pointers carry provenance, not bits. Zig 0.16 made them a compile error ("pointers cannot be
  directly bitpacked").
- **Partly undefined packed values.** A packed struct whose host has an undefined bit loads as
  `.unspecified`. 0.14.1 and 0.15.2 read a field by loading the whole struct, so each fixture
  function defines its host first.
- **Sentinel of a cast result.** Up to 0.16 the last item of a `[n:s]T` made by a cast is the
  source's bits and is not checked against `s`, in the compilers and in the model. 0.14.1 and
  0.15.2 fold a comptime index `n` of such an array to `s` in Sema; the AIR then has the
  constant, and the model follows the AIR. The export has no sentinel value for an array type,
  so the model could not check it.
- **Rejected by name** (`reject/expected.txt`): a sentinel-terminated array in a 0.17 cast
  (upstream bug); an array of tuples (the memory model has no tuple layout), of error sets or
  error unions (symbolic error storage) or of optionals in a 0.14.1 or 0.15.2 cast; a sentinel
  array and a vector in a ≤0.16 cast.
- **Not modelled.** Big-endian packed structs with a float field (fail closed).
- **NaN bits through memory.** Up to 0.16, a NaN's bits stored to memory and read as an integer
  are the model's canonical bits, the same as for any float in memory. This is pre-existing
  behaviour of `Zig.Enc`, not changed here.
