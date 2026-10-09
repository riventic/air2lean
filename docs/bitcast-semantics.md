# `@bitCast` semantics: Zig 0.16.0 vs 0.17.0

Zig 0.17.0 changed what `@bitCast` means. 0.16.0 reinterpreted the **in-memory**
representation. 0.17.0 reinterprets the **logical bit representation**, which is the same on
every target. The translator selects the rules from the function's `zig_version`
(`Air2Lean/BitCast.lean`, `logicalBitCastVersion`). ≤0.16 inputs keep the existing rules
unchanged, including the memory representation casts of arrays and `extern` aggregates
(`Zig.reprCast`, [aggregate-casts.md](aggregate-casts.md)). Sources: the 0.16.0 and 0.17.0 release tarballs (sha256 pins in
`zig-patch/versions.toml`; 0.17.0 `b6c7f172…8abd`) and the 0.17.0 release notes
("@bitCast changes").

## The two definitions

**0.16.0.**
- `zirBitcast` (0.16 `src/Sema.zig` 9524) accepts int, float, bool, vectors, and extern or packed
  structs and unions. It accepts arrays whose element type has a well-defined layout. It
  rejects enums with "use @enumFromInt/@intFromEnum", and it rejects pointers and optionals.
- The size check uses `Type.bitSize` (0.16 `src/Type.zig` 1221). On the LLVM backend an array
  has `(len-1) * 8 * @sizeOf(E) + @bitSizeOf(E)` bits, so padding between elements counts. Only
  the trailing padding is dropped. A vector has `len * @bitSizeOf(E)` bits.
- At comptime the operand is flattened to memory bytes (`src/Sema/bitcast.zig`, which depends
  on endianness). At runtime LLVM uses a `bitcast` or a store/load through memory
  (`codegen/llvm/FuncGen.zig` 4461). A vector of `iN` maps to an LLVM `<n x iN>` bitcast,
  which LLVM packs: lane 0 goes in the low bits on little-endian and the high bits on
  big-endian. An array is stored with each element in its ABI slot.

**0.17.0.**
- `zirBitcast` (0.17 `src/Sema.zig` 9403) accepts every type with
  `Type.hasBitRepresentation` (0.17 `src/Type.zig` 3242). That is void, bool, int, float, an enum
  with an *explicit* tag type, a packed struct or union, and an array or vector of these.
- Extern or auto structs and unions, error sets and error unions are compile errors. So are
  pointers and optionals, including arrays or vectors of them.
- `Type.bitSize` (0.17 `src/Type.zig` 1318) gives an array or vector
  `len_including_sentinel * @bitSizeOf(E)` bits, with no padding.
- The value is `Value.writeToPackedMemory` followed by `readFromPackedMemory` (0.17
  `src/Value.zig` 392, 523; `Sema.bitCastVal` 30148). Element `i` occupies logical bits
  `[i*eb, (i+1)*eb)`, so element 0 is in the low bits. An enum or packed type uses its backing
  integer. The result does not depend on endianness.
- Runtime: the analyzed AIR keeps one `bit_cast` (or `bit_cast_safe`) on the aggregate. The
  exporter dumps this pre-legalization AIR. LLVM later scalarizes array and vector cases into
  shifts (`Air/Legalize.zig` `scalarize_bit_cast_*`, `scalarizeBitcastBlockPayload`).
- With safety on, every runtime `@bitCast` is `bit_cast_safe` (`zirBitcast` 9495–9499, and
  `@fromBackingInt` 9633). Its only extra meaning is a check: when the result is a *scalar*
  exhaustive enum, an unnamed tag triggers the `invalid enum value` panic
  (`FuncGen.airBitCast` 4673; Legalize `expand_bit_cast_safe`). Arrays or vectors of enums get
  no check. Without safety, an invalid tag is unchecked illegal behaviour.

## Delta table (little-endian targets)

The "Same bits?" column is measured with stock Zig on aarch64-macos (§Evidence). "CE" means
compile error.

| Source → destination | 0.16.0 | 0.17.0 | Same bits? |
|---|---|---|---|
| int ↔ int, int ↔ float, `bool` ↔ `u1`, packed struct/union ↔ backing int | bit copy | bit copy | yes |
| `@Vector(n, uW)` ↔ `u(n*W)`, any `W` (`@Vector(4,u5)`→`u20`, `@Vector(3,u9)`→`u27`) | LLVM packed vector, lane 0 low | logical, lane 0 low | yes (LE). On BE, 0.16 puts lane 0 high |
| `@Vector(n, bool)` ↔ `uN` | packed bits | logical | yes (LE) |
| `[n]uW` ↔ int, `W` = 8·2^k (fills its ABI size: `[4]u8`, `[2]u16`, `[2]f32`→`u64`) | memory bytes | logical | yes (LE): `encode_array_eq_intBytes_ofLanes`. BE differs |
| `[n]uW` with padded `W` (`[2]u24`, `[3]u9`) | size `(n-1)·8·@sizeOf + W`, padding included: `[2]u24`↔`u56` = `0x44556600112233`, `[3]u9`↔`u41` = `0x1aa00ff0101` | size `n·W`: `[2]u24`↔`u48` = `0x445566112233`, `[3]u9`↔`u27` = `0x6a9ff01` | **no**. Each side's cast is a CE on the other version (size mismatch) |
| `[n]bool` ↔ int | `[8]bool` has 57 bits | `[8]bool`↔`u8`, element `i` = bit `i` | **no** (0.16 CE for `u8`) |
| array ↔ vector, or array/vector of another element size (`@Vector(4,u5)`→`[5]u4`) | element-wise store at ABI stride, or CE on size | logical regrouping | **no** |
| nested arrays (`[4][4]bool`→`u16`, `[2][1][3][5]u4`→`u120`) | CE or memory layout | flattened in order | **no** |
| packed struct ↔ `[n]u1` / `@Vector(n,u1)` | CE (57 ≠ 16 bits) | backing int bit `i` = element `i` | **no** |
| int ↔ enum with explicit tag type | CE ("use @enumFromInt") | tag bits; exhaustive destination checks the tag (`bit_cast_safe`) | new in 0.17 |
| extern struct/union ↔ anything | memory reinterpretation | CE | removed in 0.17 |
| `f80` in arrays (`[2]f80`) | 16-byte slots (208 bits) | 160 bits | **no** |

0.16's memory reinterpretation and 0.17's logical order coincide on little-endian exactly when
every array element fills its ABI size. They always coincide for vectors. Padded or non-byte
array elements, `bool` arrays, nested arrays, array↔vector regrouping, and every big-endian
target differ. (The model rejects big-endian targets anyway: `Profile.lean`.)

## What the translator does for a 0.17 input

A `bitcast` (Canon renames 0.17's `bit_cast`/`bit_cast_safe` to it, `Air/Canon.lean`
`versionTags`) whose types differ and that has an array, vector, enum or `void` on either side
goes through `bitShape?` and `logicalBitCastShapes`. Everything else (scalars, packed ↔ int,
pointer casts) keeps the existing rules, which agree with 0.17 for those types.

| Case | 0.17 model |
|---|---|
| `[n]uW`/`[n]iW`/`@Vector(n, uW)` ↔ int, any `W` (incl. padded `u24`, `u9`) | **model**: `Zig.BitCast.ofLanes` / `toLanes` |
| `[n]bool` / `@Vector(n, bool)` ↔ int | **model**: `ofBools` / `toBools` |
| lane aggregate ↔ lane aggregate of other shape, packed struct, float, bool, enum | **model**: compose through `BitVec (bits)` |
| int ↔ enum (any tag signedness), enum ↔ enum/packed/float | **model**: tag bits. An exhaustive destination becomes `Zig.enumOf (E.ofInt? …)`: an unnamed tag throws `.panic` (`invalidEnumValue`). The same model covers `bit_cast` in unsafe builds, where that case is illegal behaviour (`ZigLean/Basic.lean`: "never throws" covers both). An enum ↔ exactly its tag type keeps the ≤0.16 text |
| nested arrays, arrays/vectors of floats, enums or packed structs | **reject**: `a Zig 0.17 `@bitCast` of an array or vector whose element is not an integer or `bool` …` |
| sentinel-terminated arrays | **reject**: `… of a sentinel-terminated array …` |
| packed union ↔ aggregate/enum, `void`, any other type | **reject**: `… to or from a type other than …` |
| total bit sizes differ (cannot come from Sema) | **reject**: `… between types of A and B logical bits …` |

Every rejection message starts with "a Zig 0.17 `@bitCast`" and ends with "(logical bit order,
docs/bitcast-semantics.md)". No 0.17 aggregate cast falls back to the ≤0.16 rules.

## Lemmas (`ZigLean/BitCast.lean`)

- `toLanes_ofLanes`, `ofLanes_toLanes`, `toBools_ofBools`, `ofBools_toBools`: round trips.
- `getLsbD_ofLanes`: bit `w*i + j` of the integer is bit `j` of lane `i`. `getLsbD_ofBools` is
  the same for bools.
- `encode_array_eq_intBytes_ofLanes`: for `W = 8k` with `intSize W = k` (no padding), the
  model's memory bytes of `[n]uW` (`Zig.Enc`) are the little-endian bytes of `ofLanes v`.
  `encode_vec_eq_intBytes_ofLanes` proves the same for vectors whose lanes fill the power-of-2
  size. `encode_ofLanes_eq_encode_array` covers an unpadded result integer: the 0.17 integer and
  the array have identical encodings. So a ≤0.16 fact stated through memory carries over to the
  0.17 translation in this case. `tests/roadmap/bitcast-017/BitCastReal/Runtime.lean` applies
  it to translated real 0.17 AIR.
- `decode_boolVec`, `decode_boolVec_bits`: the model's `@Vector(n, bool)` memory decoder
  (`Vec.packedEnc` with 1-bit lanes) gives lane `i` bit `i` of the packed integer, as `toBools`
  does, so the bool-vector layout already follows the logical order.

## Evidence

- 0.17.0 behaviour tests (`test/behavior/bitcast.zig`) checked against `ZigLean.BitCast`
  (`tests/roadmap/bitcast-017/Semantics.lean`):
  - "@bitCast vector to array with different element size": `0x65e2`, `[2,14,5,6,0]`.
  - "bitcast vector to integer and back": `0xfffd`.
  - "@bitCast packed struct to array of bits".
  - "@bitCast nested arrays of bool to scalar": `0b1100_0101_1010_0011`.
  - "@bitCast deeply nested arrays to scalar": `0x8873B…0F51`.
- The safety case `test/cases/safety/bitcast_to_enum_no_matching_tag_value.zig` panics with
  `invalid enum value`. The compile-error cases `bitcast_to_enum_invalid_tag_value.zig` and
  `bitCast_extern_struct.zig` are errors.
- Native probes with stock 0.17.0 aarch64-macos (sha256 `b607e9b9…c536a`) and 0.16.0, in Debug
  and ReleaseSafe:
  - Both versions give `vec4u5→u20 = 0x65e2`, `vec3u9→u27 = 0x6a9ff01`,
    `[4]u8→u32 = 0x44332211` and `[2]f32→u64 = 0xc00000003f800000`.
  - 0.17 gives `[2]u24→u48 = 0x445566112233`, `[3]u9→u27 = 0x6a9ff01` and `[8]bool→u8 = 0x89`.
    0.16 gives `[2]u24→u56 = 0x44556600112233` and `[3]u9→u41 = 0x1aa00ff0101`.
  - Compile-only: `[8]bool→u8` fails on 0.16 ("57 bits") and passes on 0.17. `u8→enum(u8)`
    fails on 0.16 and passes on 0.17. `[2]u24→u56` passes on 0.16 and fails on 0.17 (48 bits).
    `[2]u24→u48` is the reverse. An extern struct cast passes on 0.16 and fails on 0.17.
  - 0.17 `@bitCast(@as(u8, 3))` to `enum(u8){a,b,c}` panics with `invalid enum value` (exit 134).
- `tests/roadmap/bitcast-017/check.sh`:
  - It translates real 0.17.0 AIR of `bitcast017.zig` (patched exporter, ReleaseSafe, all
    `bit_cast_safe`) and pins `BitCastReal/Gen.lean`.
  - It runs that translation against the values `zig test` checks natively.
  - It runs the synthetic accept/reject, ≤0.16-unchanged and emitted-runtime regressions
    (`Pipeline.lean`).
