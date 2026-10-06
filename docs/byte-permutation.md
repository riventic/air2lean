# Integer byte and bit permutations

`byte_swap` and `bit_reverse` export exactly one `ty_op.operand` in Zig 0.14.1,
0.15.2 and 0.16.0. Both normalize to `permuteBits`; the checker requires an integer
or an integer vector and the exact same result type. Signedness, width and vector
length cannot change. `byte_swap` also requires a width evenly divisible by eight,
including zero. `bit_reverse` accepts every legal integer width, including u0/i0,
u1/i1 and non-byte widths. Integer widths remain bounded by Zig's 65535-bit limit.
Noninteger values and malformed operand arities fail before emission.

`Zig.bitReverse` reverses exactly the operand's bits, with no sign extension or
rounding to its ABI storage size. `Zig.byteSwap` reverses the byte ordinals while
keeping the bit ordinal inside each byte. For example, `0x1234:u16` becomes
`0x3412` under byte swap and `0x2c48` under bit reversal. Signed operands have the
same two's-complement permutation: `-32767:i16` has representation `0x8001`, whose
byte swap has representation `0x0180`. Both operations preserve their input type.
The runtime `byteSwap` function is total; its checked translation domain is
byte-aligned widths. No contract claims unaligned widths are legal Zig calls.

Vectors lift the scalar runtime through the existing `Zig.Vec.mapM` emission.
Each lane is permuted separately, including three-lane vectors. Lane positions do
not change. This value support does not expand the separate vector memory-layout
or cross-type vector bitcast subset.

`ZigLean/Permutation.lean` supplies general involution, per-bit, per-byte and
per-lane contracts for arbitrary legal widths and lane counts. These contracts
prove the Lean runtime semantics. They do not prove compiler Sema, exporter,
normalizer, emitter, backend or ABI preservation. The dedicated gate checks fresh
compiler-generated AIR, malformed signatures, generated execution, native
observations and six semantic mutations separately.

Run `tests/roadmap/byte-permutation/check.sh` with a matching stock and patched
compiler and `AIR2LEAN_EXPECT_ZIG_VERSION` set to one of the three supported
releases. AIR extraction uses x86_64-linux, baseline CPU and ReleaseSafe. Native
execution uses the current host; the manifest records that host separately.
The corpus has 795 observation rows, including exhaustive 8-bit scalar patterns,
all 9-bit values, signed representations, 16/24/64/128-bit patterns, asymmetric
three-lane vectors and compiler-folded zero-width results. General maximum-width
contracts and synthetic checker acceptance are separate from those bounded native
observations. A passing gate qualifies that recorded profile and corpus only.

Source inventories remain explicitly unqualified evidence until the actual
qualification results are recorded. The compiler queue executes each version
sequentially; no preexisting generated fixture serves as a fresh exporter check.
