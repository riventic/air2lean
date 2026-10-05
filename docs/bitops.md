# Integer bit operations

`clz`, `ctz`, `popcount`, and `shl_with_overflow` AIR normalize to explicit typed operations.
The existing exporter already emits their operands. The dedicated gate exports compiler-generated
fixtures for Zig 0.16.0 on reference x86_64-linux with baseline CPU and ReleaseSafe. It compares
the generated Lean with stock Zig execution on the current host, whose OS and architecture
are recorded separately in the manifest. This establishes observations for these integer
kernels; it does not qualify the full foreign target backend or ABI. The same tag spelling exists in the older
exporters; it does not establish their differential qualification.

`Zig.clz m a` counts leading zero bits, `Zig.ctz m a` counts trailing zero bits, and
`Zig.popcount m a` counts one bits in the fixed-width representation. Signed operands use their
two's-complement bits, so `popcount(-1)` equals the source width. Both zero-count operations
return the source width for zero, including u1 and u0. The result is the smallest unsigned
integer that can represent the source width: zero bits for u0 and `floor(log2(n)) + 1` otherwise.
Malformed result widths, signed count results, and non-integer operands fail before emission.

`Zig.shlWithOverflow s a b` returns a `Zig.Result` containing `(a << b, flag)` with wrapped
result bits and a u1 flag when the shift count is valid.
The flag is zero exactly when shifting the result back recovers `a`. The reverse shift is
arithmetic for signed inputs and logical for unsigned inputs. In particular, unsigned `1:u8`
shifted by 7 gives `(128,0)`, while signed `1:i8` gives `(128,1)`. Signed `-1:i8` shifted by 7
gives `(-128,0)`. For a valid count, a zero operand never loses bits. The shift-count type is the unsigned
`Log2Int` type for the operand. Although a u2 count can represent 3 for a u3 operand, count
3 is illegal behavior. The runtime returns `.illegal` whenever a nonzero count reaches or
exceeds the width, including for a zero operand. A zero count preserves the operand and a
zero flag, including the compiler-folded u0 case. Native differential execution excludes
those illegal inputs explicitly; model tests assert the illegal result. Ordinary lost-bit
overflow returns a flag and does not raise an overflow panic.

Integer vectors use these scalar definitions independently on each lane. Count results keep
the input lane count, and shift overflow returns a pair of vectors (wrapped values and u1
flags). Any invalid count in one lane makes the whole result `.illegal`. The checker validates
every shape and the emitter uses the existing `Zig.Vec.mapM`,
`map2M`, and `unzip` semantics. Malformed mixed scalar/vector shapes and mismatched lane counts
are rejected. Accepting vectors as values does not expand the separate memory-layout subset.

`ZigLean/Bit.lean` exposes zero-count lemmas, exact numeric count lemmas under a result-width
bound, shift result/overflow rules, and a connection to the checked exact-shift operation.
These are executable bitvector semantics and kernel-checked rules; they do not prove Zig Sema,
the exporter, normalization, emission, or backend preservation. Compiler-generated fixtures,
differential observations, shape rejection cases, loop-capture cases, and six semantic mutants
supply separate evidence. See `tests/roadmap/bitops/README.md` for the qualification commands.
