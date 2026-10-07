# Checked vector addition proofs

`Proofs/Vectors/Proofs.lean` already contained `checkedAdd_ok` and
`checkedAdd_overflow`. They quantify over every pair of `Zig.Vec (BitVec 32) 4`
values. The historical T7 entry listed them as a gap; this inventory corrects
that clause without treating sampled differential outcomes as proofs.

The checked-in `Vectors.checkedAdd` definition in `Proofs/Vectors/Gen.lean`
runs `Zig.Vec.map2M (Zig.add false)` and returns its result. The proof unfolds
that definition, uses `Vec.map2M_four` to preserve lane order, and uses
`Zig.add_unsigned` for the unsigned scalar overflow condition. The new
classification and iff theorems compose these existing proofs.

| Theorem | Domain and conclusion |
|---|---|
| `Vectors.checkedAdd_ok` | If every lane's natural-number sum is below `2 ^ 32`, the result is the exact lane-wise bit-vector sum. |
| `Vectors.checkedAdd_overflow` | If any lane's natural-number sum is at least `2 ^ 32`, the result is `Zig.Error.overflow`. |
| `Vectors.checkedAdd_spec` | Without a premise, the result is overflow exactly when a finite lane witness overflows, otherwise the exact sum. |
| `Vectors.checkedAdd_overflow_iff` | The overflow result holds if and only if a lane overflows. |
| `Vectors.checkedAdd_ok_iff` | The exact successful sum holds if and only if every lane fits. |

The witnesses range over four lanes. The threshold is unsigned 32-bit
addition, including equality at `2 ^ 32`; these statements do not cover signed
addition, arbitrary vector lengths, floats, memory access or concurrent code.
The successful equation is stronger than a partial-correctness implication:
it identifies a returned value and excludes nontermination for these inputs.
Multiple overflowing lanes still give the same error, so the overflow proof
does not assume that the chosen witness is the first overflowing lane.

These are theorems about the generated Lean definition and the imported model.
They introduce no axioms, native evaluation or source-correspondence premise.
Kernel checking establishes those Lean statements; correspondence with Zig
source, compiler lowering and target behavior remains a separate qualification.

At revision `55783cc0a9936211b451ed3570cd3a0edf95c677`, root's serialized
checks with the pinned `leanprover/lean4:v4.34.0` toolchain built both vector
modules and kernel-checked their symbolic regressions against the unchanged
checked-in `Gen.lean`. The no-sorry gate and default full assumption audit
passed: 10,625 theorems across 114 shipped modules, with zero policy violations
and the existing policy unchanged. This run included no fresh Zig export or
source/target correspondence check.
The existing CI proof build includes both the theorem module and
`Proofs/Vectors/CheckedAdd.lean` through the `Proofs.+` glob. The latter
checks arbitrary-lane witnesses, exact-threshold overflow, both converses
and exclusion of the no-result outcome, using symbolic operands.
The unchanged checked-in vector translation is the initial qualification
input; version-specific freshly generated translations require their own
pipeline check.

## Memory layout

`ZigLean/Vec.lean` encodes `@Vector(n, uW)`, `@Vector(n, iW)` and `@Vector(n, fW)` in memory as
the LLVM backend lays them out (`Vec.packedEnc`): one little-endian integer of `n * W` bits, lane
`i` in bits `[i * W, (i + 1) * W)`, where `W` is the lane's bit size, not its ABI size. The ABI
size and alignment are both `⌈n * W / 8⌉` rounded up to a power of 2 (`packedVecLayout`, Zig's
`Type.abiSize`/`abiAlignment` for every backend except `stage2_c` and `stage2_x86_64`). Bits past
`n * W` and the bytes after them are padding (undefined). For byte-strided lanes (`u8`, `u32`,
`f64`, …) this is byte for byte the previous lanes-as-array encoding; `@Vector(n, bool)` keeps its
own bit-packed instance (`W = 1`).

| Theorem (`ZigLean/VecMem.lean`) | Statement |
|---|---|
| `intOfBytes_intBytes`, `intOfBytes_of_extract` | The bytes of an integer of any width read back as that integer. |
| `laneOf_packLanes` | Lane `i` of the packed integer is the `i`-th lane. |
| `Vec.packedEnc_lawful`; `LawfulEnc (Vec (BitVec w) n)`, `LawfulEnc (Vec (Float fmt) n)` | Every vector has an image of exactly `Enc.size` bytes, and decoding it gives the vector back (so `load_store_same`/`load_store_other` apply). |
| `Vec.set_lane_self`, `Vec.set_lane_ne` | A lane write replaces lane `i` and keeps every other lane. |
| `packLanes_set_mod`, `packLanes_set_shiftRight` | In the memory image, a write of lane `i` keeps every bit below bit `i * W` and every bit from `(i + 1) * W` up. |
| `laneOf_packBits_set_ne` | Lane `j ≠ i` of the image after a write of lane `i` is unchanged. |
| `Vec.storeLane_run`, `Vec.load_storeLane` | A lane store through memory (load, replace the lane, store) leaves `encode (v.set i x)` in the block; loading the vector back gives `v.set i x`. |

These are universal over lane width, lane count and lane values. They introduce no axioms.

Compiler evidence. `tests/roadmap/vector-layouts/probe.zig` prints the size, alignment and
in-memory bytes of 14 vectors (`u9`, `i9`, `u12`, `u4`, `u1`, `u24`, `u40`, `f80`, `bool` and
byte-lane controls), each before and after a store through a lane pointer `&v[i]`.
`tests/roadmap/vector-layouts/Model.lean` prints the same lines from `Enc.encode` and requires
them to be equal, line for line. Stock Zig 0.16.0 (`-fllvm`, aarch64-macos, Apple M1) gave
`aarch64-macos-ReleaseSafe.txt`; Debug and ReleaseFast gave identical output (layout evidence
only; ReleaseFast stays unqualified, [build-modes.md](build-modes.md)), and stock Zig
0.15.2 gave the same images. The probe also builds for baseline x86_64-linux-gnu and
aarch64-linux-gnu; CI runs it on its x86_64-linux host and compares that output too. The Linux ABI
probe (`tests/roadmap/abi-probes/probe.zig`, `scripts/abi-probe.py`) adds the layouts of
`@Vector(4, u9)`, `@Vector(3, u24)`, `@Vector(2, u40)` and `@Vector(5, bool)` and three packed
memory images to its exact contract.

Translator scope. The checker (`Check.lean`'s `modelLayout`) admits a vector with non-byte or
ABI-padded lanes in memory only when the AIR file's schema-12 profile names `stage2_llvm`
(`Layout.packedLanes`, set by `normalize`). The self-hosted x86_64 and C backends give such
lanes byte strides. Legacy schema-11 files carry no backend and stay rejected. The checker
still compares the model's size and alignment with the exporter's. A lane pointer into a
bit-packed vector, like one into a `bool` vector, stays rejected (`CheckCtx.itemAccess`): the
exporter does not write the pointer type's `vector_index`, so the lane is not known.
`Vec.storeLane` models such a store for the frame theorems only. `tests/roadmap/vector-layouts/Checker.lean` checks these
gates. Retranslating every committed golden and roadmap AIR set (54 inputs) gave byte-identical
output and diagnostics before and after this change. None of them has a schema-12 LLVM profile
with a non-byte vector in memory.
