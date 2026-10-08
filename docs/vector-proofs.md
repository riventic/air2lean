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
bit-packed vector is a bit-pointer (§Lane pointers). `Vec.storeLane` (a whole-vector load and
store) models a lane write for the frame theorems above. `tests/roadmap/vector-layouts/Checker.lean`
checks these gates. Retranslating every committed golden and roadmap AIR set (54 inputs) gave byte-identical
output and diagnostics before and after this change. None of them has a schema-12 LLVM profile
with a non-byte vector in memory.

## Lane pointers

Zig gives `&v[i]` of `@Vector(n, T)`, where `T` is `bool` or an integer whose bit size `w` is not
a power-of-two number of bytes (`u3`, `u9`, `u24`), the type `*align(a:0:n:i) T`: a pointer to the
vector itself, whose type carries the lane count as `host_size` and the comptime lane as
`vector_index` (Sema's `elemPtrVector`). The LLVM backend loads the whole `<n x iw>` vector,
extracts or inserts lane `i` and stores the vector back. The translator reuses the bit-pointer
encoding of a packed field pointer (host size, bit offset): `normalize` (`lanePtrLayout`) gives
such a pointer the host `⌈n * w / 8⌉` bytes, the vector's integer and LLVM's store size, and the
bit offset `i * w`. `ptr_elem_ptr` returns the vector pointer, and a load or store through the
pointer, also as a parameter or a call argument, is `Zig.loadLane`/`Zig.storeLane`
(`ZigLean/Packed.lean`). They work on the bits of the host bytes: a load needs only the lane's
bits defined, and a store replaces only the lane's bits, so a vector filled lane by lane from
`undefined` (as Zig initializes `var v: V = .{…}`) is defined. A `Byte` has a defined low prefix
only: a lane store whose bits start above the defined bits of a byte leaves that byte as it was,
and the lane then reads as `.unspecified`, never as a wrong value.

| Theorem (`ZigLean/VecMem.lean`) | Statement |
|---|---|
| `testBit_setBits`, `packLanes_set`, `Vec.packBits_set` | A lane write is `setBits` of the lane's bits in the vector's integer: bits outside `[i * w, (i + 1) * w)` keep their value. |
| `intBytes_setLane` | The byte-wise lane write of `Zig.storeLane` on the bytes of an integer gives the bytes of the integer with the lane's bits replaced. |
| `hostVal_intBytes`, `laneDefined_intBytes` | The host bytes of an integer read back as the integer, with every lane bit defined. |
| `Vec.host_of_encode` | The host bytes of a vector in memory are the first `⌈n * w / 8⌉` bytes of its image. |
| `Vec.loadLane_vec` | A load through `&v[i]` from a vector's bytes reads `v[i]` and only the host bytes. |
| `Vec.storeLane_vec` | A store of `x` through `&v[i]` writes exactly the host bytes of `v.set i x`; no other byte changes. |
| `Vec.load_storeLane_vec` | The whole vector loaded after the store is `v.set i x`: lane `i` is `x`, every other lane keeps its value (`Vec.set_lane_ne`). |

These are universal over lane width, lane count, lane index and values, for every lane type
with a `Zig.Packed` instance (`BitVec w`, `Bool`). They introduce no axioms.

Compiler evidence. `tests/roadmap/vector-layouts/lanes.zig` exercises `u9`, `u3`, `u24` and `bool`
lane pointers, as locals and as parameters of non-inlined functions; its `zig test` checks every
result natively (stock Zig 0.16.0, `-fllvm`, ReleaseSafe, aarch64-macos; CI on x86_64-linux).
`air/0.16.0` and `air/0.15.2` are the AIR that the patched compilers exported from it
(`-target x86_64-linux -mcpu=baseline`, LLVM backend): both versions give the same lane-pointer
shape (`ptr_elem_ptr` with `vector_index`, the lane count as `host_size`), and only the lane
pointer's alignment differs. `Lanes/Gen.lean` is the 0.16.0 translation; `Lanes/Proofs.lean`
proves on it that `getU3(&v[5])` reads lane 5, that `putU3(&v[5], x)` leaves `v.set 5 x` and
that `flipBool(&v[3])` negates lane 3 of a `bool` vector, for every vector in memory;
`Lanes/Checks.lean` kernel-checks every input of the native test against the translation of
each version. `probe.zig` adds, for each integer or `bool` lane-pointer case, a load through
another lane's pointer and the bytes after the host after a lane store (set to `a5` before):
the store writes only the host bytes. `Model.lean` computes those lines with
`Zig.loadLane`/`Zig.storeLane` and checks that each lane store leaves the image of `Vec.set`.
Stock Zig 0.16.0 (ReleaseSafe, Debug, ReleaseFast) and 0.15.2 printed the same lines on
aarch64-macos (layout evidence only; ReleaseFast stays unqualified, [build-modes.md](build-modes.md)).
Under emulated x86_64-linux (Docker `linux/amd64`, stock Zig 0.16.0 `x86_64-linux` release),
`lanes.zig`'s test passed and the probe printed the same lines; CI runs both natively.

Scope. The lane layout is LLVM's (LangRef: a vector of non-byte lanes is laid out as its
bit-cast integer, lane 0 in the low bits on little-endian targets); the translator admits it
only where the probe and `lanes.zig` run natively: an LLVM-backend profile on x86_64 or aarch64.
Other LLVM targets, the self-hosted x86_64 and C backends, legacy schema-11 files, float lanes (`f80`) and 0.14.1/0.15.2 runtime lanes stay
rejected. An `undefined` store through a lane pointer is rejected, as for a packed field.

Lane reads. `v.*[i]` through a pointer to a bit-packed vector is a lane pointer and a `load` in
0.16.0 (`Zig.loadLane`), and a whole-vector `load` then `array_elem_val` in 0.15.2; canonicalization
(`itemReads`) folds neither into a byte-strided `ptr_elem_val` when the lanes are `bool` or not a
power-of-two number of bytes, so 0.15.2 reads the vector with its bit-packed encoding and picks the
lane. `lane_reads.zig` checks both translations against its native values
(`test_lane_reads.py`). A `ptr_elem_val` through such a vector pointer, with a comptime or runtime
index, is rejected (`CheckCtx.itemAccess`), as is a `ptr_elem_ptr` with a runtime index (as a lane
pointer, a 0.14.1/0.15.2 `"runtime"` lane pointer or a plain item pointer), for every supported
version; Zig 0.16.0 itself rejects a runtime lane index of a vector.
