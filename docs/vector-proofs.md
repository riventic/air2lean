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
