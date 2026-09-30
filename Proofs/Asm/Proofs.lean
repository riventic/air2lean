import Proofs.Asm.Gen

/-!
# Proofs about `examples/asm/asm.zig`

`bswap32`/`lzcnt64`/`popcnt64` each lower to one `opaque` (M21: inline asm with register operands
only is translated as an opaque function per distinct `(source, constraints, operand widths)` --
see `docs/generated-code.md` § Inline asm). A proof here gets no built-in axiom about what the
instruction computes: every theorem states, as an explicit hypothesis, exactly the fact about the
opaque it needs, then derives a property of the generated wrapper from that fact alone.
-/

open Asm

/-- `bswap` is its own inverse on real x86_64 hardware. Stated as a hypothesis about the opaque
`airAsm_3500345798` (never assumed for free): applying `bswap32` twice returns the input. -/
theorem bswap32_involutive
    (hinv : ∀ x : BitVec 32, airAsm_3500345798 (airAsm_3500345798 x) = x) (x : BitVec 32) :
    (do let y ← bswap32 x; bswap32 y) = pure x := by
  unfold bswap32
  simp [zig_unfold, hinv]

/-- `popcnt` never sets more bits than the register width. Stated as a hypothesis about the
opaque `airAsm_4040357768`: its result, read as a natural number, never exceeds 64. -/
theorem popcnt64_le_width
    (hbound : ∀ x : BitVec 64, (airAsm_4040357768 x).toNat ≤ 64) (x : BitVec 64) :
    ∀ r, popcnt64 x = pure r → r.toNat ≤ 64 := by
  unfold popcnt64
  simp only [zig_unfold]
  intro r hr
  cases hr
  exact hbound x

/-- `lzcnt` of an all-ones register is 0 (no leading zero bit to count). Stated as a hypothesis
about the opaque `airAsm_3884223243`, applied to the all-ones input as the caller would state it
for that specific value. -/
theorem lzcnt64_allOnes
    (hz : airAsm_3884223243 (-1#64) = 0#64) : lzcnt64 (-1#64) = pure (0#64) := by
  unfold lzcnt64
  simp only [zig_unfold]
  rw [hz]

/-- `divl` with `edx = 0` gives the quotient and the remainder: two outputs, the second one a
store to the local `rem` (an lvalue output). Stated as a hypothesis about the opaque
`airAsm_2482283570`. Then `divmod` puts the remainder in the high 32 bits and the quotient in the
low 32 bits. -/
theorem divmod_spec (a b : BitVec 32)
    (hdiv : airAsm_2482283570 a b = (a / b, a % b)) :
    divmod a b = pure ((a % b).setWidth 64 <<< 32 ||| (a / b).setWidth 64) := by
  unfold divmod
  simp [zig_unfold, hdiv, Zig.shl]
