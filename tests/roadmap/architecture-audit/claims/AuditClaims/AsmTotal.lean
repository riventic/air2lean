import Proofs.Asm.Gen
import ZigLean.Witness

/-!
C10 (S7, fixed): register-only inline asm was a *total* opaque function (ASM-01), so before the
fix the model could not fault: `Asm.divmod a 0 = pure …` was provable, although
`examples/asm/asm.zig`'s `divmod` runs `divl`, which traps (#DE / SIGFPE) for `b = 0`.

The block is now a defined function over the instruction model (A02 decision 1, premise ASM-07)
and the wrapper guards it with the block's own fault (`airIsa_<hash>_fault`,
`Zig.Asm.isaFault`): `div`'s #DE is part of the instruction's semantics, not an allowlist
entry's claim. The strongest hypothesis-free statement about a zero divisor is the trap
(`asm_divmod_total`: no claim derives from it). An exact-success equation needs the input to
avoid the fault (`asm_divmod_nonzero`), and the claim tooling lists the instruction-model
premise it rests on.
-/

namespace AuditClaims

theorem asm_divmod_total (a : BitVec 32) : Asm.divmod a 0 = throw Zig.Error.trap := by
  unfold Asm.divmod
  simp [zig_unfold]

theorem asm_divmod_nonzero (a b : BitVec 32) (hb : b ≠ 0) :
    Asm.divmod a b = pure (((a % b).setWidth 64 <<< 32) ||| (a / b).setWidth 64) := by
  unfold Asm.divmod
  have hf : Asm.airIsa_3653072158_fault a b = if b = 0 then some .trap else none := by
    simp [zig_unfold]
  have hv : Asm.airIsa_3653072158 a b = (a / b, a % b) := by simp [zig_unfold]
  rw [hf, hv]
  simp only [hb, ↓reduceIte]
  simp [zig_unfold, Zig.shl]

-- The fault-avoiding premise `b ≠ 0` is satisfiable.
nonvacuity_witness asm_divmod_nonzero := ⟨0, 1, by decide, trivial⟩

end AuditClaims
