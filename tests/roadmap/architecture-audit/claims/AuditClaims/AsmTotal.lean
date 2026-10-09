import Proofs.Asm.Gen
import ZigLean.Witness

/-!
C10 (S7, fixed): register-only inline asm is a *total* opaque function (ASM-01), so before the
fix the model could not fault: `Asm.divmod a 0 = pure …` was provable, although
`examples/asm/asm.zig`'s `divmod` runs `divl`, which traps (#DE / SIGFPE) for `b = 0`.

Each allowlist entry now carries its fault condition (`Air2Lean/AsmAllowlist.lean`, premise
ASM-04) and the emitter guards the opaque with `Zig.asmTrap`. The strongest hypothesis-free
statement about a zero divisor is the trap (`asm_divmod_total`: no claim derives from it). An
exact-success equation needs the input to avoid the fault (`asm_divmod_nonzero`), and the claim
tooling lists the asm premises it rests on.
-/

namespace AuditClaims

theorem asm_divmod_total (a : BitVec 32) : Asm.divmod a 0 = throw Zig.Error.trap := by
  unfold Asm.divmod
  simp [zig_unfold]

theorem asm_divmod_nonzero (a b : BitVec 32) (hb : b ≠ 0) :
    Asm.divmod a b = pure (((Asm.airAsm_3653072158 a b).2.setWidth 64 <<< 32) |||
      (Asm.airAsm_3653072158 a b).1.setWidth 64) := by
  unfold Asm.divmod
  simp only [Zig.asmTrap, hb, ↓reduceIte]
  simp [zig_unfold, Zig.shl]

/-- The fault-avoiding premise `b ≠ 0` is satisfiable. -/
nonvacuity_witness asm_divmod_nonzero := ⟨0, 1, by decide, trivial⟩

end AuditClaims
