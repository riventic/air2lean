import Proofs.Asm.Gen

/-!
C10: register-only inline asm is a *total* opaque function (ASM-01), so the model cannot fault.
`examples/asm/asm.zig`'s `divmod` runs `divl`, which traps (#DE / SIGFPE) for `b = 0`; the
differential inputs exclude `b = 0` (`tests/diff/gen_inputs.zig`: "0 is a CPU fault").
Without any hypothesis about the instruction, the generated wrapper provably returns for every
input, `0` included: an exact-success equation that `scripts/claims.py` classifies as
`total_correctness` (no-panic + guaranteed-return) for code that crashes natively.
-/

namespace AuditClaims

theorem asm_divmod_total (a : BitVec 32) :
    Asm.divmod a 0 = pure (((Asm.airAsm_3653072158 a 0).2.setWidth 64 <<< 32) |||
      (Asm.airAsm_3653072158 a 0).1.setWidth 64) := by
  unfold Asm.divmod
  simp [zig_unfold, Zig.shl]

end AuditClaims
