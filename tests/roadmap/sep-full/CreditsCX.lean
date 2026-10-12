import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.Logic

/-!
# Credits are not mintable: regressions (`docs/sep-full-state.md` §Credits and room)

1. `start_holds_auth`: the memory at program start holds `emp` with the credit authority `●0` in
   the frame (`Holds.addCredits`, the adequacy step).
2. `no_mint_eupd`: `¬ EUpd emp (credits 1)`: no frame-preserving update creates a credit, because
   `EUpd` quantifies over that frame.
3. `no_mint_upd`: `¬ Upd emp (credits 1)`, for the same reason (`Upd` quantifies over every ghost
   frame that composes).

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zig.Full.CreditsCX

open Zig Zig.Full Zig.Full.FAssn

/-- The memory at program start with no globals. -/
abbrev m0 : Mem := Mem.ofGlobals Placement.fresh []

/-- The frame that holds the credit authority `●0`. -/
def rA : Res := ⟨FHeap.empty, Know.none, Ghost.credAuth 0⟩

theorem start_holds_auth : Holds m0 ⟨FHeap.empty, Know.none, Ghost.unit⟩ rA := by
  have h := (initRes_holds Placement.fresh [] (by simp)).1
  have e : initRes Placement.fresh [] = ⟨FHeap.empty, Know.none, Ghost.unit⟩ := rfl
  rw [e] at h
  have h2 := Holds.addCredits 0 h (by simp)
  simp only [Ghost.cred_zero, Ghost.add_unit, Ghost.unit_add] at h2
  exact h2

theorem m0_fseq : m0.FSeq := Mem.init_fseq _ [] (by decide)

/-- **No update creates a credit.** -/
theorem no_mint_eupd : ¬ EUpd emp (credits 1) := by
  intro h
  obtain ⟨r', hh, hc⟩ := h m0 _ rA start_holds_auth ⟨rfl, rfl, rfl⟩ m0_fseq
  have := hh.credits_le (R := emp) (R' := emp) (sep_emp.mpr hc) (sep_emp.mpr ⟨rfl, rfl, rfl⟩)
  omega

/-- **No ghost update creates a credit.** -/
theorem no_mint_upd : ¬ Upd emp (credits 1) := by
  intro h
  have hok : Ghost.Ok Ghost.unit (Ghost.credAuth 0) := start_holds_auth.ghost.1
  obtain ⟨r', hc, hh, hk, -, -, hok', -⟩ := h ⟨FHeap.empty, Know.none, Ghost.unit⟩ ⟨rfl, rfl, rfl⟩ _ hok
  obtain ⟨-, -, -, h3⟩ := hok'.1
  have := h3.2.2 0 (by simp [Ghost.credAuth, Ghost.unit, CCell.add, CCell.unit])
  simp [hc.2.2, Ghost.cred, CCell.add, Ghost.credAuth, Ghost.unit] at this

end Zig.Full.CreditsCX

#print axioms Zig.Full.CreditsCX.start_holds_auth
#print axioms Zig.Full.CreditsCX.no_mint_eupd
#print axioms Zig.Full.CreditsCX.no_mint_upd
