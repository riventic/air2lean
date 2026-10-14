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
4. `no_mint_ep`: epoch tokens (§Epoch tokens) are not mintable either: no ghost update creates the
   whole token of a ledger's current epoch next to its authority, because the frame may hold it
   (`Upd.alloc` hands it out with the ledger); only `Upd.alloc` and `Upd.bump` mint one, for a
   new epoch.

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
  have h2 := Holds.addCredits 0 h (by simp) (by simp) (by simp)
  have e2 : m0.ticks + 0 = 0 := rfl
  simp only [Ghost.cred_zero, Ghost.add_unit, Ghost.unit_add, e2] at h2
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
  obtain ⟨r', hc, -, -, -, -, ha, -, -⟩ := h ⟨FHeap.empty, Know.none, Ghost.unit⟩ ⟨rfl, rfl, rfl⟩ _ hok
  have := congrArg (fun c : KCell => c.frag .cred) ha
  simp [hc.2.2, Ghost.cred] at this

/-- **No ghost update mints an epoch token** of the current epoch: a fresh ledger (`Upd.alloc`)
comes with its epoch's whole token, which the frame then holds. -/
theorem no_mint_ep :
    ¬ ∀ γ, Upd (gauth γ 0 GMap.empty) (gauth γ 0 GMap.empty ⋆ epTok γ 0 Frac.one) := by
  intro hm
  obtain ⟨r, ⟨γ, hr⟩, -, -, -, -, -, hok, -⟩ :=
    Upd.alloc none ⟨FHeap.empty, Know.none, Ghost.unit⟩ ⟨rfl, rfl, rfl⟩ Ghost.unit (GOk.unit (m := m0)).1
  rw [gauth_epTok hr] at hok
  have hok' : Ghost.Ok (Ghost.at γ (GCell.auth1 0 GMap.empty none)) (Ghost.at γ (GCell.ep1 0 Frac.one)) := by
    unfold Ghost.Ok at hok ⊢; rwa [Ghost.add_unit, ← Ghost.at_add] at hok
  obtain ⟨r', hr', -, -, -, -, -, hok2, -⟩ :=
    hm γ ⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 0 GMap.empty none)⟩ ⟨rfl, rfl, rfl⟩ _ hok'
  rw [gauth_epTok hr'] at hok2
  have hv := hok2.1.1 γ
  simp only [Ghost.add, Ghost.at, ↓reduceIte] at hv
  rw [GCell.add_assoc, GCell.valid_auth1_add] at hv
  have h := hv.2.2.2.1 0
  simp only [GCell.add_ep_val, GCell.ep1_ep_val, ↓reduceIte] at h
  have : Frac.one.val = 1 := rfl
  grind

end Zig.Full.CreditsCX

#print axioms Zig.Full.CreditsCX.start_holds_auth
#print axioms Zig.Full.CreditsCX.no_mint_eupd
#print axioms Zig.Full.CreditsCX.no_mint_upd
#print axioms Zig.Full.CreditsCX.no_mint_ep
