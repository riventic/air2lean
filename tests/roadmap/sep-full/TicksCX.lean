import ZigLean.Sep.Full.Cost
import ZigLean.Sep.Full.Init

/-!
# Step ticks: regressions (`docs/sep-full-state.md` §Step ticks)

1. `meter_cx` (memory side): the empty memory authorizes a frame with the credit authority `●0`,
   and after one step it does not (`TickAuth`: credits held plus steps run ≤ `0`).
2. `tick_without_credit` (T2, decision D3): `¬ FTriple emp Zig.tick (fun _ => emp)`. Under a held
   meter a step without a credit breaks every frame that holds `●0`, so a step needs `credits 1`
   or the plain mode (`FTotalTriple.tick_credit`, `tick_unmetered`, `tick_plain`).
3. `no_mint_spent` (T1): `¬ EUpd emp (spent 1)`: a receipt says a step has run.
4. `no_plain_under_meter` (T4): `¬ EUpd emp unmetered` next to a frame with `●0`: the plain mode
   cannot be entered while a meter runs, so credits cannot be minted through it.
5. `tick_credit_live` (T5, positive control): the start memory with one credit and the meter
   `●1` runs a step paid by the credit, with its receipt.
6. `two_steps_exact` / `two_steps_tight` (T6, exact cost): two steps are paid by two credits and
   return two receipts, so they count exactly two steps, and no proof pays them with one credit
   from the credit-free start (`FTotalTriple.not_fewer_credits`). `two_steps_plain`: the same
   proof gives the plain-mode statement (`FTotalTriple.of_credits_unmetered`). The cost rules are
   in `ZigLean/Sep/Full/Cost.lean`.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zig.Full.TicksCX

open Zig Zig.Full Zig.Full.FAssn

/-- The memory at program start with no globals. -/
abbrev m0 : Mem := Mem.ofGlobals Placement.fresh []

/-- The frame that holds the meter `●0`. -/
def rA : Res := ⟨FHeap.empty, Know.none, Ghost.credAuth 0⟩

theorem m0_ticks : m0.ticks = 0 := rfl

theorem m0_fseq : m0.FSeq := Mem.init_fseq _ [] (by decide)

theorem start_holds (N : Nat) :
    Holds m0 ⟨FHeap.empty, Know.none, Ghost.cred N⟩ ⟨FHeap.empty, Know.none, Ghost.credAuth N⟩ := by
  have h := (initRes_holds Placement.fresh [] (by simp)).1
  have e : initRes Placement.fresh [] = ⟨FHeap.empty, Know.none, Ghost.unit⟩ := rfl
  rw [e] at h
  have h2 := Holds.addCredits N h (by simp) (by simp) (by simp)
  simp only [Ghost.unit_add, m0_ticks, Nat.zero_add] at h2
  exact h2

theorem start_holds_auth : Holds m0 ⟨FHeap.empty, Know.none, Ghost.unit⟩ rA := by
  have := start_holds 0
  rw [Ghost.cred_zero] at this
  exact this

/-- **The meter, memory side**: `●0` is authorized before a step and not after it. -/
theorem meter_cx : TickAuth m0 (ACell.authAt .cred 0) ∧ ¬ TickAuth m0.ticked (ACell.authAt .cred 0) :=
  ⟨⟨fun L hL => by
      simp at hL ⊢
      by_cases e : L = 0
      · subst e; simp [m0_ticks]
      · simp [e] at hL, by simp, fun h => by simp at h⟩, fun h => by
    have := h.meter 0 (by simp)
    simp [m0_ticks] at this⟩

theorem tick_m0 : ((Zig.tick).run m0).run = some (.ok ((), m0.ticked)) := rfl

/-- **T2: a step without a credit or the plain mode is not provable** (decision D3). -/
theorem tick_without_credit : ¬ FTriple emp Zig.tick (fun _ => emp) := by
  intro h
  have := h m0 _ rA start_holds_auth ⟨rfl, rfl, rfl⟩ m0_fseq
  rw [tick_m0] at this
  obtain ⟨r', hh', hq, -⟩ := this
  have := hh'.ghost.2.2.2.tick.meter 0 (by simp [hq.2.2, rA, Ghost.credAuth])
  simp [hq.2.2, rA, Ghost.credAuth, m0_ticks] at this

/-- **T1: no update creates a receipt.** -/
theorem no_mint_spent : ¬ EUpd emp (spent 1) := by
  intro h
  obtain ⟨r', hh, hc⟩ := h m0 _ rA start_holds_auth ⟨rfl, rfl, rfl⟩ m0_fseq
  have := hh.ghost.2.2.2.tick.spent
  simp [hc.2.2, rA, Ghost.credAuth, m0_ticks] at this

/-- **T4: no update enters the plain mode under a meter.** -/
theorem no_plain_under_meter : ¬ EUpd emp unmetered := by
  intro h
  obtain ⟨r', hh, hc⟩ := h m0 _ rA start_holds_auth ⟨rfl, rfl, rfl⟩ m0_fseq
  have := hh.ghost.2.2.2.tick.plain (by simp [hc.2.2, rA, Ghost.credAuth]) 0
  simp [hc.2.2, rA, Ghost.credAuth] at this

/-- **T5: a step paid by a credit runs**, with its receipt, next to the meter `●1`. -/
theorem tick_credit_live :
    ∃ r', Holds m0.ticked r' ⟨FHeap.empty, Know.none, Ghost.credAuth 1⟩ ∧ spent 1 r' := by
  obtain ⟨v, m', r', hr, hh, hq, -⟩ :=
    FTotalTriple.tick_credit.runs (start_holds 1) ⟨rfl, rfl, rfl⟩ m0_fseq
  rw [tick_run'] at hr
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj hr)
  exact ⟨r', hh, hq⟩

/-- Two steps. -/
def twoSteps : MemM Unit := do
  Zig.tick
  Zig.tick

/-- **T6, positive**: two credits pay two steps, which return two receipts. -/
theorem two_steps_exact : FTotalTriple (emp ⋆ credits 2) twoSteps (fun _ => emp ⋆ spent 2) := by
  have h₁ : FTotalTriple (credits 1 ⋆ credits 1) Zig.tick (fun _ => spent 1 ⋆ credits 1) :=
    FTotalTriple.tick_credit.frame
  have h₂ : FTotalTriple (credits 1 ⋆ spent 1) Zig.tick (fun _ => spent 1 ⋆ spent 1) :=
    FTotalTriple.tick_credit.frame
  refine (h₁.bind fun _ => h₂.pre fun _ h => sep_comm h).conseq (fun _ h => ?_) fun _ _ h => ?_
  · rw [show (2 : Nat) = 1 + 1 from rfl, credits_add] at h
    exact sep_emp.mp (sep_comm h)
  · rw [show (2 : Nat) = 1 + 1 from rfl, spent_add]
    exact sep_comm (sep_emp.mpr h)

/-- The empty start memory holds nothing with nothing in the frame: a credit-free start. -/
theorem start_unit : Holds m0 ⟨FHeap.empty, Know.none, Ghost.unit⟩ ⟨FHeap.empty, Know.none, Ghost.unit⟩ :=
  (initRes_holds Placement.fresh [] (by simp)).1

/-- **T6, negative**: one credit does not pay the two steps, whatever the postcondition. -/
theorem two_steps_tight (Q : Unit → FAssn) : ¬ FTotalTriple (emp ⋆ credits 1) twoSteps Q :=
  FTotalTriple.not_fewer_credits two_steps_exact (by decide) start_unit ⟨rfl, rfl, rfl⟩ m0_fseq
    ⟨by simp, by simp, by simp, by simp⟩

/-- **T6, plain mode**: the cost proof gives the plain-mode statement. -/
theorem two_steps_plain : FTotalTriple (emp ⋆ unmetered) twoSteps (fun _ => (emp ⋆ spent 2) ⋆ unmetered) :=
  two_steps_exact.of_credits_unmetered

end Zig.Full.TicksCX

#print axioms Zig.Full.TicksCX.meter_cx
#print axioms Zig.Full.TicksCX.tick_without_credit
#print axioms Zig.Full.TicksCX.no_mint_spent
#print axioms Zig.Full.TicksCX.no_plain_under_meter
#print axioms Zig.Full.TicksCX.tick_credit_live
#print axioms Zig.Full.TicksCX.two_steps_exact
#print axioms Zig.Full.TicksCX.two_steps_tight
#print axioms Zig.Full.TicksCX.two_steps_plain
