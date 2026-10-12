import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Init

/-!
# Partial and total correctness in the full-state logic (`docs/sep-full-state.md`)

`FTriple` is partial correctness: a run without a result satisfies every postcondition, also a
false one. `FTotalTriple` is `FTriple` and `FReturns`: neither divergence nor a panic has one from
a memory that holds the precondition (the start memory, `initRes_holds`). Neither has a panic
(`FTriple` admits only `.stackOverflow`). A returned Zig error is a value. A loop whose locals
count down returns (`FTotalTriple.loop_measure`, the body's step by `fsym`). The measure is not
optional: a step that does not decrease it is rejected, and a body that always repeats has no
step at all (the scenarios of the retired `loop_template` checks).
-/

namespace SepAuto.Total

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- A run without a result. -/
def diverge : MemM Unit := fun _ => ExceptT.mk none

/-- A safety panic. -/
def safetyPanic : MemM Unit := throw Error.panic

/-- Partial correctness admits divergence, with a false postcondition. -/
theorem diverge_partial (P : FAssn) : FTriple P diverge (fun _ _ => False) :=
  fun _ _ _ _ _ _ => trivial

/-- The start memory (no globals) and its resource. -/
theorem start (σ : Placement) :
    Holds (Mem.ofGlobals σ []) (initRes σ []) ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧
      globals [] (initRes σ []) ∧ (Mem.ofGlobals σ []).FSeq :=
  let h := initRes_holds σ [] (by decide)
  ⟨h.1, h.2, Mem.init_fseq σ [] (by simp [Mem.GlobalsFit])⟩

/-- No total triple for divergence from a memory that holds the precondition. -/
theorem diverge_not_total (Q : Unit → FAssn) (σ : Placement) :
    ¬ FTotalTriple (globals []) diverge Q := fun ht => by
  obtain ⟨hh, hp, hs⟩ := start σ
  obtain ⟨v, m', hr⟩ := ht.2 _ _ _ hh hp hs
  cases hr

/-- No triple at all for a panic: partial correctness rules out panics too. -/
theorem panic_not_partial (Q : Unit → FAssn) (σ : Placement) :
    ¬ FTriple (globals []) safetyPanic Q := fun ht => by
  obtain ⟨hh, hp, hs⟩ := start σ
  have := ht _ _ _ hh hp hs
  simp [safetyPanic] at this
  cases this

/-- A total triple is a partial one with the return witness, and back. -/
theorem total_iff (P : FAssn) (c : MemM Unit) (Q : Unit → FAssn) :
    FTotalTriple P c Q ↔ FTriple P c Q ∧ FReturns P c := Iff.rfl

/-- A returned Zig error is a value: total correctness holds. -/
theorem error_value (P : FAssn) :
    FTotalTriple P (pure (.error "OutOfMemory") : MemM (Except ErrName Unit)) (fun _ => P) := by
  fsym

/-- Count the locals down: repeat while the counter was nonzero. -/
def countdown : MM (BitVec 64) Bool := do
  let n ← get
  if n == 0 then pure false
  else
    let n' ← callR (Zig.sub false n 1)
    set n'
    pure true

/-- The loop returns, at `0`, keeping any frame. -/
theorem countdown_total (P : FAssn) (n : BitVec 64) :
    FTotalTriple P ((Zig.loop countdown fun b : Bool => b).run n) (fun r => ⟪r.1 = false ∧ r.2 = 0⟫ ⋆ P) :=
  FTotalTriple.loop_measure (fun _ => P) BitVec.toNat _
    (fun s => by unfold countdown; fsym) n

/-! ## The measure must decrease -/

/-- Locals of a counter loop with a bound. -/
structure L where
  i : BitVec 32
  n : BitVec 32
  deriving Inhabited

/-- `while (i < n) i -= 1`: the counter steps away from its bound. -/
def awayLoop : MM L Bool := do
  let i ← pure ((← get).i)
  let n ← pure ((← get).n)
  if Zig.lt false i n then do
    let i' ← callR (Zig.sub false i (1 : BitVec 32))
    modify (fun s => { s with i := i' })
    pure true
  else pure false

/-- `while (i < n) { if (i == 7) i = 0 else i += 1 }`: a counter that is also reset. -/
def resetLoop : MM L Bool := do
  let i ← pure ((← get).i)
  let n ← pure ((← get).n)
  if Zig.lt false i n then do
    if i == 7 then modify (fun s => { s with i := 0 })
    else do
      let i' ← callR (Zig.add false i (1 : BitVec 32))
      modify (fun s => { s with i := i' })
    pure true
  else pure false

/-- The distance of the counter to its bound. -/
def gap (s : L) : Nat := s.n.toNat - s.i.toNat

/-- Away from the bound, the counter itself decreases: the step holds with that measure. -/
theorem away_step (P : FAssn) (s : L) (h : 0 < s.i.toNat) :
    FTotalTriple P (awayLoop.run s)
      (fun r => if (fun b : Bool => b) r.1 then ⟪r.2.i.toNat < s.i.toNat⟫ ⋆ P else P) := by
  unfold awayLoop; fsym

set_option linter.unusedVariables false in
/-- … but not with the distance to the bound, which grows. -/
example (P : FAssn) (s : L) (h : 0 < s.i.toNat) : True := by
  fail_if_success
    have : FTotalTriple P (awayLoop.run s)
        (fun r => if (fun b : Bool => b) r.1 then ⟪gap r.2 < gap s⟫ ⋆ P else P) := by
      unfold awayLoop gap; fsym
  trivial

/-- Without a measure the reset loop's step holds (the bound is kept) … -/
theorem reset_step (P : FAssn) (s : L) :
    FTotalTriple P (resetLoop.run s)
      (fun r => if (fun b : Bool => b) r.1 then ⟪r.2.n = s.n⟫ ⋆ P else P) := by
  unfold resetLoop; fsym

set_option linter.unusedVariables false in
/-- … but a reset raises the distance to the bound: with it the step is rejected (from `i ≤ 7`
the loop runs forever when `n > 7`). -/
example (P : FAssn) (s : L) : True := by
  fail_if_success
    have : FTotalTriple P (resetLoop.run s)
        (fun r => if (fun b : Bool => b) r.1 then ⟪gap r.2 < gap s⟫ ⋆ P else P) := by
      unfold resetLoop gap; fsym
  trivial

/-- A body that always repeats. -/
def spin : MM Nat Bool := pure true

/-- No measure makes the step of a body that always repeats, from a memory that holds the
precondition. -/
theorem spin_no_measure (μ : Nat → Nat) (X : Nat → FAssn) (post : Bool × Nat → FAssn) (s : Nat)
    (σ : Placement) :
    ¬ FTotalTriple (globals []) (spin.run s)
      (fun r => if (fun b : Bool => b) r.1 then ⟪μ r.2 < μ s⟫ ⋆ X r.2 else post r) := fun ht => by
  obtain ⟨hh, hp, hs⟩ := start σ
  have := ht.1 _ _ _ hh hp hs
  simp only [spin, StateT.run_pure] at this
  obtain ⟨_, _, hq, _⟩ := this
  simp only [↓reduceIte] at hq
  exact Nat.lt_irrefl _ (sep_lift.mp hq).1

end SepAuto.Total
