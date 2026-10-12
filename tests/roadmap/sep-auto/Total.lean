import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Init

/-!
# Partial and total correctness in the full-state logic (`docs/sep-full-state.md`)

`FTriple` is partial correctness: a run without a result satisfies every postcondition, also a
false one. `FTotalTriple` is `FTriple` and `FReturns`: neither divergence nor a panic has one from
a memory that holds the precondition (the start memory, `initRes_holds`). Neither has a panic
(`FTriple` admits only `.stackOverflow`). A returned Zig error is a value. A loop whose locals
count down returns (`FTotalTriple.loop_measure`, the body's step by `fsym`).
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
  ⟨(initRes_holds σ [] (by decide)).1, (initRes_holds σ [] (by decide)).2,
    Mem.init_fseq σ [] (by simp [Mem.GlobalsFit])⟩

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

end SepAuto.Total
