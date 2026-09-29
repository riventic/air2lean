import ZigLean.Conc.Basic
import ZigLean.Basic

/-!
# Calls and sync ops in a concurrent function

`Zig.CM Tgt σ α`: the body monad of a concurrent function, its locals over `ConcM`. The lifts
of calls to the other function kinds (`callMC`, `callRC`), the sync ops that `Emit.lean` writes
(`yieldC` before each atomic op, `spawnC`, `joinC`), and the lemmas that `partial_fixpoint` needs
to see through them (as `ZigLean/Mem/Basic.lean` has for `MM`).
-/

namespace Zig

/-- The body monad of a concurrent function. -/
abbrev CM (Tgt σ α : Type) := StateT σ (ConcM Tgt) α

variable {Tgt σ α : Type}

/-- A call from a concurrent function to another one. -/
@[inline] def callC (r : ConcM Tgt α) : CM Tgt σ α := StateT.lift r

/-- A call from a concurrent function to a function that uses memory: no stop. -/
@[inline] def callMC (r : MemM α) : CM Tgt σ α := StateT.lift (ConcM.liftMem r)

/-- A call from a concurrent function to a pure function. -/
@[inline] def callRC (r : Result α) : CM Tgt σ α := StateT.lift (ConcM.liftMem (StateT.lift r))

/-- Another thread can run first: before each atomic op. -/
def yieldC : CM Tgt σ Unit := StateT.lift (discard (ConcM.sync (Tgt := Tgt) .yield))

/-- `Thread.spawn` of the target `t`: never fails (`docs/std-models.md` §Thread model). -/
def spawnC (t : Tgt) : CM Tgt σ (Except ErrName ThreadId) := do
  let tid ← StateT.lift (ConcM.sync (.spawn t))
  pure (.ok tid)

/-- `Thread.join`: waits until thread `tid` ends. -/
def joinC (tid : ThreadId) : CM Tgt σ Unit := StateT.lift (discard (ConcM.sync (Tgt := Tgt) (.join tid)))

section Monotone
open Lean.Order

theorem ConcM.monotone_liftMem {γ : Type} [PartialOrder γ] (f : γ → MemM α) (hmono : monotone f) :
    monotone (fun x => (ConcM.liftMem (f x) : ConcM Tgt α)) := by
  intro x₁ x₂ hx n m
  have h : (f x₁).run m ⊑ (f x₂).run m := hmono x₁ x₂ hx m
  show CoN.le (.leaf ((f x₁).run m)) (.leaf ((f x₂).run m))
  generalize (f x₁).run m = a at h ⊢
  generalize (f x₂).run m = b at h ⊢
  cases h with
  | bot => exact .bot _
  | refl => exact CoN.le_refl _

@[partial_fixpoint_monotone]
theorem monotone_callC {γ : Type} [PartialOrder γ] (f : γ → ConcM Tgt α) (hmono : monotone f) :
    monotone (fun (x : γ) => (callC (f x) : CM Tgt σ α)) := by
  apply monotone_of_monotone_apply
  intro s
  show monotone (fun x => (f x) >>= fun a => pure (a, s))
  exact monotone_bind _ _ _ hmono (monotone_const _)

@[partial_fixpoint_monotone]
theorem monotone_callMC {γ : Type} [PartialOrder γ] (f : γ → MemM α) (hmono : monotone f) :
    monotone (fun (x : γ) => (callMC (f x) : CM Tgt σ α)) :=
  monotone_callC _ (ConcM.monotone_liftMem f hmono)

@[partial_fixpoint_monotone]
theorem monotone_callRC {γ : Type} [PartialOrder γ] (f : γ → Result α) (hmono : monotone f) :
    monotone (fun (x : γ) => (callRC (f x) : CM Tgt σ α)) := by
  apply monotone_callC _ (ConcM.monotone_liftMem _ _)
  apply monotone_of_monotone_apply
  intro m
  show monotone (fun x => (f x) >>= fun a => pure (a, m))
  exact monotone_bind _ _ _ hmono (monotone_const _)

@[partial_fixpoint_monotone]
theorem monotone_runCM' {γ : Type} [PartialOrder γ] (f : γ → CM Tgt σ α) (hmono : monotone f)
    (s : σ) : monotone (fun (x : γ) => (f x).run' s) := by
  have h := Functor.monotone_map (fun x => StateT.run (f x) s) (·.1) (monotone_stateTRun f hmono s)
  simpa [StateT.run', StateT.run] using h

@[partial_fixpoint_monotone]
theorem monotone_loopCM {ε γ : Type} [PartialOrder γ] (f : γ → CM Tgt σ ε) (again : ε → Bool)
    (hmono : monotone f) : monotone (fun (x : γ) => loop (f x) again) := by
  intro x1 x2 hx
  have hle : f x1 ⊑ f x2 := hmono x1 x2 hx
  apply loop.fixpoint_induct (f x1) again (motive := fun v => v ⊑ loop (f x2) again)
  · exact fun _ hc h => csup_le hc h
  · intro l hl
    rw [loop.eq_1 (f x2) again]
    apply PartialOrder.rel_trans (MonoBind.bind_mono_left hle)
    apply MonoBind.bind_mono_right
    intro e
    split
    · exact hl
    · exact PartialOrder.rel_refl

end Monotone

end Zig
