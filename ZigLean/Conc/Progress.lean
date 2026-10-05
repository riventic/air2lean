import ZigLean.Conc.Logic

/-!
# Source progress hints

Hints expose a scheduling opportunity. They add no happens-before edge, memory fence,
time observation, or fairness premise. `Thread.yield` also exposes its source error result;
ordinary Zig errors are values of `Except ErrName`, not `Zig.Error` failures.
-/

namespace Zig

/-- The two conservative environment outcomes of `std.Thread.yield`. Option zero succeeds;
option one is the source error. Supported Zig versions all declare `SystemCannotYield`.
Older Windows implementations always succeed, so that target gets an extra model outcome. -/
def threadYieldResult (choice : Nat) : Except ErrName Unit :=
  if choice = 0 then .ok () else .error "SystemCannotYield"

/-- A spin hint permits another ready thread to run, including choosing this thread again. -/
def spinLoopHint {Tgt : Type} : ConcM Tgt Unit := ConcM.sync .yield

/-- A yield permits scheduling and chooses success or `error.SystemCannotYield` without
changing memory itself. It does not require any other thread to run. -/
def threadYield {Tgt : Type} : ConcM Tgt (Except ErrName Unit) := do
  let choice ← ConcM.sync (.choose 2)
  pure (threadYieldResult choice)

/-- Body-monad forms used by generated code. -/
def spinLoopHintC {Tgt σ : Type} : CM Tgt σ Unit := StateT.lift spinLoopHint

def threadYieldC {Tgt σ : Type} : CM Tgt σ (Except ErrName Unit) := StateT.lift threadYield

/-- Exhaustive source result domain, independent of the scheduling oracle. -/
theorem threadYieldResult_valid (c : Nat) :
    threadYieldResult c = .ok () ∨ threadYieldResult c = .error "SystemCannotYield" := by
  unfold threadYieldResult
  split <;> simp

/-- Both modeled source operations retain the no-result outcome at depth zero. -/
theorem spinLoopHint_zero {Tgt : Type} (m : Mem) :
    spinLoopHint (Tgt := Tgt) 0 m = .leaf none := rfl

theorem threadYield_zero {Tgt : Type} (m : Mem) :
    threadYield (Tgt := Tgt) 0 m = .leaf none := rfl

namespace Conc.Proto.WP

variable {Tgt γ : Type} {P : Conc.Proto Tgt γ} {t : ThreadId}
  {G : ThreadId → γ} {m : Mem} {n : Nat}

/-- Safety rule: establish the invariant at the hint, then prove the continuation from every
interference state satisfying it. This makes no claim that the continuation will run. -/
theorem spinLoopHint {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (Conc.upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ → Q () G₁ { m₁ with current := t } k) :
    P.WP t (Zig.spinLoopHint : ConcM Tgt Unit) Q G m n := by
  exact sync h

/-- Safety/partial-correctness rule for yield: both ordinary source returns need a postcondition
at every permitted interference state. No fairness or eventual-success premise is hidden. -/
theorem threadYield {Q : Except ErrName Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (Conc.upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
        ∀ c, c < 2 → Q (threadYieldResult c) G₁ { m₁ with current := t } k) :
    P.WP t (Zig.threadYield : ConcM Tgt (Except ErrName Unit)) Q G m n := by
  apply bind
  apply sync
  intro k hk
  obtain ⟨g, hi, hq⟩ := h k hk
  refine ⟨g, hi, fun G₁ m₁ hg hi₁ c hc => ?_⟩
  apply pure'
  exact hq G₁ m₁ hg hi₁ c (by omega)

end Conc.Proto.WP
end Zig
