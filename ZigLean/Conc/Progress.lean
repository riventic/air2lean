import ZigLean.Conc.Logic

/-!
# Source progress hints

The spin hint (the `pause`/`isb` instruction of `std.atomic.spinLoopHint`) exposes a
scheduling opportunity. It adds no happens-before edge, memory fence, time observation, or
fairness premise. `std.Thread.yield` is translated from its std code down to `sched_yield`
(OSY-01, `ZigLean/Os/Thread.lean`), which is the same kind of scheduling opportunity.
-/

namespace Zig

/-- A spin hint permits another ready thread to run, including choosing this thread again. -/
def spinLoopHint {Tgt : Type} : ConcM Tgt Unit := ConcM.sync .yield

/-- Body-monad form used by generated code. -/
def spinLoopHintC {Tgt σ : Type} : CM Tgt σ Unit := StateT.lift spinLoopHint

/-- The hint retains the no-result outcome at depth zero. -/
theorem spinLoopHint_zero {Tgt : Type} (m : Mem) :
    spinLoopHint (Tgt := Tgt) 0 m = .leaf none := rfl

namespace Conc.Proto.WP

variable {Tgt γ : Type} {P : Conc.Proto Tgt γ} {t : ThreadId}
  {G : ThreadId → γ} {m : Mem} {n : Nat}

/-- Safety rule: establish the invariant at the hint, then prove the continuation from every
interference state satisfying it. This makes no claim that the continuation will run. -/
theorem spinLoopHint {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (Conc.upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ → Q () G₁ { m₁ with current := t } k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Zig.spinLoopHint : ConcM Tgt Unit) Q G m n :=
  sync h hcost

end Conc.Proto.WP
end Zig
