import ZigLean.Conc.Logic
import ZigLean.Conc.Call
import ZigLean.Mem.Reuse

/-!
# A weakest precondition at a concrete run

The rules of `ZigLean/Conc/Logic.lean` and `ZigLean/Conc/Lemmas.lean` prove `Proto.WP` of code.
A counterexample to such a statement (a kernel-checked witness that some code does *not* meet a
contract, e.g. `tests/roadmap/sep-full/RelaxedUnlockCX.lean`) goes the other way: from `WP` of a
run whose memory steps the kernel computes, it reads the post at the run's actual end. These are
the inversions of the rules for the shapes generated code has, once for every protocol:

- `WP.pick_inv`: a stop where the oracle picks (`SyncOp.pick`, the start of every atomic op,
  `atomicRmwAsC`, `cmpxchgAsC`): the ghost value the thread stopped with keeps the invariant, and
  the rest holds for every environment that keeps it and for every pick;
- `WP.liftMem_bind_inv`, `WP.liftMem_inv`, `WP.pure_inv`: a `MemM` step that returns, and the end;
- `pickCall_eq`: a pick and the `MemM` step it chooses (`do let c ← pickC count; callMC (x c)`)
  as `ConcM` binds, the form the inversions read.

The memory a step returns is `resMem` of its run; `run_of_value` turns the value that the kernel
computes (`runValue`, `decide +kernel`) into the run with that memory, so later steps run from a
closed term.
-/

namespace Zig

/-- The memory a run returns (the empty memory where it returns none or throws). -/
def resMem {α : Type} : Option (Except Error (α × Mem)) → Mem
  | some (.ok (_, m)) => m
  | _ => {}

/-- **A run whose value the kernel computed** returns `resMem` of itself. -/
theorem run_of_value {α : Type} {x : MemM α} {m : Mem} {a : α}
    (h : runValue x m = some (.ok a)) : (x.run m).run = some (.ok (a, resMem (x.run m).run)) := by
  unfold runValue at h
  cases e : (x.run m).run with
  | none => rw [e] at h; cases h
  | some r =>
    rw [e] at h
    cases r with
    | error => cases h
    | ok p =>
      obtain ⟨a', m'⟩ := p
      simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq] at h
      subst h; rfl

namespace Conc
namespace Proto

variable {Tgt γ α β σ : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}

/-- **A stop where the oracle picks**: the thread stopped with some ghost value that keeps the
invariant, and for every environment that keeps it and every pick the rest holds. -/
theorem WP.pick_inv {count : Mem → Nat} {f : Nat → ConcM Tgt β}
    {Q : β → (ThreadId → γ) → Mem → Nat → Prop} {n : Nat}
    (h : P.WP t (ConcM.sync (.pick count) >>= f) Q G m (n + 1)) :
    ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ → t < m₁.threads.size →
      ∀ c, (c < count { m₁ with current := t } ∨ count { m₁ with current := t } = 0 ∧ c = 0) →
        P.WP t (f c) Q G₁ { m₁ with current := t } n := by
  obtain ⟨-, g, hi, -, hk⟩ := h
  exact ⟨g, hi, fun G₁ m₁ hg hi₁ ht c hc => hk G₁ m₁ hg hi₁ ht c hc⟩

/-- **A `MemM` step that returns**: the rest runs from its memory. -/
theorem WP.liftMem_bind_inv {x : MemM α} {f : α → ConcM Tgt β}
    {Q : β → (ThreadId → γ) → Mem → Nat → Prop} {n : Nat} {a : α} {m' : Mem}
    (h : P.WP t (ConcM.liftMem x >>= f) Q G m n) (hr : (x.run m).run = some (.ok (a, m')))
    (hs : m'.threads.size = m.threads.size) : P.WP t (f a) Q G m' n := by
  unfold WP at h ⊢
  have e : (ConcM.liftMem x >>= f : ConcM Tgt β) n m = f a n m' := by
    show CoN.bind (CoN.leaf (ExceptT.run (x.run m))) _ = _
    rw [hr]; rfl
  rw [e] at h; rw [hs]; exact h

/-- **A `MemM` step that returns, as the whole run**: the post at its memory. -/
theorem WP.liftMem_inv {x : MemM α} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {n : Nat}
    {a : α} {m' : Mem} (h : P.WP t (ConcM.liftMem x) Q G m n)
    (hr : (x.run m).run = some (.ok (a, m'))) : Q a G m' n := by
  unfold WP at h
  have e : (ConcM.liftMem x : ConcM Tgt α) n m = CoN.leaf (some (.ok (a, m'))) := by
    show CoN.leaf (ExceptT.run (x.run m)) = _
    rw [hr]
  rw [e] at h; simp only [Proto.Safe] at h; exact h.2

/-- **The end of a run**: the post. -/
theorem WP.pure_inv {a : α} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {n : Nat}
    (h : P.WP t (pure a : ConcM Tgt α) Q G m n) : Q a G m n := by
  change P.Safe t Q m.threads.size G (CoN.leaf (some (.ok (a, m)))) at h
  simp only [Proto.Safe] at h; exact h.2

end Proto

/-- **A pick and the `MemM` step it chooses** (an atomic op: `cmpxchgAsC`, `atomicRmwAsC`, …),
as `ConcM` binds (`Proto.WP.pick_inv`, `Proto.WP.liftMem_bind_inv`). -/
theorem pickCall_eq {Tgt σ α : Type} {count : Mem → Nat} {x : Nat → MemM α} {s : σ} :
    ((do let c ← pickC count; callMC (x c)) : CM Tgt σ α).run s =
      (ConcM.sync (.pick count) >>= fun c => ConcM.liftMem (x c) >>= fun a => pure (a, s)) := by
  funext n m; cases n <;> rfl

end Conc
end Zig
