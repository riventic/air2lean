import ZigLean.Sep.Witness
import AuditClaims.Gen

/-!
Architecture-audit counterexamples (docs/architecture-audit/claims.md). Every theorem here is
kernel-checked with standard axioms only, mentions the generated root in its conclusion, and is
classified by `scripts/claims.py` at the strength noted. None of them is evidence that
`AuditClaims.root` is correct: `root 255` panics.
-/

open Zig Assn

namespace AuditClaims

/-- C1: the claim is a hypothesis. Hypotheses are stripped, so this is `total_correctness`. -/
theorem hyp_is_claim (x : BitVec 8) (h : root x = pure (x + 1)) : root x = pure (x + 1) := h

/-- C2: unsatisfiable precondition (`x.toNat > 300` for an 8-bit `x`). `total_correctness`. -/
theorem unsat_pre (x : BitVec 8) (hx : x.toNat > 300) : root x = pure (x + 1) := by
  have := x.isLt; omega

/-- C3: one ground input. `total_correctness`; the manifest `domain` string is not checked. -/
theorem ground_instance : root 3 = pure 4 := rfl

/-- C4: `TotalTriple` with precondition `False`. `total_correctness`. -/
theorem total_false_pre (Q : Unit → Assn) : TotalTriple (fun _ => False) spin Q := by
  intro m hP hF hd hm hp; exact hp.elim

/-- C5: the root occurs only inside the postcondition of a triple about `pure ()`.
`conclusion_dependencies` contains `AuditClaims.root`, so coverage binds this as `direct`. -/
theorem root_in_post :
    TotalTriple emp (pure () : MemM Unit) (fun _ => ⌜root 255 = root 255⌝) :=
  (TotalTriple.ret (Q := fun _ => ⌜root 255 = root 255⌝) ()).conseq
    (fun _ h => ⟨rfl, h⟩) (fun _ _ h => h)

/-- C6: an exact-success equation whose left side is not the root at all; the root is only an
ignored argument on the right. `total_correctness`, `direct`. -/
theorem root_ignored : (pure 5 : Result Nat) = pure (Function.const _ 5 (root 255)) := rfl

/-- C7: partial correctness of a program that never returns, with postcondition `False`.
`partial_correctness`: coverage reported `functionally_verified_partial`. Its precondition is
satisfiable (witness below), so only the missing liveness witness (S6) caps it. -/
theorem spin_partial : Triple emp spin (fun _ _ => False) := by
  intro m hP hF hd hm hp hs; trivial

/-- F4: a hand-written model in a contract (here a clock oracle). Nothing maps it to a premise. -/
def clockModel : Nat := 3

/-- F4: the claim rests on a hypothesis about `clockModel`, which no premise or root assumption
accounts for. Kernel-checked, `safety` (an exact success over one fixed input). -/
theorem oracle_hyp (_h : clockModel = 3) : root 3 = pure 4 := rfl

/-- Equation shapes (`conclusion.lhs`, `conclusion.reflexive`): a reflexive equation states
nothing about the root; a relational one relates two different applications of it. Neither is
an exact-success claim. -/
theorem root_refl (x : BitVec 8) : root x = root x := rfl

theorem root_rel (x : BitVec 8) : root (x + 0) = root x := by simp

nonvacuity_witness spin_partial :=
  ⟨{}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, rfl, Mem.seq_default, trivial⟩

end AuditClaims
