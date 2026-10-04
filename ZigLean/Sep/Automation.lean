import ZigLean.Sep.Triple
import Lean

/-!
# Proof-producing separation normalization and framing

`sep_normalize` uses associativity, commutativity, and the empty heap unit to normalize
assertions, including assertions beneath a heap application. `sep_frame rule` infers the
unused conjuncts of a partial triple's precondition, applies the existing frame rule, and
proves the pre/post rearrangements. Every successful tactic emits ordinary kernel-checked
proof terms. Atoms are opaque: this does not unfold ownership, infer arithmetic facts, or
split arrays. Repeated atoms are counted separately.

Normalization uses Lean's standard simp ordering. It can leave equivalent expressions
unmatched when atom heads are definitionally equal wrappers or differ only in implicit
typeclass instances; such goals need an explicit rewrite or the separation equalities.
-/

namespace Zig

theorem sep_comm_eq (P Q : Assn) : (P ∗ Q) = (Q ∗ P) := by
  funext h
  exact propext ⟨sep_comm, sep_comm⟩

theorem sep_assoc_eq (P Q R : Assn) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  funext h
  exact propext ⟨sep_assoc, sep_assoc'⟩

theorem sep_left_comm_eq (P Q R : Assn) : (P ∗ (Q ∗ R)) = (Q ∗ (P ∗ R)) := by
  rw [← sep_assoc_eq, sep_comm_eq P Q, sep_assoc_eq]

theorem sep_emp_eq (P : Assn) : (P ∗ Assn.emp) = P := by
  funext h
  exact propext sep_emp

theorem emp_sep_eq (P : Assn) : (Assn.emp ∗ P) = P := by
  rw [sep_comm_eq, sep_emp_eq]

end Zig

open Lean.Parser.Tactic

macro "sep_normalize" loc:(location)? : tactic =>
  `(tactic| simp only [Zig.sep_assoc_eq, Zig.sep_comm_eq, Zig.sep_left_comm_eq,
    Zig.sep_emp_eq, Zig.emp_sep_eq] $[$loc]?)

namespace Zig.SepAutomation

open Lean Meta Elab Tactic

/-- Only explicit separating conjunctions and units are inspected. -/
private partial def atoms (e : Expr) : Array Expr :=
  collect [e] #[]
where
  collect (pending : List Expr) (result : Array Expr) : Array Expr :=
    match pending with
    | [] => result
    | head :: tail =>
      let head := head.consumeMData
      if head.isAppOfArity ``Zig.Assn.sep 2 then
        let args := head.getAppArgs
        collect (args[0]! :: args[1]! :: tail) result
      else if head.isConstOf ``Zig.Assn.emp then collect tail result
      else collect tail (result.push head)

private def inferFrame (available needed : Expr) : MetaM Expr := do
  let all := atoms available
  let mut consumed := Array.replicate all.size false
  let mut cursor := 0
  for atom in atoms needed do
    let mut found := false
    for i in [cursor:all.size] do
      unless consumed[i]! do
        if ← isDefEq atom all[i]! then
          consumed := consumed.set! i true
          found := true
          while cursor < all.size do
            if consumed[cursor]! then cursor := cursor + 1
            else break
          break
    unless found do
      throwError "sep_frame: precondition does not contain required atom {atom}"
  let mut rest := #[]
  for i in [cursor:all.size] do
    unless consumed[i]! do
      rest := rest.push all[i]!
  return rest.foldr (fun p q => mkApp2 (mkConst ``Zig.Assn.sep) p q)
    (mkConst ``Zig.Assn.emp)

/-- Infer the frame from the preconditions; check both consequences with normalization. -/
elab "sep_frame " rule:term : tactic => withMainContext do
  let goalType ← instantiateMVars (← getMainTarget)
  unless goalType.isAppOfArity ``Zig.Triple 4 do
    throwError "sep_frame: expected a Zig.Triple goal"
  let proof ← Term.elabTerm rule none
  let ruleType ← instantiateMVars (← inferType proof)
  unless ruleType.isAppOfArity ``Zig.Triple 4 do
    throwError "sep_frame: supplied rule must prove a Zig.Triple"
  unless ← isDefEq ruleType.getAppArgs[2]! goalType.getAppArgs[2]! do
    throwError "sep_frame: supplied rule proves a different command"
  let frame ← inferFrame goalType.getAppArgs[1]! ruleType.getAppArgs[1]!
  let frameSyntax ← Term.exprToSyntax (← instantiateMVars frame)
  let proofSyntax ← Term.exprToSyntax (← instantiateMVars proof)
  evalTactic (← `(tactic| (
    refine Zig.Triple.conseq (Zig.Triple.frame (R := $frameSyntax) $proofSyntax) ?_ ?_
    · intro h hp
      sep_normalize at hp ⊢
      exact hp
    · intro v h hq
      sep_normalize at hq ⊢
      exact hq)))

end Zig.SepAutomation
