import ZigLean.Sep.Automation

open Zig Assn

-- AC normalization works on assertion functions and applied assertions.
example (P Q R S : Assn) : (((P ∗ emp) ∗ Q) ∗ (R ∗ S)) = (S ∗ (Q ∗ (P ∗ R))) := by
  sep_normalize

example (P Q R : Assn) (h : Heap) (hp : ((P ∗ Q) ∗ R) h) : (R ∗ (Q ∗ P)) h := by
  sep_normalize at hp ⊢
  exact hp

-- The frame is inferred, including its repeated atoms and empty units.
example (P Q R : Assn) (c : MemM Unit) (rule : Triple P c (fun _ => Q)) :
    Triple ((R ∗ emp) ∗ (P ∗ R)) c (fun _ => R ∗ (R ∗ Q)) := by
  sep_frame rule

example (P Q : Assn) (c : MemM Unit) (rule : Triple emp c (fun _ => emp)) :
    Triple (P ∗ Q) c (fun _ => Q ∗ P) := by
  sep_frame rule

example (P : Assn) (c : MemM Unit) (rule : Triple P c (fun _ => P)) :
    Triple P c (fun _ => P) := by
  sep_frame rule

-- Insufficient multiplicity is rejected: one resource cannot be counted twice.
example (P : Assn) (c : MemM Unit) (rule : Triple (P ∗ P) c (fun _ => emp)) : True := by
  fail_if_success
    have : Triple P c (fun _ => emp) := by sep_frame rule
  trivial

-- A frame cannot silently disappear from the postcondition.
example (P R : Assn) (c : MemM Unit) (rule : Triple P c (fun _ => P)) : True := by
  fail_if_success
    have : Triple (P ∗ R) c (fun _ => P) := by sep_frame rule
  trivial

-- Neither arbitrary command changes nor non-triple inputs are accepted.
example (P : Assn) (c d : MemM Unit) (rule : Triple P c (fun _ => P)) : True := by
  fail_if_success
    have : Triple P d (fun _ => P) := by sep_frame rule
  fail_if_success sep_frame rule
  trivial

example (P : Assn) (c : MemM Unit) : True := by
  fail_if_success
    have : Triple P c (fun _ => P) := by sep_frame (True.intro)
  trivial

-- Embedded expressions retain a non-default encoding instance in an opaque frame.
example (T : Type) [Enc T] (e : Enc T) (p : Ptr) (v : T) (P : Assn)
    (c : MemM Unit) (rule : Triple P c (fun _ => P)) :
    Triple (P ∗ @pts T e p 4 v) c (fun _ => P ∗ @pts T e p 4 v) := by
  sep_frame rule

-- Distinct encoding instances cannot be silently substituted during matching.
example (T : Type) (e₁ e₂ : Enc T) (p : Ptr) (v : T) (c : MemM Unit)
    (rule : Triple (@pts T e₁ p 4 v) c (fun _ => @pts T e₁ p 4 v)) : True := by
  fail_if_success
    have : Triple (@pts T e₂ p 4 v) c (fun _ => @pts T e₂ p 4 v) := by
      sep_frame rule
  trivial

-- Lean's simp order ignores instance arguments; this exotic permutation is unsupported.
-- Its equivalence remains provable directly with sep_comm_eq.
example (T : Type) (e₁ e₂ : Enc T) (p : Ptr) (v : T) : True := by
  fail_if_success
    have : (@pts T e₁ p 4 v ∗ @pts T e₂ p 4 v) =
        (@pts T e₂ p 4 v ∗ @pts T e₁ p 4 v) := by
      sep_normalize
  have : (@pts T e₁ p 4 v ∗ @pts T e₂ p 4 v) =
      (@pts T e₂ p 4 v ∗ @pts T e₁ p 4 v) := sep_comm_eq _ _
  trivial
