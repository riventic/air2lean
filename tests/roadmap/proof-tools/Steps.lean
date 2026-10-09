import ZigLean.Sep.Step

/-!
Regressions for the symbolic-execution tactics of `ZigLean.Sep.Step`: framed load/store
steps on `pts` and on indexed `arr` access, caller-supplied rules, pure/existential
introduction, array splitting and the closing entailment. Each successful tactic run is an
ordinary proof term checked by the kernel; the rejected attempts below show that a missing
points-to, a dropped frame, a wrong value or an unprovable bound is not accepted.
-/

open Zig Assn

-- Copy one cell to another. Both points-to atoms and the frame `R` are found in an
-- arbitrary order; the postcondition is checked up to AC and `emp`.
example (p q : Ptr) (x y : BitVec 32) (R : Assn) :
    Triple (R ∗ (pts q 4 y ∗ pts p 4 x))
      (do let v ← load (BitVec 32) 4 p; store 4 q v) (fun _ => pts p 4 x ∗ (pts q 4 x ∗ R)) := by
  sep_steps
  sep_ret

-- The same program as a total triple: the steps use the total load/store rules.
example (p q : Ptr) (x y : BitVec 32) (R : Assn) :
    TotalTriple (R ∗ (pts q 4 y ∗ pts p 4 x))
      (do let v ← load (BitVec 32) 4 p; store 4 q v) (fun _ => pts p 4 x ∗ (pts q 4 x ∗ R)) := by
  sep_steps
  sep_ret

-- A returned value becomes a pure postcondition atom, closed by `rfl`.
example (p : Ptr) (x : BitVec 32) :
    Triple (pts p 4 x) (load (BitVec 32) 4 p) (fun r => ⌜r = x⌝ ∗ pts p 4 x) := by
  sep_steps
  sep_ret

-- Indexed access into an array: the element is read through `arr`, the update is
-- reassembled into the whole array, and the bounds come from the context.
example (p : Ptr) (xs : List (BitVec 32)) (i j : BitVec 64) (R : Assn)
    (hi : i.toNat < xs.length) (hj : j.toNat < xs.length) :
    TotalTriple (arr p xs ∗ R)
      (do let v ← load (BitVec 32) 4 (p.elem 4 i); store 4 (p.elem 4 j) v)
      (fun _ => arr p (xs.set j.toNat xs[i.toNat]) ∗ R) := by
  sep_steps
  sep_ret

-- A bound that does not follow from the context by `omega` remains a visible goal.
example (p : Ptr) (xs : List (BitVec 32)) (i : BitVec 64) (hi : i.toNat ∈ List.range xs.length) :
    Triple (arr p xs) (load (BitVec 32) 4 (p.elem 4 i)) (fun _ => arr p xs) := by
  sep_steps
  · sep_ret
  · guard_target =ₛ i.toNat < xs.length
    exact List.mem_range.mp hi

-- Splitting at an index: the prefix is accessed, the suffix is framed unchanged.
example (p : Ptr) (x y z : BitVec 32) (w : BitVec 32) :
    Triple (arr p [x, y, z]) (store 4 (p.elem 4 1) w)
      (fun _ => arr p [x, w] ∗ arr (p.add 8) [z]) := by
  sep_split p 2
  sep_steps
  sep_ret

-- A caller-supplied contract: its frame is inferred, its existential and pure facts are
-- introduced (an equation on a local is substituted), and the witness is supplied at the end.
example (p q : Ptr) (c : MemM Ptr) (x : BitVec 32) (R : Assn)
    (rule : Triple (pts p 4 x) c (fun r => Assn.ex fun y : BitVec 32 => ⌜r = q⌝ ∗ pts p 4 y)) :
    Triple (R ∗ pts p 4 x) (c >>= fun r => load (BitVec 32) 4 p >>= fun v => pure (r, v))
      (fun r => ⌜r.1 = q⌝ ∗ Assn.ex fun y : BitVec 32 => ⌜r.2 = y⌝ ∗ (pts p 4 y ∗ R)) := by
  sep_step using rule
  sep_steps
  sep_ret y

-- A rule whose precondition is a compound (left-nested, `emp`-padded) assertion is used as
-- stated; only its atoms are matched against the goal.
example (p q : Ptr) (c : MemM Unit) (x y : BitVec 32) (R : Assn)
    (rule : Triple ((pts p 4 x ∗ emp) ∗ pts q 4 y) c (fun _ => pts p 4 y ∗ pts q 4 x)) :
    Triple (pts q 4 y ∗ (R ∗ pts p 4 x)) c (fun _ => R ∗ (pts q 4 x ∗ pts p 4 y)) := by
  sep_step using rule
  sep_ret

-- Two equal pure atoms in the postcondition are both discharged.
example (p : Ptr) (x : BitVec 32) :
    Triple (pts p 4 x) (pure x) (fun r => ⌜r = x⌝ ∗ (⌜r = x⌝ ∗ pts p 4 x)) := by
  sep_ret

-- `sep_intro` names facts and witnesses in order.
example (p : Ptr) (b : Bool) :
    Triple (Assn.ex fun x : BitVec 32 => ⌜b = true⌝ ∗ pts p 4 x) (load (BitVec 32) 4 p)
      (fun r => ⌜b = true⌝ ∗ Assn.ex fun x => ⌜r = x⌝ ∗ pts p 4 x) := by
  sep_intro x hb
  sep_steps
  sep_ret x

-- `sep_unfold` normalizes a generated-style `MM` body: `StateT.run` is pushed through
-- `get`/`modify`/`callM`, and branch conditions are decided by the supplied fact.
example (p : Ptr) (x : BitVec 32) (n : BitVec 64) (hn : n.toNat < 4) :
    Triple (pts p 4 x)
      ((do
        let k ← get
        if Zig.lt false k (4 : BitVec 64) then
          let v ← callM (load (BitVec 32) 4 p)
          modify fun _ => k + 1
          pure v
        else throw .outOfBounds : MM (BitVec 64) (BitVec 32)).run n)
      (fun r => ⌜r = (x, n + 1)⌝ ∗ pts p 4 x) := by
  sep_unfold [hn]
  sep_steps
  sep_ret

/-! ## Rejected attempts -/

-- The binders below are used only inside the rejected `fail_if_success` blocks.
set_option linter.unusedVariables false

-- No points-to for the loaded address: the step fails instead of inventing ownership.
example (p q : Ptr) (x : BitVec 32) : True := by
  fail_if_success
    have : Triple (pts q 4 x) (load (BitVec 32) 4 p) (fun _ => pts q 4 x) := by
      sep_step
  trivial

-- A dropped frame atom is not an AC rearrangement of the precondition.
example (p : Ptr) (x : BitVec 32) (R : Assn) : True := by
  fail_if_success
    have : Triple (pts p 4 x ∗ R) (load (BitVec 32) 4 p) (fun r => ⌜r = x⌝ ∗ pts p 4 x) := by
      sep_steps
      sep_ret
  trivial

-- A store never promises the old value.
example (p : Ptr) (x w : BitVec 32) (hne : x ≠ w) : True := by
  fail_if_success
    have : Triple (pts p 4 x) (store 4 p w) (fun _ => pts p 4 x) := by
      sep_steps
      sep_ret
  trivial

-- An array update keeps the unchanged elements and nothing else: a wrong neighbor fails.
example (p : Ptr) (x y z w : BitVec 32) : True := by
  fail_if_success
    have : Triple (arr p [x, y, z]) (store 4 (p.elem 4 1) w) (fun _ => arr p [w, w, z]) := by
      sep_steps
      sep_ret
  trivial

-- A rule about a different command is rejected.
example (p q : Ptr) (x : BitVec 32) : True := by
  fail_if_success
    have : Triple (pts p 4 x) (load (BitVec 32) 4 p) (fun r => ⌜r = x⌝ ∗ pts p 4 x) := by
      sep_step using (Triple.load (p := q) (a := 4) (v := x) (by decide))
      sep_ret
  trivial

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
theorem steps_axioms (p : Ptr) (xs : List (BitVec 32)) (i : BitVec 64) (w : BitVec 32)
    (hi : i.toNat < xs.length) :
    TotalTriple (arr p xs) (store 4 (p.elem 4 i) w) (fun _ => arr p (xs.set i.toNat w)) := by
  sep_steps
  sep_ret

/-- info: 'steps_axioms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms steps_axioms
