import ZigLean.Sep.Full.Auto

/-!
# `fsym` on the scenarios of the retired step tactics (`docs/proof-automation.md`)

The scenarios of the legacy `sep_steps`/`sep_ret`/`sep_frame` regressions, in the full-state
logic: framed loads and stores with the frame found in any order, a returned value as a fact of
the postcondition, a caller-supplied rule (`fsym [rule]`) with an existential and a fact, a
rule whose precondition is a compound assertion, existentials and facts of the precondition, a
generated-style `MM` body with `get`/`modify`/`callM` and a branch decided by a fact, an item
store through `p.elem` with the neighbours framed, and a side condition left to the caller. The
rejected attempts show that a missing points-to, a dropped frame, a wrong value, a changed
neighbour or a rule about another command is not accepted. The programs are written by hand in
the shape the translator generates. (Whole-array ownership `arr p xs` with a symbolic index
waits for the library's array rules, `Full/Arr`.)
-/

namespace SepAuto.Steps

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- Copy one cell to another. -/
def copy (p q : Ptr) : MemM Unit := do
  let v ← Zig.load (BitVec 32) 4 p
  Zig.store 4 q v

/-- Both points-to atoms and the frame `R` are found in any order. -/
theorem copy_total (p q : Ptr) (x y : BitVec 32) (R : FAssn) :
    FTotalTriple (R ⋆ (up (pts q 4 y) ⋆ up (pts p 4 x))) (copy p q)
      (fun _ => up (pts p 4 x) ⋆ (up (pts q 4 x) ⋆ R)) := by
  unfold copy
  fsym

/-- The same program, partial correctness. -/
theorem copy_partial (p q : Ptr) (x y : BitVec 32) (R : FAssn) :
    FTriple (R ⋆ (up (pts q 4 y) ⋆ up (pts p 4 x))) (copy p q)
      (fun _ => up (pts p 4 x) ⋆ (up (pts q 4 x) ⋆ R)) := by
  unfold copy
  fsym

/-- A returned value becomes a fact of the postcondition. -/
theorem load_ret (p : Ptr) (x : BitVec 32) :
    FTotalTriple (up (pts p 4 x)) (Zig.load (BitVec 32) 4 p) (fun r => ⟪r = x⟫ ⋆ up (pts p 4 x)) := by
  fsym

/-- A caller-supplied rule: its frame is inferred, its existential and fact are introduced, and
the witness is found at the return. -/
theorem rule_call (p q : Ptr) (c : MemM Ptr) (x : BitVec 32) (R : FAssn)
    (rule : FTotalTriple (up (pts p 4 x)) c
      (fun r => FAssn.ex fun y : BitVec 32 => ⟪r = q⟫ ⋆ up (pts p 4 y))) :
    FTotalTriple (R ⋆ up (pts p 4 x)) (c >>= fun r => Zig.load (BitVec 32) 4 p >>= fun v => pure (r, v))
      (fun r => ⟪r.1 = q⟫ ⋆ FAssn.ex fun y : BitVec 32 => ⟪r.2 = y⟫ ⋆ (up (pts p 4 y) ⋆ R)) := by
  fsym [rule]

/-- A rule whose precondition is a compound (nested, `emp`-padded) assertion is used as stated. -/
theorem rule_compound (p q : Ptr) (c : MemM Unit) (x y : BitVec 32) (R : FAssn)
    (rule : FTotalTriple ((up (pts p 4 x) ⋆ emp) ⋆ up (pts q 4 y)) c
      (fun _ => up (pts p 4 y) ⋆ up (pts q 4 x))) :
    FTotalTriple (up (pts q 4 y) ⋆ (R ⋆ up (pts p 4 x))) c
      (fun _ => R ⋆ (up (pts q 4 x) ⋆ up (pts p 4 y))) := by
  fsym [rule]

/-- Two equal facts in the postcondition are both discharged. -/
theorem two_facts (p : Ptr) (x : BitVec 32) :
    FTotalTriple (up (pts p 4 x)) (pure x : MemM (BitVec 32))
      (fun r => ⟪r = x⟫ ⋆ (⟪r = x⟫ ⋆ up (pts p 4 x))) := by
  fsym

/-- Existentials and facts of the precondition move into the context. -/
theorem pre_ex (p : Ptr) (b : Bool) :
    FTotalTriple (FAssn.ex fun x : BitVec 32 => ⟪b = true⟫ ⋆ up (pts p 4 x)) (Zig.load (BitVec 32) 4 p)
      (fun r => ⟪b = true⟫ ⋆ FAssn.ex fun x => ⟪r = x⟫ ⋆ up (pts p 4 x)) := by
  fsym

/-- A generated-style `MM` body: `get`, a branch decided by a fact, a call, `modify`. -/
def body (p : Ptr) : MM (BitVec 64) (BitVec 32) := do
  let k ← get
  if Zig.lt false k (4 : BitVec 64) then
    let v ← callM (Zig.load (BitVec 32) 4 p)
    modify fun _ => k + 1
    pure v
  else throw .outOfBounds

theorem body_run (p : Ptr) (x : BitVec 32) (n : BitVec 64) (hn : n.toNat < 4) :
    FTotalTriple (up (pts p 4 x)) ((body p).run n) (fun r => ⟪r = (x, n + 1)⟫ ⋆ up (pts p 4 x)) := by
  unfold body
  fsym

/-- An item store `p[1] = w` into three owned items: the item pointer `p.elem 4 1` is the item at
`p.add 4`, and the neighbours are framed unchanged. -/
theorem elem_store (p : Ptr) (x y z w : BitVec 32) :
    FTotalTriple (up (pts p 4 x) ⋆ up (pts (p.add 4) 4 y) ⋆ up (pts (p.add 8) 4 z))
      (Zig.store 4 (p.elem 4 1) w)
      (fun _ => up (pts p 4 x) ⋆ up (pts (p.add 4) 4 w) ⋆ up (pts (p.add 8) 4 z)) := by
  fsym

/-- Add `n` to the word at `ctx`, checked. -/
def bump (ctx : Ptr) (n : BitVec 64) : MemM (BitVec 64) := do
  let e ← Zig.load (BitVec 64) 8 ctx
  let e' ← StateT.lift (Zig.add false e n)
  Zig.store (α := BitVec 64) 8 ctx e'
  pure e'

/-- A side condition that the facts do not give stays a goal for the caller (here the overflow
check, from a hypothesis that the arithmetic solver does not read). -/
theorem bound_left (ctx : Ptr) (v n : BitVec 64) (h : v.toNat + n.toNat ∈ List.range (2 ^ 64)) :
    FTotalTriple (up (pts ctx 8 v)) (bump ctx n)
      (fun r => ⟪r.toNat = v.toNat + n.toNat⟫ ⋆ up (pts ctx 8 r)) := by
  unfold bump
  fsym
  exact List.mem_range.mp h

/-! ## Rejected attempts -/

set_option linter.unusedVariables false

/-- An item store keeps the other items: a changed neighbour is rejected. -/
example (p : Ptr) (x y z w : BitVec 32) : True := by
  fail_if_success
    have : FTotalTriple (up (pts p 4 x) ⋆ up (pts (p.add 4) 4 y) ⋆ up (pts (p.add 8) 4 z))
        (Zig.store 4 (p.elem 4 1) w)
        (fun _ => up (pts p 4 w) ⋆ up (pts (p.add 4) 4 w) ⋆ up (pts (p.add 8) 4 z)) := by
      fsym
  trivial

/-- No points-to for the loaded address: the walk fails instead of inventing ownership. -/
example (p q : Ptr) (x : BitVec 32) : True := by
  fail_if_success
    have : FTotalTriple (up (pts q 4 x)) (Zig.load (BitVec 32) 4 p) (fun _ => up (pts q 4 x)) := by
      fsym
  trivial

/-- A frame cannot be dropped from the postcondition. -/
example (p : Ptr) (x : BitVec 32) (R : FAssn) : True := by
  fail_if_success
    have : FTotalTriple (up (pts p 4 x) ⋆ R) (Zig.load (BitVec 32) 4 p)
        (fun r => ⟪r = x⟫ ⋆ up (pts p 4 x)) := by
      fsym
  trivial

/-- A store never promises the old value. -/
example (p : Ptr) (x w : BitVec 32) (hne : x ≠ w) : True := by
  fail_if_success
    have : FTotalTriple (up (pts p 4 x)) (Zig.store 4 p w) (fun _ => up (pts p 4 x)) := by
      fsym
  trivial

/-- A rule about another command is not used. -/
example (p q : Ptr) (x : BitVec 32) (c : MemM Unit) (rule : FTotalTriple (up (pts q 4 x)) c (fun _ => emp)) :
    True := by
  fail_if_success
    have : FTotalTriple (up (pts q 4 x)) (Zig.store 4 q x) (fun _ => emp) := by
      fsym [rule]
  trivial

end SepAuto.Steps
