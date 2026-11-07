import ZigLean.Sep.Full.AutoAll

/-!
# List walks from their invariants (ledger #list-walk-step)

A linked list walked by a loop body in the shape the translator emits (`while (cur) |n| …` over
`?*Node`: a test `cur.isSome`, the payload, the node's `next` at offset 0 and its item at 8),
with the invariant registered by `@[fsym_inv]` over a **ghost measure** (`B.inv … s n`, the
nodes left; the loop rule is `loop_ghost_ex`). `fsym` proves the functions with no step or loop
lemma:

* at the cursor's test it splits the ghost list of the nodes left (`[]`: the cursor is `null`;
  `z :: zs`: the list unfolds to the node at the cursor and the rest), because each case decides
  the test (`ghostSplit?`);
* at a repetition it folds the node into the invariant's list (`lseg (some p) none ?ys` tried as
  `[]` and as `?z :: ?ys'`: a constructor fold of the planner), and at the entry the empty prefix
  (`?ys := []`);
* a node joins a segment at its end by the caller's update `lseg_snoc_upd`.

A wrong invariant is rejected by the walk of its step.
-/

namespace SepAuto.ListWalk
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- A node at `p`: `next` at offset 0, the item at 8. -/
def node (p : Ptr) (v : BitVec 32) (q : Option Ptr) : FAssn :=
  up (pts p 8 q) ⋆ up (pts (p.add 8) 4 v)

/-- The segment from `hd` to `tl` holding `ys`. -/
def lseg : Option Ptr → Option Ptr → List (BitVec 32) → FAssn
  | hd, tl, [] => ⟪hd = tl⟫
  | hd, tl, v :: vs => FAssn.ex fun p => FAssn.ex fun q =>
      ⟪hd = some p⟫ ⋆ (node p v q ⋆ lseg q tl vs)

theorem lseg_snoc {q : Option Ptr} {p : Ptr} {v : BitVec 32} :
    ∀ {hd : Option Ptr} {ys : List (BitVec 32)} {r : Res},
      (lseg hd (some p) ys ⋆ node p v q) r → lseg hd q (ys ++ [v]) r
  | _, [], _, h => by
    obtain ⟨rfl, hn⟩ := sep_lift.mp h
    exact ⟨p, q, sep_lift.mpr ⟨rfl, sep_comm (sep_lift.mpr ⟨rfl, hn⟩)⟩⟩
  | _, y :: ys, _, h => by
    obtain ⟨p', h⟩ := sep_ex.mp h
    obtain ⟨q', h⟩ := sep_ex.mp h
    obtain ⟨hp, h⟩ := sep_lift.mp (sep_assoc h)
    exact ⟨p', q', sep_lift.mpr ⟨hp, sep_mono_right (fun _ h => lseg_snoc h) (sep_assoc h)⟩⟩

theorem lseg_snoc_upd {hd q : Option Ptr} {p : Ptr} {v : BitVec 32} {ys : List (BitVec 32)} :
    EUpd (lseg hd (some p) ys ⋆ node p v q) (lseg hd q (ys ++ [v])) :=
  EUpd.of_imp fun _ h => lseg_snoc h

structure RevLocals where
  prev : Option Ptr
  cur : Option Ptr
  deriving Inhabited

inductive Exit where
  | ret
  | brk
  | done
  | rep

def again : Exit → Bool
  | .rep => true
  | _ => false

/-- `while (cur) |n| { cur = n.next; n.next = prev; prev = n; }` -/
def rev.loop : MM RevLocals Exit := do
  match ← ((do
    let c ← pure ((← get).cur)
    if c.isSome then (do
      let n ← Zig.optPayload c
      let nx ← Zig.load (Option Ptr) 8 n
      modify (fun s => { s with cur := nx })
      let pr ← pure ((← get).prev)
      Zig.store (α := Option Ptr) 8 n pr
      modify (fun s => { s with prev := some n })
      pure .brk)
    else (do
      pure .done)) : MM RevLocals Exit) with
  | .brk => pure .rep
  | e => pure e

/-- `prev` holds the first items reversed, `cur` the other `n`. -/
@[fsym_inv] def rev.loop.inv (xs : List (BitVec 32)) (s : RevLocals) (n : Nat) : FAssn :=
  FAssn.ex fun ys => FAssn.ex fun zs =>
    ⟪xs = ys.reverse ++ zs ∧ zs.length = n⟫ ⋆ (lseg s.prev none ys ⋆ lseg s.cur none zs)

@[fsym_inv] def rev.loop.post (xs : List (BitVec 32)) (r : Exit × RevLocals) : FAssn :=
  ⟪r.1 = .done⟫ ⋆ lseg r.2.prev none xs.reverse

def rev (hd : Option Ptr) : MemM (Option Ptr) := do
  let e ← ((do
    modify (fun s => { s with prev := none })
    modify (fun s => { s with cur := hd })
    match ← ((do Zig.loop rev.loop again) : MM RevLocals Exit) with
    | .done => pure .ret
    | e => pure e) : MM RevLocals Exit).run (default : RevLocals)
  match e with
  | (.ret, s) => pure s.prev
  | _ => throw .panic

/-- **`rev` by its loop's registered invariant**: the cursor's test splits the ghost list, the
repetition folds the node into the list at `prev`, the entry the empty prefix. -/
theorem rev_total (hd : Option Ptr) (xs : List (BitVec 32)) :
    FTotalTriple (lseg hd none xs) (rev hd) (fun r => lseg r none xs.reverse) := by
  unfold rev
  fsym

/-- The same loop in the partial logic (`FTriple.loop` with `∃ n, rev.loop.inv xs s n`). -/
theorem rev_partial (hd : Option Ptr) (xs : List (BitVec 32)) :
    FTriple (lseg hd none xs) (rev hd) (fun r => lseg r none xs.reverse) := by
  unfold rev
  fsym

structure LenLocals where
  c : BitVec 64
  p : Option Ptr
  deriving Inhabited

/-- `while (p) |n| { c += 1; p = n.next; }` -/
def len.loop : MM LenLocals Exit := do
  match ← ((do
    let p ← pure ((← get).p)
    if p.isSome then (do
      let n ← Zig.optPayload p
      let c ← Zig.add false ((← get).c) (1 : BitVec 64)
      modify (fun s => { s with c := c })
      let nx ← Zig.load (Option Ptr) 8 n
      modify (fun s => { s with p := nx })
      pure .brk)
    else (do
      pure .done)) : MM LenLocals Exit) with
  | .brk => pure .rep
  | e => pure e

/-- The visited nodes are a segment from `hd` to the cursor, `c` counts them. -/
@[fsym_inv] def len.loop.inv (hd : Option Ptr) (xs : List (BitVec 32)) (s : LenLocals) (n : Nat) :
    FAssn :=
  FAssn.ex fun ys => FAssn.ex fun zs =>
    ⟪xs = ys ++ zs ∧ zs.length = n ∧ s.c.toNat = ys.length⟫ ⋆ (lseg hd s.p ys ⋆ lseg s.p none zs)

@[fsym_inv] def len.loop.post (hd : Option Ptr) (xs : List (BitVec 32)) (r : Exit × LenLocals) :
    FAssn :=
  ⟪r.1 = .done ∧ r.2.c.toNat = xs.length⟫ ⋆ lseg hd none xs

def len (hd : Option Ptr) : MemM (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with c := 0 })
    modify (fun s => { s with p := hd })
    match ← ((do Zig.loop len.loop again) : MM LenLocals Exit) with
    | .done => pure .ret
    | e => pure e) : MM LenLocals Exit).run (default : LenLocals)
  match e with
  | (.ret, s) => pure s.c
  | _ => throw .panic

/-- **A walk that keeps the visited prefix**: the node joins the segment by the caller's update
`lseg_snoc_upd`. -/
theorem len_total (hd : Option Ptr) (xs : List (BitVec 32)) (hfit : xs.length < 2 ^ 64) :
    FTotalTriple (lseg hd none xs) (len hd)
      (fun r => ⟪r.toNat = xs.length⟫ ⋆ lseg hd none xs) := by
  unfold len
  fsym [lseg_snoc_upd]

/-- The planner's constructor fold on its own: the node and the list after it are the list from
the node, an unknown list (`?l := z :: ys`). -/
example (ys : List (BitVec 32)) (z : BitVec 32) (pr : Option Ptr) (p : Ptr) :
    EUpd (up (pts p 8 pr) ⋆ up (pts (p.add 8) 4 z) ⋆ lseg pr none ys)
      (FAssn.ex fun l => ⟪l = z :: ys⟫ ⋆ lseg (some p) none l) := by
  fsym_entail

section
open Lean Meta Elab Tactic Zig.Full.Auto.Report
-- The claims below are quoted inside `run_tac`: unhygienic, so they name the example's variables.
set_option hygiene false

set_option linter.unusedVariables false in
/-- No node at `p`: no constructor of the unknown list closes the update (`[]` needs
`some p = none`, `?z :: ?l'` a node at `p`). The goal is inspected, never admitted. -/
example (ys : List (BitVec 32)) (pr : Option Ptr) (p : Ptr) : True := by
  run_tac withMainContext do
    let ty ← elabTerm (← `(EUpd (lseg pr none ys) (FAssn.ex fun l => lseg (some p) none l))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let gs ← evalTacticAt (← `(tactic| fsym_entail)) g.mvarId!
    if gs.isEmpty then throwError "the update without a node was closed"
  trivial

/-- The same body under another name … -/
def bad.loop : MM RevLocals Exit := rev.loop

/-- … whose invariant is wrong: `prev` holding the visited items in their order. It holds at the
entry, but the step does not keep it. -/
@[fsym_inv] def bad.loop.inv (xs : List (BitVec 32)) (s : RevLocals) (n : Nat) : FAssn :=
  FAssn.ex fun ys => FAssn.ex fun zs =>
    ⟪xs = ys ++ zs ∧ zs.length = n⟫ ⋆ (lseg s.prev none ys ⋆ lseg s.cur none zs)

@[fsym_inv] def bad.loop.post (xs : List (BitVec 32)) (r : Exit × RevLocals) : FAssn :=
  ⟪r.1 = .done⟫ ⋆ lseg r.2.prev none xs

set_option linter.unusedVariables false in
/-- **A wrong invariant is rejected**: it holds at the entry, and every residual is in the walk
of its step, whose postcondition is the invariant at the next iteration (the claim is false for a
list of two different items). -/
example (hd : Option Ptr) (xs : List (BitVec 32)) : True := by
  run_tac withMainContext do
    let ty ← elabTerm (← `(FTotalTriple (lseg hd none xs)
      ((Zig.loop bad.loop again).run { prev := none, cur := hd })
      (fun r => lseg r.2.prev none xs))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (gs, report) ← runReport g.mvarId!
    let inStep (r : Residual) := (r.origin.source.text.splitOn "bad.loop.inv").length > 1
    unless !gs.isEmpty && report.residuals.all inStep do
      throwError "the wrong invariant was not rejected by the walk of its step: {line report}"
  trivial

end

end SepAuto.ListWalk
