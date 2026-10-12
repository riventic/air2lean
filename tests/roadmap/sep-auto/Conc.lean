import ZigLean.Sep.Full.Auto

/-!
# `fsym` on concurrent programs (`CTriple`, `docs/proof-automation.md`)

Programs written by hand in the shape the translator generates for a concurrent function (the
body monad `CM`, run from its locals): an atomic load and a `cmpxchg` (oracle picks, the
sequential atomic rules), an indirect call through a table of candidates (folded into
`callIndirect`, executed by a `CTriple` rule for the table call or by the arm the facts select;
for an open function type the last arm is the environment's call, `Table.callOr`), and a loop read with its invariant (`CTriple.loop`).
-/

namespace SepAuto.Conc

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

variable {Tgt : Type}

/-- Publish `q` in the hint word at `w` if it holds `none`: load, then `cmpxchg`. -/
def publish (w q : Ptr) : ConcM Tgt (Option Ptr) :=
  (do
    let v ← atomicLoadUnorderedEncC (Option Ptr) 8 w
    if v.isNone then
      let _ ← cmpxchgPtrC (α := Option Ptr) .relaxed .relaxed 8 w v (some q)
      pure (some q)
    else pure v : CM Tgt Unit (Option Ptr)).run' ()

theorem publish_spec (w q : Ptr) :
    CTriple (Tgt := Tgt) (aptsE w (none : Option Ptr)) (publish w q)
      (fun r => ⟪r = some q⟫ ⋆ aptsE w (some q)) := by
  unfold publish
  fsym

/-- Two candidates of one function type. -/
def inc (x : BitVec 64) : ConcM Tgt (BitVec 64) := pure (x + 1)
def dbl (x : BitVec 64) : ConcM Tgt (BitVec 64) := pure (x + x)

/-- The program's table for that type. -/
def tbl : Table Tgt (BitVec 64) (BitVec 64) := [(⟨some 1, 0⟩, inc), (⟨some 2, 0⟩, dbl)]

/-- A call through the function pointer `f`, as generated: one arm per candidate. -/
def callVia (f : Ptr) (x : BitVec 64) : ConcM Tgt (BitVec 64) :=
  (do
    let r ← (if f == (⟨some 1, 0⟩ : Ptr) then callC (inc x)
      else if f == (⟨some 2, 0⟩ : Ptr) then callC (dbl x) else throw .illegal)
    pure (r + 0) : CM Tgt Unit (BitVec 64)).run' ()

/-- By a specification of the table call (any pointer the table serves): `CTriple.tableCall`'s
reading, as a `CTriple` rule. -/
theorem callVia_rule (f : Ptr) (x : BitVec 64) (R : FAssn)
    (h : ∀ y, CTriple (Tgt := Tgt) R (tbl.call f y) (fun _ => R)) :
    CTriple (Tgt := Tgt) R (callVia f x) (fun _ => R) := by
  unfold callVia
  fsym [h]

/-- By the arm that the facts select. -/
theorem callVia_arm (x : BitVec 64) (R : FAssn) :
    CTriple (Tgt := Tgt) R (callVia ⟨some 2, 0⟩ x) (fun r => ⟪r = x + x⟫ ⋆ R) := by
  unfold callVia dbl
  fsym

/-- A call through `f` of an open function type (`docs/interfaces.md`), as generated: the
program's arms, then the environment `e` for any other pointer. -/
def callOpen (e : EnvFn Tgt (BitVec 64) (BitVec 64)) (f : Ptr) (x : BitVec 64) :
    ConcM Tgt (BitVec 64) :=
  (do
    let r ← (if f == (⟨some 1, 0⟩ : Ptr) then callC (inc x)
      else if f == (⟨some 2, 0⟩ : Ptr) then callC (dbl x) else callC (extCall (e f x)))
    pure (r + 0) : CM Tgt Unit (BitVec 64)).run' ()

/-- By a specification of the call with the environment (`Table.callOr`), whichever arm runs. -/
theorem callOpen_rule (e : EnvFn Tgt (BitVec 64) (BitVec 64)) (f : Ptr) (x : BitVec 64)
    (R : FAssn) (h : ∀ y, CTriple (Tgt := Tgt) R (tbl.callOr e f y) (fun _ => R)) :
    CTriple (Tgt := Tgt) R (callOpen e f x) (fun _ => R) := by
  unfold callOpen
  fsym [h]

/-- A pointer of the program runs its arm, whatever the environment. -/
theorem callOpen_arm (e : EnvFn Tgt (BitVec 64) (BitVec 64)) (x : BitVec 64) (R : FAssn) :
    CTriple (Tgt := Tgt) R (callOpen e ⟨some 2, 0⟩ x) (fun r => ⟪r = x + x⟫ ⋆ R) := by
  unfold callOpen dbl
  fsym

/-- Any other pointer runs the environment, by its contract. -/
theorem callOpen_env (e : EnvFn Tgt (BitVec 64) (BitVec 64)) (f : Ptr) (x : BitVec 64)
    (R : FAssn) (h1 : f ≠ ⟨some 1, 0⟩) (h2 : f ≠ ⟨some 2, 0⟩)
    (he : ∀ y, CTriple (Tgt := Tgt) R (extCall (e f y)) (fun _ => R)) :
    CTriple (Tgt := Tgt) R (callOpen e f x) (fun _ => R) := by
  unfold callOpen
  fsym [he]

/-- Count a word down to zero: `while (n != 0) n -= 1`, as a generated loop over its locals. -/
def body (_ : Unit) : CM Tgt (BitVec 64) Bool := do
  let n ← get
  if n == 0 then pure false
  else
    let n' ← callRC (Zig.sub false n 1)
    set n'
    pure true

/-- The loop body keeps the invariant `R` (the loop rule `CTriple.loop`). -/
theorem body_spec (R : FAssn) :
    ∀ s : BitVec 64, CTriple (Tgt := Tgt) R ((body ()).run s)
      (fun r => if (fun b : Bool => b) r.1 then R else R) := by
  unfold body
  fsym

/-- The loop, by its invariant. -/
theorem loop_spec (R : FAssn) (s : BitVec 64) :
    CTriple (Tgt := Tgt) R ((Zig.loop (body ()) (fun b : Bool => b)).run s) (fun _ => R) :=
  CTriple.loop (fun _ => R) (fun _ => R) (body_spec R) s

end SepAuto.Conc
