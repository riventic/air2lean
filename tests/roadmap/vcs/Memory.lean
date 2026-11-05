import ZigLean.Sep.Full.AutoAll

/-!
Verification conditions on the full-state logic (`docs/vcs.md`): the goals that `fsym` leaves on
an `FTotalTriple`/`FTriple` goal are the obligations, and `fsym.report` gives each its origin (the
kind of the obligation). The programs are small functions written as the translator writes them.
-/

namespace VCMemory

open Zig Zig.Full FAssn

def loadStore (p : Ptr) : MemM Unit := do
  let x ← Zig.load (BitVec 32) 4 p
  Zig.store (α := BitVec 32) 4 p x

def incr (p : Ptr) : MemM Unit := do
  let x ← Zig.load (BitVec 32) 4 p
  let y ← Zig.add false x (1 : BitVec 32)
  Zig.store (α := BitVec 32) 4 p y

-- Ownership is not assumed: without the cell no rule executes the load, and the walk stops there.
/--
info: fsym-report {"residuals":[{"goal":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T emp (load (BitVec 32) 4 p >>= fun x => store 4 p x >>= pure) fun x => emp"},"index":0,"origin":{"condition":"program","judgment":"Zig.Full.FLogic.T","program":{"head":"Zig.load","text":"load (BitVec 32) 4 p"},"reason":"no_rule","rule":null,"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T emp (load (BitVec 32) 4 p >>= fun x => store 4 p x >>= pure) fun x => emp"}}}],"schemaVersion":1,"status":"stopped"}
---
error: unsolved goals
p : Ptr
⊢ FLogic.total.T emp (load (BitVec 32) 4 p >>= fun x => store 4 p x >>= pure) fun x => emp
-/
#guard_msgs in
example (p : Ptr) : FTotalTriple emp (loadStore p) (fun _ => emp) := by
  set_option fsym.report true in fsym

-- A fabricated postcondition cannot ignore the actual heap: the heap obligation is left.
/--
info: fsym-report {"residuals":[{"goal":{"head":"Zig.Full.EUpd","text":"EUpd (up (pts p 4 x)) (up (pts p 4 (x + 1)))"},"index":0,"origin":{"condition":"postcondition","judgment":"Zig.Full.FLogic.T","program":{"head":"Pure.pure","text":"pure v"},"reason":"postcondition_not_proved","rule":{"head":"Zig.Full.Auto.ret","text":"Auto.ret"},"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T (up (pts p 4 x)) (pure v) fun x_1 => up (pts p 4 (x + 1))"}}}],"schemaVersion":1,"status":"stopped"}
---
error: unsolved goals
p : Ptr
x : BitVec 32
v : Unit
right✝ : 0 ≤ p.off
w✝ : BlockId
h✝ : p.block = some w✝
⊢ EUpd (up (pts p 4 x)) (up (pts p 4 (x + 1)))
-/
#guard_msgs in
example (p : Ptr) (v : BitVec 32) :
    FTotalTriple (up (pts p 4 v)) (loadStore p) (fun _ => up (pts p 4 (v + 1))) := by
  set_option fsym.report true in fsym

-- Overflow stays a safety obligation (a premise of the step rule) even when the postcondition
-- is the true one.
/--
info: fsym-report {"residuals":[{"goal":{"head":"LT.lt","text":"x.toNat + (1#32).toNat < 2 ^ 32"},"index":0,"origin":{"condition":"rule_premise","judgment":"Zig.Full.FLogic.T","program":{"head":"StateT.lift","text":"StateT.lift (add false x 1#32)"},"reason":"side_condition_not_proved","rule":{"head":"Zig.Full.Auto.add_step","text":"@Auto.add_step"},"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T (up (pts p 4 x)) (StateT.lift (add false x 1#32) >>= fun x => store 4 p x >>= pure) fun x_1 =>\n  up (pts p 4 (x + 1))"}}}],"schemaVersion":1,"status":"stopped"}
---
error: unsolved goals
case h
p : Ptr
x : BitVec 32
right✝ : 0 ≤ p.off
w✝ : BlockId
h✝ : p.block = some w✝
hc : ¬x.toNat + (1#32).toNat < 2 ^ 32
⊢ x.toNat + (1#32).toNat < 2 ^ 32
-/
#guard_msgs in
example (p : Ptr) (v : BitVec 32) :
    FTotalTriple (up (pts p 4 v)) (incr p) (fun _ => up (pts p 4 (v + 1))) := by
  set_option fsym.report true in fsym

-- With the bound, nothing is left.
example (p : Ptr) (v : BitVec 32) (fits : v.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts p 4 v)) (incr p) (fun _ => up (pts p 4 (v + 1))) := by
  fsym

-- A returned Zig error is an obligation of the postcondition at that return, distinct from a
-- safety panic.
def check (b : Bool) : MemM (Except ErrName Unit) :=
  if b then pure (.error "Empty") else pure (.ok ())

/--
info: fsym-report {"residuals":[{"goal":{"head":"Eq","text":"Except.error \"Empty\" = Except.ok ()"},"index":0,"origin":{"condition":"postcondition","judgment":"Zig.Full.FLogic.T","program":{"head":"Pure.pure","text":"pure (Except.error \"Empty\")"},"reason":"postcondition_not_proved","rule":{"head":"Zig.Full.Auto.ret","text":"Auto.ret"},"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T emp (pure (Except.error \"Empty\")) fun r => ⟪r = Except.ok ()⟫ ⋆ emp"}}}],"schemaVersion":1,"status":"stopped"}
---
error: unsolved goals
⊢ Except.error "Empty" = Except.ok ()
-/
#guard_msgs in
example (b : Bool) : FTotalTriple emp (check b) (fun r => ⟪r = .ok ()⟫ ⋆ emp) := by
  set_option fsym.report true in fsym

-- A reachable panic is left as the triple of its `throw` on its path (here `b = true`), which
-- no rule proves.
def guarded (b : Bool) : MemM Unit := if b then throw .panic else pure ()

/--
info: fsym-report {"residuals":[{"goal":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T emp (throw Error.panic) fun x => emp"},"index":0,"origin":{"condition":"reachability","judgment":"Zig.Full.FLogic.T","program":{"head":"MonadExcept.throw","text":"throw Error.panic"},"reason":"panic_not_refuted","rule":null,"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T emp (throw Error.panic) fun x => emp"}}}],"schemaVersion":1,"status":"stopped"}
---
error: unsolved goals
case inl
⊢ FLogic.total.T emp (throw Error.panic) fun x => emp
-/
#guard_msgs in
example (b : Bool) : FTotalTriple emp (guarded b) (fun _ => emp) := by
  set_option fsym.report true in fsym

-- That obligation is false: a total triple of a panic has no proof.
example : ¬ FTotalTriple emp (throw .panic : MemM Unit) (fun _ => emp) := by
  intro ht
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ := Witness.FAdmit.of_emp
  exact absurd (ht.1 m r rF hh hp hs : Error.panic = .stackOverflow) (by decide)

-- A raw loop needs an explicit invariant and variant; none is guessed: the loop is left.
def spin (p : Ptr) : MemM Unit := do
  let _ ← (Zig.loop (pure false : MM Unit Bool) id).run ()
  loadStore p

/--
info: fsym-report {"residuals":[{"goal":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T (up (pts p 4 v)) (StateT.run (loop (pure false) id) () >>= fun x => loadStore p >>= pure) fun x =>\n  up (pts p 4 v)"},"index":0,"origin":{"condition":"program","judgment":"Zig.Full.FLogic.T","program":{"head":"StateT.run","text":"StateT.run (loop (pure false) id) ()"},"reason":"no_rule","rule":null,"source":{"head":"Zig.Full.FLogic.T","text":"FLogic.total.T (up (pts p 4 v)) (StateT.run (loop (pure false) id) () >>= fun x => loadStore p >>= pure) fun x =>\n  up (pts p 4 v)"}}}],"schemaVersion":1,"status":"stopped"}
---
error: unsolved goals
p : Ptr
v : BitVec 32
right✝ : 0 ≤ p.off
w✝ : BlockId
h✝ : p.block = some w✝
⊢ FLogic.total.T (up (pts p 4 v)) (StateT.run (loop (pure false) id) () >>= fun x => loadStore p >>= pure) fun x =>
    up (pts p 4 v)
-/
#guard_msgs in
example (p : Ptr) (v : BitVec 32) :
    FTotalTriple (up (pts p 4 v)) (spin p) (fun _ => up (pts p 4 v)) := by
  set_option fsym.report true in fsym

/-! ## Stores of bytes (`docs/architecture-audit/nan-bits.md`)

The translator writes a NaN constant's exact bytes with `Zig.storeBytes`, and a float vector's
store is a `Zig.store` whose bytes, not its value, are what memory holds afterwards (a NaN lane's
bits are undefined). Both write the bytes into an owned region. -/

def storeNaNBits (p : Ptr) : MemM Unit :=
  Zig.storeBytes p 4 (Zig.Enc.encode (2141192194 : BitVec 32))

example (p : Ptr) (bs : Array Byte) (h : bs.size = 4) :
    FTotalTriple (up (region p 4 bs)) (storeNaNBits p)
      (fun _ => up (region p 4 (writeBytes bs 0 (Zig.Enc.encode (2141192194 : BitVec 32))))) := by
  fsym

def storeVec (p : Ptr) (v : Vec F32 4) : MemM Unit := Zig.store (α := Vec F32 4) 16 p v

example (p : Ptr) (bs : Array Byte) (v : Vec F32 4) (h : bs.size = 16) :
    FTotalTriple (up (region p 16 bs)) (storeVec p v)
      (fun _ => up (region p 16 (writeBytes bs 0 (Enc.encode v)))) := by
  fsym

end VCMemory
