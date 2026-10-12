import ZigLean.VC
import ZigLean.VecMem

/-!
Memory VCs on the full-state logic (`docs/vcs.md`): `vc_gen` on an `FTotalTriple`/`FTriple`
goal is the walk of `fsym`, and the goals the walk leaves are the obligations. The programs are
small functions written as the translator writes them.
-/

namespace VCMemory

open Zig Zig.Full FAssn VC

def loadStore (p : Ptr) : MemM Unit := do
  let x ← Zig.load (BitVec 32) 4 p
  Zig.store (α := BitVec 32) 4 p x

def incr (p : Ptr) : MemM Unit := do
  let x ← Zig.load (BitVec 32) 4 p
  let y ← Zig.add false x (1 : BitVec 32)
  Zig.store (α := BitVec 32) 4 p y

-- Ownership is not assumed: without the cell no rule executes the load, and `vc_gen` refuses.
/--
info: fsym: no rule for the command
  load (BitVec 32) 4 p
with the precondition
  emp
---
error: vc_gen: the walk stopped at the command
  load (BitVec 32) 4 p
(no `@[fsym]` rule or `@[vc_contract]` theorem executes it, or the step budget ran out)
-/
#guard_msgs in
example (p : Ptr) : FTotalTriple emp (loadStore p) (fun _ => emp) := by
  vc_gen

-- A fabricated postcondition cannot ignore the actual heap: the heap obligation is left.
/--
error: unsolved goals
case memory_1
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
  vc_gen

-- Overflow stays a safety obligation even when the postcondition is the true one.
/--
error: unsolved goals
case safety_1
p : Ptr
x : BitVec 32
right✝ : 0 ≤ p.off
w✝ : BlockId
h✝ : p.block = some w✝
⊢ x.toNat + (1#32).toNat < 2 ^ 32
-/
#guard_msgs in
example (p : Ptr) (v : BitVec 32) :
    FTotalTriple (up (pts p 4 v)) (incr p) (fun _ => up (pts p 4 (v + 1))) := by
  vc_gen

-- With the bound, nothing is left.
example (p : Ptr) (v : BitVec 32) (fits : v.toNat + 1 < 2 ^ 32) :
    FTotalTriple (up (pts p 4 v)) (incr p) (fun _ => up (pts p 4 (v + 1))) := by
  vc_gen

-- A returned Zig error is an `error` obligation, distinct from a safety panic.
def check (b : Bool) : MemM (Except ErrName Unit) :=
  if b then pure (.error "Empty") else pure (.ok ())

/--
error: unsolved goals
case error_1
⊢ Except.error "Empty" = Except.ok ()
-/
#guard_msgs in
example (b : Bool) : FTotalTriple emp (check b) (fun r => ⟪r = .ok ()⟫ ⋆ emp) := by
  vc_gen

-- A reachable panic is the safety obligation `False` on its path (here `b = true`).
def guarded (b : Bool) : MemM Unit := if b then throw .panic else pure ()

/--
error: unsolved goals
case safety_1
⊢ False
-/
#guard_msgs in
example (b : Bool) : FTotalTriple emp (guarded b) (fun _ => emp) := by
  vc_gen

-- A raw loop needs an explicit invariant and variant; none is guessed.
def spin (p : Ptr) : MemM Unit := do
  let _ ← (Zig.loop (pure false : MM Unit Bool) id).run ()
  loadStore p

/--
error: vc extraction for `VCMemory.spin`:
  invariant + variant required for loop `VCMemory.spin` at an unnamed AIR loop
VC extraction does not guess invariants. For a memory loop, prove `(Zig.loop body again).run s` with `FTotalTriple.loop_ghost inv post` (the measure carried by `inv s n`) or `FTriple.loop inv post` (`ZigLean/Sep/Full/Loop.lean`); for a `Result` loop use `Zig.loop_spec` (invariant `inv`, variant `m`). Register the proved function contract with `@[vc_contract]` so callers can use it.
vc-report {"function":"VCMemory.spin","requests":[{"instruction":null,"loop":"VCMemory.spin","request":"invariant + variant"}],"status":"loop-request"}
-/
#guard_msgs in
example (p : Ptr) (v : BitVec 32) :
    FTotalTriple (up (pts p 4 v)) (spin p) (fun _ => up (pts p 4 v)) := by
  vc_gen

/-! ## Stores of bytes (`docs/architecture-audit/nan-bits.md`)

The translator writes a NaN constant's exact bytes with `Zig.storeBytes`, and a float vector's
store is a `Zig.store` whose bytes, not its value, are what memory holds afterwards (a NaN lane's
bits are undefined). Both write the bytes into an owned region. -/

def storeNaNBits (p : Ptr) : MemM Unit :=
  Zig.storeBytes p 4 (Zig.Enc.encode (2141192194 : BitVec 32))

example (p : Ptr) (bs : Array Byte) (h : bs.size = 4) :
    FTotalTriple (up (region p 4 bs)) (storeNaNBits p)
      (fun _ => up (region p 4 (writeBytes bs 0 (Zig.Enc.encode (2141192194 : BitVec 32))))) := by
  vc_gen

def storeVec (p : Ptr) (v : Vec F32 4) : MemM Unit := Zig.store (α := Vec F32 4) 16 p v

example (p : Ptr) (bs : Array Byte) (v : Vec F32 4) (h : bs.size = 16) :
    FTotalTriple (up (region p 16 bs)) (storeVec p v)
      (fun _ => up (region p 16 (writeBytes bs 0 (Enc.encode v)))) := by
  vc_gen

end VCMemory
