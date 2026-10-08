import ZigLean
import ZigLean.Conc.PtrAtomic

namespace PP
open Zig

inductive Tgt where
  | producer (slot : Ptr)

def producer (slot : Ptr) : ConcM Tgt Unit :=
  ((do
    match ← Zig.callMC (Zig.Allocator.create ⟨⟩ 4 4) with
    | .error _ => pure ()
    | .ok n =>
      Zig.store (α := BitVec 32) 4 n (42 : BitVec 32)
      Zig.atomicStorePtrC (α := Option Zig.Ptr) .release 8 slot (some n)) : Zig.CM Tgt Unit Unit).run' ()

def dispatch : Tgt → ConcM Tgt Unit
  | .producer s => producer s

def publishRead : ConcM Tgt (BitVec 32) := do
  let slot ← Zig.allocStack 8 8
  let r ← ((do
    Zig.store (α := Option Zig.Ptr) 8 slot none
    match ← Zig.spawnC (Tgt.producer slot) with
    | .error _ => pure (0 : BitVec 32)
    | .ok h =>
      let r ← match ← Zig.atomicLoadPtrC (Option Zig.Ptr) .acquire 8 slot with
        | some p => Zig.load (BitVec 32) 4 p
        | none => pure 0
      Zig.joinC h
      match ← Zig.atomicLoadPtrC (Option Zig.Ptr) .relaxed 8 slot with
      | some p => Zig.callMC (Zig.Allocator.destroy ⟨⟩ 4 p)
      | none => pure ()
      pure r) : Zig.CM Tgt Unit (BitVec 32)).run' ()
  Zig.free slot
  pure r

def okVal (r : Result (BitVec 32 × Mem)) : Option Nat :=
  match r.run with
  | some (.ok (v, _)) => some v.toNat
  | _ => none
def sched (cs : List Nat) : Nat → Nat := fun i => cs.getD i 0

#eval okVal (Sched.run dispatch 100 (sched []) publishRead {})
#eval okVal (Sched.run dispatch 100 (sched [0,1,1]) publishRead {})
#eval (List.range 64).map fun k => okVal (Sched.run dispatch 100 (fun i => (k >>> i) % 2) publishRead {})
end PP
