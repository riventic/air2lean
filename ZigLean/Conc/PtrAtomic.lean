import ZigLean.Conc.Call
import ZigLean.Mem.AtomicPtr

/-!
# Pointer atomics in a concurrent function

The sync ops that `Emit.lean` writes for an atomic op on a `*T` or `?*T` pointee
(`ZigLean/Mem/AtomicPtr.lean`): a `pick` of the oracle, then the op in `MemM`, as the integer ops
of `ZigLean/Conc/Call.lean`. `α` is `Zig.Ptr` or `Option Zig.Ptr`.
-/

namespace Zig

variable {Tgt σ α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α]

def atomicLoadPtrC (α : Type) [Enc α] (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    CM Tgt σ α := do
  let c ← pickC (loadCount 64 ord align p)
  callMC (atomicLoadPtrAt α c ord align p)

def atomicStorePtrC (ord : AtomicOrder) (align : Nat) (p : Ptr) (v : α) : CM Tgt σ Unit := do
  let c ← pickC (storeCount 64 ord align p)
  callMC (atomicStorePtrAt c ord align p v)

def atomicXchgPtrC (ord : AtomicOrder) (align : Nat) (p : Ptr) (v : α) : CM Tgt σ α := do
  let c ← pickC (rmwCount 64 ord align p)
  callMC (atomicXchgPtrAt c ord align p v)

def cmpxchgPtrC (succ fail : AtomicOrder) (align : Nat) (p : Ptr) (expected new : α) :
    CM Tgt σ (Option α) := do
  let c ← pickC (casPtrCount align p expected)
  callMC (cmpxchgPtrAt c succ fail align p expected new)

def cmpxchgWeakPtrC (succ fail : AtomicOrder) (align : Nat) (p : Ptr) (expected new : α) :
    CM Tgt σ (Option α) := do
  let c ← pickC (weakCasPtrCount align p expected)
  callMC (cmpxchgWeakPtrAt c succ fail align p expected new)

end Zig
