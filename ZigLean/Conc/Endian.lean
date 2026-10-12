import ZigLean.Conc.Call
import ZigLean.Conc.AtomicWord
import ZigLean.Endian
import ZigLean.Permutation

/-!
# Atomics and futexes at a byte order (T03)

The atomic messages of `ZigLean/Mem/Thread.lean` are the location's memory bytes, and its ops
read and write them as a little-endian integer. On a big-endian target (`ZigLean/Endian.lean`)
an `n`-bit integer with `n % 8 = 0` is stored with its value bytes reversed, so the little-endian
integer of those bytes is `byteSwap v`; a value of at most one byte is the same at both orders.
At `.big` every op here is the little-endian op conjugated by `byteSwap`: a load swaps the value
it read, a store and the operands of a `cmpxchg` swap before writing or comparing (the swap is a
bijection, so the comparison of messages is unchanged), and an RMW applies the op to the swapped
old value and writes the swapped result (`atomicRmwFnAt`). A futex compares the 32-bit word the
same way. The checker admits big-endian atomics only on representations of at most 8 bits or of
a whole number of bytes (`Check.lean`'s `checkBigEndian`). Pointer atomics keep their symbolic
bytes, the same at both orders.

`Emit.lean` writes the `…Of .big` op for a big-endian profile; little-endian translations keep
the existing ops, and every `…Of .little` op is the existing one (`atomicLoadCOf_little`, …).
-/

namespace Zig

/-- The little-endian integer of the bytes of `v` stored at order `o`: `byteSwap v` at `.big`
(the identity for at most 8 bits). -/
def ByteOrder.swapBits (o : ByteOrder) {n : Nat} (v : BitVec n) : BitVec n :=
  match o with
  | .little => v
  | .big => byteSwap v

@[simp] theorem ByteOrder.swapBits_little {n : Nat} (v : BitVec n) :
    ByteOrder.little.swapBits v = v := rfl

theorem ByteOrder.swapBits_swapBits (o : ByteOrder) {n : Nat} (v : BitVec n) (hn : n % 8 = 0) :
    o.swapBits (o.swapBits v) = v := by
  cases o
  · rfl
  · exact byteSwap_involution v hn

variable {Tgt σ : Type}

def atomicLoadCOf (o : ByteOrder) {n : Nat} (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    CM Tgt σ (BitVec n) :=
  match o with
  | .little => atomicLoadC ord align p
  | .big => byteSwap <$> atomicLoadC ord align p

def atomicLoadUnorderedCOf (o : ByteOrder) {n : Nat} (align : Nat) (p : Ptr) :
    CM Tgt σ (BitVec n) :=
  match o with
  | .little => atomicLoadUnorderedC align p
  | .big => byteSwap <$> atomicLoadUnorderedC align p

def atomicStoreCOf (o : ByteOrder) {n : Nat} (ord : AtomicOrder) (align : Nat) (p : Ptr)
    (v : BitVec n) : CM Tgt σ Unit :=
  atomicStoreC ord align p (o.swapBits v)

def atomicRmwCOf (o : ByteOrder) {n : Nat} (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
    (align : Nat) (p : Ptr) (v : BitVec n) : CM Tgt σ (BitVec n) :=
  match o with
  | .little => atomicRmwC op signed ord align p v
  | .big => do
    let c ← pickC (rmwCount n ord align p)
    byteSwap <$> callMC (atomicRmwFnAt c (fun old => byteSwap (op.apply signed (byteSwap old) v))
      ord align p)

def cmpxchgCOf (o : ByteOrder) {n : Nat} (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : BitVec n) : CM Tgt σ (Option (BitVec n)) :=
  match o with
  | .little => cmpxchgC succ fail align p expected new
  | .big => (·.map byteSwap) <$> cmpxchgC succ fail align p (byteSwap expected) (byteSwap new)

def cmpxchgWeakCOf (o : ByteOrder) {n : Nat} (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : BitVec n) : CM Tgt σ (Option (BitVec n)) :=
  match o with
  | .little => cmpxchgWeakC succ fail align p expected new
  | .big => (·.map byteSwap) <$> cmpxchgWeakC succ fail align p (byteSwap expected) (byteSwap new)

/-! ### On an enum, a `bool` or a packed struct: the integer op on its bits -/

def atomicLoadAsCOf (o : ByteOrder) (α : Type) {n : Nat} [Packed α n] (ord : AtomicOrder)
    (align : Nat) (p : Ptr) : CM Tgt σ α := do
  callRC (Packed.ofBits? (← atomicLoadCOf o (n := n) ord align p))

def atomicStoreAsCOf (o : ByteOrder) {α : Type} {n : Nat} [Packed α n] (ord : AtomicOrder)
    (align : Nat) (p : Ptr) (v : α) : CM Tgt σ Unit :=
  atomicStoreCOf o ord align p (Packed.toBits v)

def atomicRmwAsCOf (o : ByteOrder) {α : Type} {n : Nat} [Packed α n] (op : RmwOp)
    (ord : AtomicOrder) (align : Nat) (p : Ptr) (v : α) : CM Tgt σ α := do
  callRC (Packed.ofBits? (← atomicRmwCOf o op false ord align p (Packed.toBits v)))

def cmpxchgAsCOf (o : ByteOrder) {α : Type} {n : Nat} [Packed α n] (succ fail : AtomicOrder)
    (align : Nat) (p : Ptr) (expected new : α) : CM Tgt σ (Option α) := do
  match ← cmpxchgCOf o succ fail align p (Packed.toBits expected) (Packed.toBits new) with
  | none => pure none
  | some b => some <$> callRC (Packed.ofBits? b)

def cmpxchgWeakAsCOf (o : ByteOrder) {α : Type} {n : Nat} [Packed α n] (succ fail : AtomicOrder)
    (align : Nat) (p : Ptr) (expected new : α) : CM Tgt σ (Option α) := do
  match ← cmpxchgWeakCOf o succ fail align p (Packed.toBits expected) (Packed.toBits new) with
  | none => pure none
  | some b => some <$> callRC (Packed.ofBits? b)

/-! ### Futexes: the kernel compares the 32-bit word -/

def futexWaitCOf (o : ByteOrder) {α : Type} {n : Nat} [Packed α n] (_ : Io) (p : Ptr)
    (expected : α) : CM Tgt σ Unit :=
  StateT.lift (discard (ConcM.sync (Tgt := Tgt)
    (.wait p (o.swapBits ((Packed.toBits expected).setWidth 32)))))

def futexWaitCancelableCOf (o : ByteOrder) {α : Type} {n : Nat} [Packed α n] (io : Io) (p : Ptr)
    (expected : α) : CM Tgt σ (Except ErrName Unit) := do
  if ← callMC Thread.cancelPending then
    callMC Thread.takeCancel
    pure (.error "Canceled")
  else
    futexWaitCOf o io p expected
    lateCancelC

def threadFutexWaitCOf (o : ByteOrder) (p : Ptr) (expected : BitVec 32) : CM Tgt σ Unit :=
  threadFutexWaitC p (o.swapBits expected)

/-! ### `.little` is the existing model -/

theorem atomicLoadCOf_little {n : Nat} (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    (atomicLoadCOf .little ord align p : CM Tgt σ (BitVec n)) = atomicLoadC ord align p := rfl

theorem atomicStoreCOf_little {n : Nat} (ord : AtomicOrder) (align : Nat) (p : Ptr) (v : BitVec n) :
    (atomicStoreCOf .little ord align p v : CM Tgt σ Unit) = atomicStoreC ord align p v := rfl

theorem atomicRmwCOf_little {n : Nat} (op : RmwOp) (signed : Bool) (ord : AtomicOrder) (align : Nat)
    (p : Ptr) (v : BitVec n) :
    (atomicRmwCOf .little op signed ord align p v : CM Tgt σ (BitVec n)) =
      atomicRmwC op signed ord align p v := rfl

theorem cmpxchgCOf_little {n : Nat} (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : BitVec n) :
    (cmpxchgCOf .little succ fail align p expected new : CM Tgt σ (Option (BitVec n))) =
      cmpxchgC succ fail align p expected new := rfl

theorem threadFutexWaitCOf_little (p : Ptr) (expected : BitVec 32) :
    (threadFutexWaitCOf .little p expected : CM Tgt σ Unit) = threadFutexWaitC p expected := rfl

end Zig
