import ZigLean.Mem.Enc

/-!
# `packed struct`

`Zig.Packed α n`: a type that is `n` bits in a packed struct. `Emit.lean` writes an instance for
each packed struct: `toBits` puts field 0 in the lowest bits, as Zig does; `ofBits` reads the
fields back. `@bitCast` between a packed struct and its backing integer is `toBits`/`ofBits`.

In memory a packed struct is its backing integer (the instance's `Enc`). A bit-pointer
(`&p.field`, `*align(a:o:h) T`) points to the host integer (`h` bytes); `loadBits`/`storeBits`
read and write the field's `n` bits at bit `o` of it.
-/

namespace Zig

class Packed (α : Type) (n : outParam Nat) where
  toBits : α → BitVec n
  ofBits : BitVec n → α

instance {n : Nat} : Packed (BitVec n) n where
  toBits v := v
  ofBits v := v

instance : Packed Bool 1 where
  toBits b := if b then 1#1 else 0#1
  ofBits v := v == 1#1

/-- The `n` bits of `α` at bit `o` of `host`. -/
def Packed.get {α : Type} {n w : Nat} [Packed α n] (host : BitVec w) (o : Nat) : α :=
  Packed.ofBits (host.extractLsb' o n)

/-- `host` with the `n` bits at bit `o` replaced by `v`. -/
def Packed.set {α : Type} {n w : Nat} [Packed α n] (host : BitVec w) (o : Nat) (v : α) :
    BitVec w :=
  let mask : BitVec w := ((BitVec.allOnes n).setWidth w) <<< o
  (host &&& ~~~mask) ||| (((Packed.toBits v).setWidth w) <<< o)

/-- A load through a bit-pointer: the host integer is `hostSize` bytes at `p`. -/
def loadBits (α : Type) {n : Nat} [Packed α n] (hostSize align bitOffset : Nat) (p : Ptr) :
    MemM α := do
  let host ← load (BitVec (8 * hostSize)) align p
  pure (Packed.get host bitOffset)

/-- A store through a bit-pointer: read the host integer, replace the field's bits, write it
back. -/
def storeBits {α : Type} {n : Nat} [Packed α n] (hostSize align bitOffset : Nat) (p : Ptr)
    (v : α) : MemM Unit := do
  let host ← load (BitVec (8 * hostSize)) align p
  store align p (Packed.set host bitOffset v)

end Zig
