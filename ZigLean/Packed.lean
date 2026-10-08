import ZigLean.Mem.Enc

/-!
# `packed struct`

`Zig.Packed α n`: a type that is `n` bits in a packed struct. `Emit.lean` writes an instance for
each packed struct: `toBits` puts field 0 in the lowest bits, as Zig does; `ofBits` reads the
fields back. `@bitCast` between a packed struct and its backing integer is `toBits`/`ofBits`.

`valid` is `false` for bits that are not a value: a tag value without a name of an exhaustive
enum, in any field. Where bits become a value (a load, `@bitCast`, a bit-pointer or a `packed`
union read), `ofBits?` throws `.illegal` for them, as the `Enc` of an enum does.

In memory a packed struct is its backing integer (the instance's `Enc`). A bit-pointer
(`&p.field`, `*align(a:o:h) T`) points to the host integer (`h` bytes); `loadBits`/`storeBits`
read and write the field's `n` bits at bit `o` of it.
-/

namespace Zig

class Packed (α : Type) (n : outParam Nat) where
  toBits : α → BitVec n
  ofBits : BitVec n → α
  valid : BitVec n → Bool := fun _ => true

instance {n : Nat} : Packed (BitVec n) n where
  toBits v := v
  ofBits v := v

instance : Packed Bool 1 where
  toBits b := if b then 1#1 else 0#1
  ofBits v := v == 1#1

/-- The `n` bits of `α` at bit `o` of `host`. -/
def Packed.get {α : Type} {n w : Nat} [Packed α n] (host : BitVec w) (o : Nat) : α :=
  Packed.ofBits (host.extractLsb' o n)

/-- `ofBits` where bits become a value: bits that are not `valid` throw `.illegal`. -/
def Packed.ofBits? {α : Type} {n : Nat} [Packed α n] (b : BitVec n) : Result α :=
  if Packed.valid (α := α) b then pure (Packed.ofBits b) else throw .illegal

/-- The `n` bits of `α` at bit `o` of `host` are `valid`. -/
def Packed.validAt (α : Type) {n w : Nat} [Packed α n] (host : BitVec w) (o : Nat) : Bool :=
  Packed.valid (α := α) (host.extractLsb' o n)

/-- `host` with the `n` bits at bit `o` replaced by `v`. -/
def Packed.set {α : Type} {n w : Nat} [Packed α n] (host : BitVec w) (o : Nat) (v : α) :
    BitVec w :=
  let mask : BitVec w := ((BitVec.allOnes n).setWidth w) <<< o
  (host &&& ~~~mask) ||| (((Packed.toBits v).setWidth w) <<< o)

/-- The host integer of a bit-pointer, from its `hostSize` bytes at `p`. A packed struct whose
backing integer is not `8 * hostSize` bits has undefined padding bits in its last byte
(`Byte.part`, `intBytes`): they read as 0, because an access reads or writes only the field's
bits, the bits below `fieldEnd`. A field bit that is undefined throws `.unspecified`. Also the
last byte's kind, to write it back the same way. -/
def loadHost (hostSize align fieldEnd : Nat) (p : Ptr) :
    MemM (BitVec (8 * hostSize) × Option Nat) := do
  let bs ← loadBytes p (Enc.size (BitVec (8 * hostSize))) align
  let last := match (bs[hostSize - 1]? : Option Byte) with | some (.part m _) => some m | _ => none
  if let some m := last then
    if 8 * (hostSize - 1) + m < fieldEnd then throw .unspecified
  let bs := bs.modify (hostSize - 1) fun | .part _ x => .int x | b => b
  let host ← intOfBytes (8 * hostSize) bs
  pure (host, last)

/-- A load through a bit-pointer: the host integer is `hostSize` bytes at `p`. -/
def loadBits (α : Type) {n : Nat} [Packed α n] (hostSize align bitOffset : Nat) (p : Ptr) :
    MemM α := do
  let (host, _) ← loadHost hostSize align (bitOffset + n) p
  Packed.ofBits? (host.extractLsb' bitOffset n)

/-- A store through a bit-pointer: read the host integer, replace the field's bits, write it
back. Undefined padding bits in the last byte stay undefined. -/
def storeBits {α : Type} {n : Nat} [Packed α n] (hostSize align bitOffset : Nat) (p : Ptr)
    (v : α) : MemM Unit := do
  let (host, last) ← loadHost hostSize align (bitOffset + n) p
  let bs := Enc.encode (Packed.set host bitOffset v)
  let bs := match last, (bs[hostSize - 1]? : Option Byte) with
    | some m, some (.int x) => bs.set! (hostSize - 1) (.part m (x &&& BitVec.ofNat 8 (2 ^ m - 1)))
    | _, _ => bs
  storeBytes p align bs


/-! ## Vector lanes

A pointer to one lane of a vector whose lanes are not a power-of-two number of bytes
(`&v[i]` of `@Vector(n, u9)`, `u3`, `u24` or `bool`; Zig's type `*align(a:0:n:i) T`) is a
bit-pointer into the vector's `n * w`-bit integer (`ZigLean/Vec.lean`'s `Vec.packedEnc`, the
LLVM backend's layout): `Check.lean` gives it the host `⌈n * w / 8⌉` bytes, the vector's
LLVM store size, and the bit offset `i * w`. LLVM loads the whole vector and extracts or
inserts the lane, then stores the whole vector.

Unlike a packed struct's host, a vector in memory can be partly undefined: an `undefined`
vector that the program fills lane by lane. So `loadLane`/`storeLane` look at the bits of
each byte: a load needs only the lane's own bits defined, and a store replaces only the lane's
bits. A `Byte` has a defined low prefix (`Byte.part`), so a lane whose bits start above the
defined bits of a byte cannot be written into it: that byte stays as it was and the lane reads
as undefined (`.unspecified`), never as a wrong value. Lanes written in increasing order (as
Zig initializes a vector) are always defined. `ZigLean/VecMem.lean` proves that on a defined
vector a lane load reads the lane and a lane store leaves exactly the image of `Vec.set`.
-/

/-- The defined low bits of a byte: how many (8 for `.int`, `m` for `.part m`, else 0) and their
value. -/
def Byte.lowBits : Byte → Nat × Nat
  | .int x => (8, x.toNat)
  | .part m x => (Nat.min m 8, x.toNat % 2 ^ Nat.min m 8)
  | _ => (0, 0)

/-- The bits `[lo, hi)` of byte `k` of a host that a lane of `w` bits at bit `o` covers (empty if
`hi ≤ lo`). -/
def laneSpan (k o w : Nat) : Nat × Nat := (Nat.min 8 (o - 8 * k), Nat.min 8 (o + w - 8 * k))

/-- Every bit of the lane of `w` bits at bit `o` of the host bytes `bs` is defined. -/
def laneDefined (bs : Array Byte) (o w : Nat) : Bool :=
  (List.range bs.size).all fun k =>
    let (lo, hi) := laneSpan k o w
    hi ≤ lo || hi ≤ (bs[k]!).lowBits.1

/-- The host bytes as an integer, little-endian, with undefined bits as 0. -/
def hostVal (bs : Array Byte) : Nat := bs.toList.foldr (fun b acc => b.lowBits.2 + 256 * acc) 0

/-- Byte `k` of a host after a write of the lane bits `x` (`< 2 ^ w`) at bit `o`: the bits that
the lane covers replaced, the others kept. If the lane's bits start above the byte's defined
bits, the byte cannot hold them and stays as it was. -/
def Byte.setLane (b : Byte) (k o w x : Nat) : Byte :=
  let (lo, hi) := laneSpan k o w
  let (m, old) := b.lowBits
  if hi ≤ lo || m < lo then b else
  -- The lane's bits in this byte, at `[lo, hi)`.
  let bits := (x >>> (8 * k + lo - o)) % 2 ^ (hi - lo)
  let v := (old % 2 ^ lo) ||| (bits <<< lo) ||| ((old >>> hi) <<< hi)
  if Nat.max m hi = 8 then .int (BitVec.ofNat 8 v) else .part (Nat.max m hi) (BitVec.ofNat 8 v)

/-- A load through a lane pointer: the `n` bits at `bitOffset` of the `hostSize` bytes at `p`. -/
def loadLane (α : Type) {n : Nat} [Packed α n] (hostSize align bitOffset : Nat) (p : Ptr) :
    MemM α := do
  let bs ← loadBytes p hostSize align
  if laneDefined bs bitOffset n then Packed.ofBits? (BitVec.ofNat n (hostVal bs >>> bitOffset))
  else throw .unspecified

/-- A store through a lane pointer: read the `hostSize` bytes at `p`, replace the lane's bits,
write them back. -/
def storeLane {α : Type} {n : Nat} [Packed α n] (hostSize align bitOffset : Nat) (p : Ptr)
    (v : α) : MemM Unit := do
  let bs ← loadBytes p hostSize align
  storeBytes p align (bs.mapIdx fun k b => b.setLane k bitOffset n (Packed.toBits v).toNat)

end Zig
