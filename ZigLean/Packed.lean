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
read and write the field's `n` bits at bit `o` of it, with defined-bit masks (§Defined bits);
`storeUndefBits` makes them undefined. `ZigLean/PackedLemmas.lean` proves the frame: the other
bits keep their state.
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

/-! ## Defined bits

A bit-pointer access reads and writes the field's bits only. Each host byte is a defined-bit
mask and a value (`Byte.defBits`): `.int` all, `.undef` none, `.part m` the low `m` bits,
`.mask d` the bits of `d`. A store sets the field's bits of each byte (`Byte.writeBits`) and
keeps every other bit as it was, defined or not: an undefined neighbour field stays undefined
bit by bit, and `undefined` stored to a field makes only the field's bits undefined. A load needs
only the field's bits to be defined (`readBits`). -/

/-- The low `m` bits of a byte. -/
def lowMask8 (m : Nat) : BitVec 8 := BitVec.ofNat 8 (2 ^ m - 1)

/-- A byte as its defined-bit mask and its value (0 in undefined bits); `none` for a pointer
or error byte, which has no integer bits. -/
def Byte.defBits : Byte → Option (BitVec 8 × BitVec 8)
  | .undef => some (0, 0)
  | .int x => some (BitVec.allOnes 8, x)
  | .part m x => some (lowMask8 m, x &&& lowMask8 m)
  | .mask d x => some (d, x &&& d)
  | _ => none

/-- The byte with the defined bits `d` and the values `x` there, in its canonical form:
`.int`, `.undef`, `.part m` for the low `m` bits, else `.mask`. -/
def Byte.ofDefBits (d x : BitVec 8) : Byte :=
  if d = BitVec.allOnes 8 then .int x
  else if d = 0 then .undef
  else match [1, 2, 3, 4, 5, 6, 7].find? (lowMask8 · = d) with
    | some m => .part m (x &&& d)
    | none => .mask d (x &&& d)

/-- Bit `k` of a byte: `some b` if it is defined, `none` if it is undefined or the byte has no
integer bits (a pointer or error byte). -/
def Byte.bit (b : Byte) (k : Nat) : Option Bool :=
  match b.defBits with
  | some (d, x) => if d.getLsbD k then some (x.getLsbD k) else none
  | none => none

/-- `b` with the bits in `f` replaced: by the bits of `v` (`some v`), or undefined (`none`).
The other bits keep their state; a byte without bits in `f` is unchanged. A pointer or error
byte that a field overlaps keeps no other defined bits. -/
def Byte.writeBits (f : BitVec 8) (v : Option (BitVec 8)) (b : Byte) : Byte :=
  if f = 0 then b else
  let (d, x) := b.defBits.getD (0, 0)
  match v with
  | some v => Byte.ofDefBits (d ||| f) ((x &&& ~~~f) ||| (v &&& f))
  | none => Byte.ofDefBits (d &&& ~~~f) (x &&& ~~~f)

/-- The bits of byte `i` of the host that belong to the `n`-bit field at bit `o`. -/
def fieldMaskByte (o n i : Nat) : BitVec 8 := BitVec.ofNat 8 (((2 ^ n - 1) <<< o) >>> (8 * i))

/-- Byte `i` of the host with `v` at bit `o` (the field's bits, `fieldMaskByte`, matter). -/
def fieldValByte {n : Nat} (v : BitVec n) (o i : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((v.toNat <<< o) >>> (8 * i))

/-- The host bytes `bs` with the `n`-bit field at bit `o` replaced by `v` (`some`) or made
undefined (`none`), byte by byte. -/
def writeField {n : Nat} (bs : Array Byte) (o : Nat) (v : Option (BitVec n)) : Array Byte :=
  (bs.toList.mapIdx fun i b => b.writeBits (fieldMaskByte o n i) (v.map (fieldValByte · o i))).toArray

/-- Bit `j` of the host bytes `bs` (`Byte.bit`); `none` past the end. -/
def hostBit (bs : Array Byte) (j : Nat) : Option Bool :=
  match bs[j / 8]? with
  | some b => b.bit (j % 8)
  | none => none

/-- The `n` bits at bit `o` of the host bytes `bs`; `none` if one of them is not defined. -/
def readBits (bs : Array Byte) (o : Nat) : (n : Nat) → Option (BitVec n)
  | 0 => some 0#0
  | n + 1 => do
    let hi ← hostBit bs (o + n)
    let lo ← readBits bs o n
    pure (BitVec.cons hi lo)

/-- A load through a bit-pointer: the host integer is the `hostSize` bytes at `p` (the
exporter's `host_size`, which can be less than the ABI size of the integer: `(bits + 7) / 8`
on LLVM). The whole host is read (provenance, bounds, alignment, races); only the field's bits
must be defined, else `.unspecified`. -/
def loadBits (α : Type) {n : Nat} [Packed α n] (hostSize align bitOffset : Nat) (p : Ptr) :
    MemM α := do
  let bs ← loadBytes p hostSize align
  match readBits bs bitOffset n with
  | some b => Packed.ofBits? b
  | none => throw .unspecified

/-- A store through a bit-pointer: read the host, replace the field's bits, write it back.
Every other bit keeps its state (`writeField`), defined or undefined. -/
def storeBits {α : Type} {n : Nat} [Packed α n] (hostSize align bitOffset : Nat) (p : Ptr)
    (v : α) : MemM Unit := do
  let bs ← loadBytes p hostSize align
  storeBytes p align (writeField bs bitOffset (some (Packed.toBits v)))

/-- A store of `undefined` through a bit-pointer: the field's `n` bits become undefined, bit by
bit; every other bit keeps its state. -/
def storeUndefBits (n hostSize align bitOffset : Nat) (p : Ptr) : MemM Unit := do
  let bs ← loadBytes p hostSize align
  storeBytes p align (writeField bs bitOffset (none : Option (BitVec n)))

end Zig
