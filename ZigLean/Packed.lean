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

`Packed` is also the *logical bit representation* of every packable type (Zig 0.17's
`@bitCast`, `ZigLean/PackedRepr.lean`): floats, packed unions, arrays and vectors get instances
there. `mask` gives the bits of a value that are determined: all of them for an integer, `bool`,
enum or packed struct of these; none for a NaN (the model's canonical NaN stands for any NaN,
`docs/floats.md` §NaN); the defined bits of a packed union's bytes. Where a value becomes bits
that someone can observe (`toBits?`, a bit-pointer store, a packed struct's memory image), an
undetermined bit is undefined, never the model's choice.
-/

namespace Zig

class Packed (α : Type) (n : outParam Nat) where
  toBits : α → BitVec n
  ofBits : BitVec n → α
  valid : BitVec n → Bool := fun _ => true
  /-- The bits of a value that are determined (`toBits` gives the others as 0). -/
  mask : α → BitVec n := fun _ => BitVec.allOnes n

instance {n : Nat} : Packed (BitVec n) n where
  toBits v := v
  ofBits v := v

instance : Packed Bool 1 where
  toBits b := if b then 1#1 else 0#1
  ofBits v := v == 1#1

/-- A float lane is its bits (`Float.bits`): the lane of a lane pointer into a bit-packed float
vector (`@Vector(n, f80)`'s 80-bit lanes, L09; `Zig.loadLane`/`Zig.storeLane`). -/
instance {fmt : FloatFmt} : Packed (Float fmt) fmt.width where
  toBits f := f.bits
  ofBits b := ⟨b⟩

/-- The `n` bits of `α` at bit `o` of `host`. -/
def Packed.get {α : Type} {n w : Nat} [Packed α n] (host : BitVec w) (o : Nat) : α :=
  Packed.ofBits (host.extractLsb' o n)

/-- `ofBits` where bits become a value: bits that are not `valid` throw `.illegal`. -/
def Packed.ofBits? {α : Type} {n : Nat} [Packed α n] (b : BitVec n) : Result α :=
  if Packed.valid (α := α) b then pure (Packed.ofBits b) else throw .illegal

/-- The `n` bits of `α` at bit `o` of `host` are `valid`. -/
def Packed.validAt (α : Type) {n w : Nat} [Packed α n] (host : BitVec w) (o : Nat) : Bool :=
  Packed.valid (α := α) (host.extractLsb' o n)

/-- The bits of `v` if every one of them is determined (`mask`), else `none`. -/
def Packed.defBits? {α : Type} {n : Nat} [Packed α n] (v : α) : Option (BitVec n) :=
  if Packed.mask v = BitVec.allOnes n then some (Packed.toBits v) else none

/-- `@bitCast` of `v` to its bits: an undetermined bit (a NaN's, an undefined bit of a packed
union) has no value, `.unspecified`, as `Float.toBits?` does for a NaN. -/
def Packed.toBits? {α : Type} {n : Nat} [Packed α n] (v : α) : Result (BitVec n) :=
  match Packed.defBits? v with
  | some b => pure b
  | none => throw .unspecified

/-! ## Defined bits

A bit-pointer access reads and writes the field's bits only. Each host byte is a defined-bit
mask and a value (`Byte.defBits`, `ZigLean/Mem/Enc.lean`): `.int` all, `.undef` none, `.part m` the low `m` bits,
`.mask d` the bits of `d`. A store sets the field's bits of each byte (`Byte.writeBits`) and
keeps every other bit as it was, defined or not: an undefined neighbour field stays undefined
bit by bit, and `undefined` stored to a field makes only the field's bits undefined. A load needs
only the field's bits to be defined (`readBits`). -/

/-- The value bytes of `v` (`intBytes`), each bit defined where `Packed.mask` says. -/
def Packed.bytes {α : Type} {n : Nat} [Packed α n] (v : α) : Array Byte :=
  maskedBytes (Packed.toBits v) (Packed.mask v)

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
Every other bit keeps its state (`writeField`), defined or undefined. A value with an
undetermined bit (`Packed.mask`: a NaN, a packed union with undefined bits) leaves the whole
field undefined. -/
def storeBits {α : Type} {n : Nat} [Packed α n] (hostSize align bitOffset : Nat) (p : Ptr)
    (v : α) : MemM Unit := do
  let bs ← loadBytes p hostSize align
  storeBytes p align (writeField bs bitOffset (Packed.defBits? v))

/-- A store of `undefined` through a bit-pointer: the field's `n` bits become undefined, bit by
bit; every other bit keeps its state. -/
def storeUndefBits (n hostSize align bitOffset : Nat) (p : Ptr) : MemM Unit := do
  let bs ← loadBytes p hostSize align
  storeBytes p align (writeField bs bitOffset (none : Option (BitVec n)))

/-! ## Vector lanes

A pointer to one lane of a vector whose lanes are not a power-of-two number of bytes
(`&v[i]` of `@Vector(n, u9)`, `u3`, `u24` or `bool`; Zig's type `*align(a:0:n:i) T`) is a
bit-pointer into the vector's `n * w`-bit integer (`ZigLean/Vec.lean`'s `Vec.packedEnc`, the
LLVM backend's layout): `Air2Lean/Air/Normalize.lean`'s `lanePtrLayout` gives it the host
`⌈n * w / 8⌉` bytes, the vector's LLVM store size, and the bit offset `i * w`. LLVM loads the whole vector and extracts or
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

/-- Byte `k` of a host after a write of the `w` lane bits `x` at bit `o`: the bits that the lane
covers replaced, the others kept. If the lane's bits start above the byte's defined
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

/-- `vector_store_elem`: `v[i] = x` through a pointer `p` to a bit-packed vector of `lanes`
lanes of `w` bits with a runtime index (Zig 0.14.1/0.15.2; 0.16.0 rejects a runtime vector
index): the store through the lane pointer of lane `i` (`storeLane` at bit `i * w`). An index
past the lanes is illegal behaviour; a safe build checks it first (the `outOfBounds` panic). -/
def storeLaneAt {α : Type} {w : Nat} [Packed α w] (lanes hostSize align : Nat) (p : Ptr)
    (i : BitVec 64) (v : α) : MemM Unit :=
  if i.toNat < lanes then storeLane hostSize align (i.toNat * w) p v else throw .illegal

end Zig
