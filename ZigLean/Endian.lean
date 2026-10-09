import ZigLean.Packed
import ZigLean.Vec

/-!
# Byte order (T03)

The target's byte order as a parameter: `ByteOrder.little` (x86_64, aarch64) or
`ByteOrder.big` (s390x). It fixes the order of an integer's value bytes in memory, and so of
every type whose bytes are an integer's: floats, a slice's length, enums, packed structs (their
backing integer), bit-pointer hosts and vectors.

A big-endian `uN` has the bytes of the little-endian `uN` in reverse order: the most significant
byte first, so the partly used byte of a `uN` with `N % 8 ≠ 0` (`Byte.part`) comes first. Padding
up to the ABI size (`intSize`) follows the value bytes at both orders, as Zig's
`Value.writeToMemory` writes `(N + 7) / 8` bytes at offset 0.

The definitions of `ZigLean/Mem/Enc.lean`, `Packed.lean` and `Vec.lean` remain the little-endian
model. Each order-parameterized definition here is that model at `.little` by `rfl`
(`intEncOf_little`, `loadBitsOf_little`, …), so little-endian generated code keeps its terms and
proofs. Generated code for a big-endian profile opens `Zig.BigEndian`, whose scoped instances
take priority over the global little-endian ones (`docs/generated-code.md` §Byte order).

Pointer and error bytes are symbolic (`Byte.ptrFrag p i`, `Byte.errFrag e i`): `i` names the
byte's position in the stored value, and no integer read accepts such a byte. Their encodings are
the same at both orders; the order of their fragments is not observable.
-/

namespace Zig

/-- The byte order of a target profile (`profile.endian`). -/
inductive ByteOrder where
  | little
  | big
  deriving DecidableEq, Repr, Inhabited

namespace ByteOrder

/-- The value bytes of an integer at this order, from its little-endian value bytes. -/
@[inline] def arrange : ByteOrder → Array Byte → Array Byte
  | .little, bs => bs
  | .big, bs => bs.reverse

@[simp] theorem arrange_little (bs : Array Byte) : ByteOrder.little.arrange bs = bs := rfl
@[simp] theorem arrange_big (bs : Array Byte) : ByteOrder.big.arrange bs = bs.reverse := rfl

theorem arrange_arrange (o : ByteOrder) (bs : Array Byte) : o.arrange (o.arrange bs) = bs := by
  cases o <;> simp

@[simp] theorem size_arrange (o : ByteOrder) (bs : Array Byte) : (o.arrange bs).size = bs.size := by
  cases o <;> simp

end ByteOrder

/-! ## Integers and floats -/

/-- The value bytes of `v` at order `o` (`intBytes` at `.little`). -/
def intBytesOf (o : ByteOrder) {n : Nat} (v : BitVec n) : Array Byte := o.arrange (intBytes v)

/-- The integer in the first `(n + 7) / 8` bytes at order `o` (`intOfBytes` at `.little`). -/
def intOfBytesOf : ByteOrder → (n : Nat) → Array Byte → (trunc : Bool) → Result (BitVec n)
  | .little, n, bs, trunc => intOfBytes n bs trunc
  | .big, n, bs, trunc => intOfBytes n (bs.extract 0 ((n + 7) / 8)).reverse trunc

theorem intBytesOf_little {n : Nat} (v : BitVec n) : intBytesOf .little v = intBytes v := rfl
theorem intOfBytesOf_little (n : Nat) (bs : Array Byte) (t : Bool) :
    intOfBytesOf .little n bs t = intOfBytes n bs t := rfl

/-- `uN`/`iN` at order `o`: the value bytes, then undefined padding up to `intSize n`. -/
@[instance_reducible] def intEncOf (o : ByteOrder) (n : Nat) : Enc (BitVec n) where
  size := intSize n
  align := intAlign n
  encode v := padTo (intSize n) (intBytesOf o v)
  decode bs := intOfBytesOf o n bs false

/-- The little-endian instance is the existing `Enc (BitVec n)` (`ZigLean/Mem/Enc.lean`). -/
theorem intEncOf_little (n : Nat) : intEncOf .little n = (inferInstance : Enc (BitVec n)) := rfl

/-- A float at order `o`: the bytes of its bits as an integer of the same width. -/
@[instance_reducible] def floatEncOf (o : ByteOrder) (fmt : FloatFmt) : Enc (Float fmt) where
  size := intSize fmt.width
  align := intAlign fmt.width
  encode v := (intEncOf o fmt.width).encode v.bits
  decode bs := do pure ⟨← intOfBytesOf o fmt.width bs false⟩

theorem floatEncOf_little (fmt : FloatFmt) :
    floatEncOf .little fmt = (inferInstance : Enc (Float fmt)) := rfl

/-! ## Slices

A slice is its pointer (symbolic bytes, the same at both orders), then its `usize` length at the
profile's order. -/

@[instance_reducible] def sliceEncOf (o : ByteOrder) : Enc Slice where
  size := 16
  align := 8
  encode s := Enc.encode s.ptr ++ (intEncOf o 64).encode s.len
  decode bs := do
    pure ⟨← Enc.decode (bs.extract 0 8), ← (intEncOf o 64).decode (bs.extract 8 16)⟩

theorem sliceEncOf_little : sliceEncOf .little = (inferInstance : Enc Slice) := rfl

@[instance_reducible] def optSliceEncOf (o : ByteOrder) : Enc (Option Slice) where
  size := 16
  align := 8
  encode
    | none => Array.replicate 8 (.int 0) ++ Array.replicate 8 .undef
    | some s => (sliceEncOf o).encode s
  decode bs :=
    if bs.extract 0 8 == Array.replicate 8 (.int 0) then pure none
    else some <$> (sliceEncOf o).decode bs

theorem optSliceEncOf_little : optSliceEncOf .little = (inferInstance : Enc (Option Slice)) := rfl

/-! ## Vectors

A vector in memory is the integer of its packed lanes (`Vec.packBits`). At `.big` the first lane
is the most significant: the lanes are packed in reverse order, then stored as a big-endian
integer. For lanes of a whole number of bytes this is lane 0's big-endian bytes first, then lane 1's,
…, as LLVM stores `<n x iW>` on a big-endian target. The translator admits big-endian vectors in
memory only with such lanes (`Check.lean`). -/

/-- The packed integer of the lanes of `v` at order `o`. -/
def Vec.packBitsOf (o : ByteOrder) {α : Type} {n : Nat} (w : Nat) (toBits : α → BitVec w)
    (v : Vec α n) : BitVec (n * w) :=
  match o with
  | .little => v.packBits w toBits
  | .big => (⟨v.lanes.reverse⟩ : Vec α n).packBits w toBits

/-- The lanes of the packed integer `x` at order `o`. -/
def Vec.unpackBitsOf (o : ByteOrder) {α : Type} (n w : Nat) (ofBits : BitVec w → α) (x : Nat) :
    Vec α n :=
  match o with
  | .little => ⟨Vector.ofFn fun i => ofBits (laneOf w x i)⟩
  | .big => ⟨(Vector.ofFn fun i => ofBits (laneOf w x i)).reverse⟩

/-- `Vec.packedEnc` at order `o`. -/
@[reducible] def Vec.packedEncOf (o : ByteOrder) {α : Type} (n w : Nat) (toBits : α → BitVec w)
    (ofBits : BitVec w → α) : Enc (Vec α n) where
  size := packedVecLayout n w
  align := packedVecLayout n w
  encode v := padTo (packedVecLayout n w) (intBytesOf o (Vec.packBitsOf o w toBits v))
  decode bs := do
    let x ← intOfBytesOf o (n * w) bs false
    pure (Vec.unpackBitsOf o n w ofBits x.toNat)

theorem Vec.packedEncOf_little {α : Type} (n w : Nat) (toBits : α → BitVec w)
    (ofBits : BitVec w → α) :
    Vec.packedEncOf .little n w toBits ofBits = Vec.packedEnc n w toBits ofBits := rfl

/-! ## Bit-pointers

The host of a bit-pointer is an integer of `hostSize` bytes at the profile's order; the field's
bit offset counts from its least significant bit at both orders (the exporter's `bit_offset`).
The access reads the host bytes, puts them in little-endian order (`ByteOrder.arrange`, its own
inverse), and reads or writes the field's bits as `ZigLean/Packed.lean` does. -/

/-- `loadBits` at order `o`. -/
def loadBitsOf (o : ByteOrder) (α : Type) {n : Nat} [Packed α n] (hostSize align bitOffset : Nat)
    (p : Ptr) : MemM α := do
  let bs ← loadBytes p hostSize align
  match readBits (o.arrange bs) bitOffset n with
  | some b => Packed.ofBits? b
  | none => throw .unspecified

/-- `storeBits` at order `o`. -/
def storeBitsOf (o : ByteOrder) {α : Type} {n : Nat} [Packed α n] (hostSize align bitOffset : Nat)
    (p : Ptr) (v : α) : MemM Unit := do
  let bs ← loadBytes p hostSize align
  storeBytes p align (o.arrange (writeField (o.arrange bs) bitOffset (some (Packed.toBits v))))

/-- `storeUndefBits` at order `o`. -/
def storeUndefBitsOf (o : ByteOrder) (n hostSize align bitOffset : Nat) (p : Ptr) : MemM Unit := do
  let bs ← loadBytes p hostSize align
  storeBytes p align (o.arrange (writeField (o.arrange bs) bitOffset (none : Option (BitVec n))))

theorem loadBitsOf_little (α : Type) {n : Nat} [Packed α n] (hostSize align bitOffset : Nat)
    (p : Ptr) : loadBitsOf .little α hostSize align bitOffset p = loadBits α hostSize align bitOffset p :=
  rfl

theorem storeBitsOf_little {α : Type} {n : Nat} [Packed α n] (hostSize align bitOffset : Nat)
    (p : Ptr) (v : α) :
    storeBitsOf .little hostSize align bitOffset p v = storeBits hostSize align bitOffset p v := rfl

theorem storeUndefBitsOf_little (n hostSize align bitOffset : Nat) (p : Ptr) :
    storeUndefBitsOf .little n hostSize align bitOffset p = storeUndefBits n hostSize align bitOffset p :=
  rfl

/-! ## The big-endian instances

Generated code for a big-endian profile opens `Zig.BigEndian`. Its instances have a priority above
every global `Enc` instance of these types, so a struct, enum, optional, array or error-union
encoding that the generated code builds from them is big-endian too. -/

namespace BigEndian
scoped instance (priority := 20000) encBitVec {n : Nat} : Enc (BitVec n) := intEncOf .big n
scoped instance (priority := 20000) encFloat {fmt : FloatFmt} : Enc (Float fmt) := floatEncOf .big fmt
scoped instance (priority := 20000) encSlice : Enc Slice := sliceEncOf .big
scoped instance (priority := 20000) encOptSlice : Enc (Option Slice) := optSliceEncOf .big
scoped instance (priority := 20000) encVecBitVec {w n : Nat} : Enc (Vec (BitVec w) n) :=
  Vec.packedEncOf .big n w id id
scoped instance (priority := 20000) encVecFloat {fmt : FloatFmt} {n : Nat} : Enc (Vec (Float fmt) n) :=
  Vec.packedEncOf .big n fmt.width Float.bits Float.mk
end BigEndian

end Zig
