import ZigLean.Union
import ZigLean.Endian
import ZigLean.BitCast

/-!
# Logical bit representation of every packable type (L07, L08)

`Zig.Packed α n` (`ZigLean/Packed.lean`) is a type's `n`-bit *logical* representation: what a
packed struct or union field holds, what a bit-pointer reads and writes, and what Zig 0.17's
`@bitCast` reinterprets (`docs/bitcast-semantics.md`). Integers, `bool`, enums and packed structs
have instances there or in the generated code; this file adds the rest of Zig's packable types,
so one class serves packed fields and logical casts alike:

* a float is its IEEE bits; a NaN has no determined bits (`mask` 0: the model's canonical NaN
  stands for every NaN, `docs/floats.md` §NaN), so a NaN observed as bits is undefined, never
  the canonical pattern;
* an array `[n]T` (`Vector α n`) and a vector `@Vector(n, T)` (`Vec α n`) are their elements'
  bits concatenated, element 0 in the lowest bits (Zig 0.17's `Value.writeToPackedMemory`;
  `ZigLean/BitCast.lean`'s `ofLanes` for integer elements), at any nesting depth;
* a packed union (generated `structure U where bytes : Vector Byte size`) is the first `w` bits
  of its bytes (`PackedU.bitsOf`); bits that are undefined in the bytes are not determined
  (`PackedU.maskOf`).

`Packed.encodeOf o v` is the memory image of a value with undetermined bits: the bytes of its
backing integer at byte order `o`, each bit defined exactly where `mask` says (`Byte.ofDefBits`).
For a fully determined value it is the integer's encoding (`encodeOf_full`).
-/

namespace Zig

/-! ## Floats -/

instance {fmt : FloatFmt} : Packed (Float fmt) fmt.width where
  toBits x := x.bits
  ofBits b := ⟨b⟩
  mask := Float.detMask

/-! ## Arrays and vectors -/

/-- Element `i` of `n` elements of `w` bits each, packed element 0 lowest. -/
def lanesOf {w : Nat} (n : Nat) (x : BitVec (n * w)) : Vector (BitVec w) n := BitCast.toLanes x

instance {α : Type} {w n : Nat} [Packed α w] : Packed (Vector α n) (n * w) where
  toBits v := BitCast.ofLanes (v.map Packed.toBits)
  ofBits b := (lanesOf n b).map Packed.ofBits
  valid b := (lanesOf (w := w) n b).all (Packed.valid (α := α))
  mask v := BitCast.ofLanes (v.map Packed.mask)

instance {α : Type} {w n : Nat} [Packed α w] : Packed (Vec α n) (n * w) where
  toBits v := Packed.toBits v.lanes
  ofBits b := ⟨Packed.ofBits b⟩
  valid b := Packed.valid (α := Vector α n) b
  mask v := Packed.mask v.lanes

/-! ## Packed unions -/

/-- The first `w` bits of the bytes `bs`, little-endian; an undefined bit reads as 0. -/
def PackedU.bitsOf (w : Nat) (bs : Array Byte) : BitVec w :=
  (BitVec.ofBoolListLE ((List.range w).map fun j => (hostBit bs j).getD false)).cast (by simp)

/-- Which of the first `w` bits of `bs` are defined. -/
def PackedU.maskOf (w : Nat) (bs : Array Byte) : BitVec w :=
  (BitVec.ofBoolListLE ((List.range w).map fun j => (hostBit bs j).isSome)).cast (by simp)

/-! ## Memory images with undetermined bits -/

/-- The memory image of `v` at byte order `o`: its backing integer's `intSize n` bytes, each bit
defined where `Packed.mask` says, then undefined padding. -/
def Packed.encodeOf (o : ByteOrder) {α : Type} {n : Nat} [Packed α n] (v : α) : Array Byte :=
  padTo (intSize n) (o.arrange (Packed.bytes v))

/-! ## `@bitCast` through the bits -/

/-- `@bitCast` of `x` to `β` of the same bit size: its bits (`.unspecified` if one is
undetermined), then the `β` they make (`.illegal` if they are no `β`: an enum tag without a
name). -/
def Packed.bitCast (β : Type) {α : Type} {n m : Nat} [Packed α n] [Packed β m]
    (x : α) (h : n = m := by decide) : Result β := do
  Packed.ofBits? ((← Packed.toBits? x).cast h)

/-- The round trip of a logical `@bitCast`, under its representation condition: `x`'s bits are all
determined and make `x` again, and the bits of every `β` value are themselves (no padding, no
undetermined bits, every bit pattern valid: an integer, a packed struct of integers, an array of
these). An enum or a float on the `β` side breaks the condition (an unnamed tag is no value; a
NaN has no determined bits), and the round trip then need not hold. -/
theorem Packed.bitCast_roundtrip {α β : Type} {n : Nat} [Packed α n] [Packed β n] (x : α)
    (hmask : Packed.mask x = BitVec.allOnes n) (hvalid : Packed.valid (α := α) (Packed.toBits x))
    (hx : Packed.ofBits (Packed.toBits x) = x)
    (hβ : ∀ b : BitVec n, Packed.toBits (Packed.ofBits b : β) = b ∧
      Packed.mask (Packed.ofBits b : β) = BitVec.allOnes n ∧ Packed.valid (α := β) b) :
    (Packed.bitCast β x rfl >>= fun y => Packed.bitCast α y rfl) = pure x := by
  have h1 := hβ (Packed.toBits x)
  simp [Packed.bitCast, Packed.toBits?, Packed.defBits?, hmask, Packed.ofBits?, h1.1, h1.2.1,
    h1.2.2, hvalid, hx]

end Zig
