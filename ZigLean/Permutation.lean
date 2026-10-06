import ZigLean.Basic
import ZigLean.Vec

/-!
# Integer byte and bit permutations

Both operations act on the fixed-width representation, including signed integers.
The translator checks byte-aligned widths for `byteSwap`; zero width is valid.
Vectors use the same scalar operation independently on each lane.
-/
namespace Zig

/-- `@bitReverse`, with no sign extension or padding to an ABI storage width. -/
@[inline] def bitReverse {n : Nat} (a : BitVec n) : BitVec n := a.reverse

/-- The source bit for destination bit `i`: reverse bytes, keep bits within a byte. -/
def byteSwapIndex (n i : Nat) : Nat := (n / 8 - 1 - i / 8) * 8 + i % 8

/-- `@byteSwap`. The legal domain is `n % 8 = 0`, checked before emission. -/
def byteSwap {n : Nat} (a : BitVec n) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin n =>
    a.getLsbD (byteSwapIndex n i.val))).cast (by simp)

@[simp] theorem bitReverse_bit {n : Nat} (a : BitVec n) (i : Nat) :
    (bitReverse a).getLsbD i = a.getMsbD i := BitVec.getLsbD_reverse

@[simp] theorem bitReverse_involution {n : Nat} (a : BitVec n) :
    bitReverse (bitReverse a) = a := BitVec.reverse_reverse_eq

/-- Each output bit comes from the corresponding reversed byte, never from another lane. -/
theorem byteSwap_bit {n : Nat} (a : BitVec n) (i : Nat) (hi : i < n) :
    (byteSwap a).getLsbD i = a.getLsbD (byteSwapIndex n i) := by
  simp [byteSwap, List.getD_eq_getElem?_getD, hi]

theorem byteSwapIndex_lt {n i : Nat} (hn : n % 8 = 0) (hi : i < n) :
    byteSwapIndex n i < n := by
  unfold byteSwapIndex
  omega

theorem byteSwapIndex_involution {n i : Nat} (hn : n % 8 = 0) (hi : i < n) :
    byteSwapIndex n (byteSwapIndex n i) = i := by
  unfold byteSwapIndex
  omega

@[simp] theorem byteSwap_involution {n : Nat} (a : BitVec n) (hn : n % 8 = 0) :
    byteSwap (byteSwap a) = a := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  rw [byteSwap_bit _ _ hi, byteSwap_bit _ _ (byteSwapIndex_lt hn hi),
    byteSwapIndex_involution hn hi]

/-- The byte ordinal reverses while its bit ordinal stays fixed. -/
theorem byteSwap_byte_bit {n : Nat} (a : BitVec n) (b k : Nat)
    (hb : b < n / 8) (hk : k < 8) :
    (byteSwap a).getLsbD (8 * b + k) = a.getLsbD (8 * (n / 8 - 1 - b) + k) := by
  rw [byteSwap_bit _ _ (by omega)]
  congr 1
  unfold byteSwapIndex
  omega

@[simp] theorem byteSwap_zero : byteSwap (0 : BitVec 0) = 0 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  omega

/-- Applying the scalar permutation to a vector preserves its lane positions. -/
@[simp] theorem byteSwap_lane {n lanes : Nat} (v : Vec (BitVec n) lanes)
    (i : Nat) (hi : i < lanes) :
    (Vec.map byteSwap v).lanes[i] = byteSwap v.lanes[i] := by
  simp [Vec.map]

@[simp] theorem bitReverse_lane {n lanes : Nat} (v : Vec (BitVec n) lanes)
    (i : Nat) (hi : i < lanes) :
    (Vec.map bitReverse v).lanes[i] = bitReverse v.lanes[i] := by
  simp [Vec.map]

@[simp] theorem byteSwap_vector_involution {n lanes : Nat} (v : Vec (BitVec n) lanes)
    (hn : n % 8 = 0) : Vec.map byteSwap (Vec.map byteSwap v) = v := by
  cases v with
  | mk xs =>
    congr 1
    apply Vector.ext
    intro i hi
    simp [Vec.map, byteSwap_involution _ hn]

@[simp] theorem bitReverse_vector_involution {n lanes : Nat} (v : Vec (BitVec n) lanes) :
    Vec.map bitReverse (Vec.map bitReverse v) = v := by
  cases v with
  | mk xs =>
    congr 1
    apply Vector.ext
    intro i hi
    simp [Vec.map]

end Zig
