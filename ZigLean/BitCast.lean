import ZigLean.Mem.Enc
import ZigLean.Vec

/-!
# `@bitCast` in logical bit order (Zig 0.17.0)

Zig 0.17.0 defines `@bitCast` on the *logical* bit representation, independent of the target
endianness (`docs/bitcast-semantics.md`): an integer is its two's-complement bits, a `bool` is
one bit, a packed struct is its backing integer, and an array or vector is its elements
concatenated in order, element 0 in the lowest bits, each element taking exactly its
`@bitSizeOf` bits (no ABI padding). `Emit.lean` lowers a 0.17 bit-cast that involves an array or
vector as "source to its bits, then bits to the destination" with the functions here.

* `ofLanes`/`toLanes`: integer lanes (`[n]uW`, `@Vector(n, iW)`, …) ↔ `BitVec (n * W)`.
* `ofBools`/`toBools`: `bool` lanes ↔ `BitVec n`.

The lemmas show the round trips, and that for lanes whose bit size fills their ABI size (8, 16,
32, 64, 128, … bits) the little-endian memory bytes of the lanes (`Zig.Enc`, Zig 0.16's
memory-reinterpretation `@bitCast`) are exactly the bytes of the logical integer: on the
modelled (little-endian) targets the two definitions agree there, so a proof about a ≤0.16
translation through memory stays a proof about the 0.17 translation. A `bool` vector's memory
encoding is already its logical bits (`toBools` is its decoder).
-/

namespace Zig.BitCast

/-! ## Natural-number form -/

/-- The lanes `xs` (each `< 2 ^ w`) concatenated, lane 0 in the lowest `w` bits. -/
def packNat (w : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + 2 ^ w * packNat w xs

/-- The first `k` little-endian bytes of `x`. -/
def bytesNat : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, x => x % 256 :: bytesNat k (x / 256)

theorem packNat_lt (w : Nat) (xs : List Nat) (h : ∀ x ∈ xs, x < 2 ^ w) :
    packNat w xs < 2 ^ (xs.length * w) := by
  induction xs with
  | nil => simp [packNat]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hp := ih (fun y hy => h y (by simp [hy]))
    have hpow : 2 ^ ((xs.length + 1) * w) = 2 ^ w * 2 ^ (xs.length * w) := by
      rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm]
    simp only [packNat, List.length_cons, hpow]
    calc x + 2 ^ w * packNat w xs < 2 ^ w + 2 ^ w * packNat w xs := by omega
      _ = 2 ^ w * (packNat w xs + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ 2 ^ w * 2 ^ (xs.length * w) := Nat.mul_le_mul_left _ hp

/-- Lane `i` of the packed lanes. -/
theorem packNat_lane (w : Nat) (xs : List Nat) (h : ∀ x ∈ xs, x < 2 ^ w) (i : Nat)
    (hi : i < xs.length) : packNat w xs / 2 ^ (w * i) % 2 ^ w = xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx := h x (by simp)
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    cases i with
    | zero =>
      simp only [packNat, Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ i =>
      simp only [packNat, List.getElem_cons_succ]
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * i)) (2 ^ w), ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hx, Nat.zero_add]
      exact ih (fun y hy => h y (by simp [hy])) i (by simp at hi; omega)

/-- Splitting `x` into `n` lanes of `w` bits and packing them again gives `x` back. -/
theorem packNat_ofFn (w n x : Nat) (hx : x < 2 ^ (n * w)) :
    packNat w (List.ofFn fun i : Fin n => x / 2 ^ (w * i.val) % 2 ^ w) = x := by
  induction n generalizing x with
  | zero => simp at hx; simp [packNat, hx]
  | succ n ih =>
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    have hlt : x / 2 ^ w < 2 ^ (n * w) := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add]
      rwa [Nat.succ_mul] at hx
    rw [List.ofFn_succ]
    simp only [packNat, Fin.val_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Fin.val_succ]
    have hshift : ∀ i : Fin n, x / 2 ^ (w * (i.val + 1)) % 2 ^ w =
        x / 2 ^ w / 2 ^ (w * i.val) % 2 ^ w := by
      intro i
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ, Nat.add_comm (w * i.val) w]
    simp only [hshift]
    rw [ih (x / 2 ^ w) hlt, Nat.mod_add_div]

theorem bytesNat_length (k x : Nat) : (bytesNat k x).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [bytesNat, ih]

theorem bytesNat_getElem (k x i : Nat) (h : i < (bytesNat k x).length) :
    (bytesNat k x)[i] = x / 256 ^ i % 256 := by
  induction k generalizing x i with
  | zero => simp [bytesNat] at h
  | succ k ih =>
    cases i with
    | zero => simp [bytesNat]
    | succ i =>
      simp only [bytesNat, List.getElem_cons_succ]
      rw [ih, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ i) 256]

/-- The bytes of `a + 256 ^ k * b` (`a < 256 ^ k`): the `k` bytes of `a`, then those of `b`. -/
theorem bytesNat_append (k m a b : Nat) (ha : a < 256 ^ k) :
    bytesNat (k + m) (a + 256 ^ k * b) = bytesNat k a ++ bytesNat m b := by
  induction k generalizing a with
  | zero => simp at ha; subst ha; simp [bytesNat]
  | succ k ih =>
    have hdiv : a / 256 < 256 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; rwa [Nat.pow_succ] at ha
    rw [Nat.add_right_comm, bytesNat, bytesNat, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256,
      Nat.mul_assoc, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by decide), ih _ hdiv]
    rfl

/-- Packing lanes of whole bytes (`w = 8 * k`) concatenates their little-endian bytes. -/
theorem bytesNat_packNat (k : Nat) (xs : List Nat) (h : ∀ x ∈ xs, x < 2 ^ (8 * k)) :
    bytesNat (xs.length * k) (packNat (8 * k) xs) = (xs.map (bytesNat k)).flatten := by
  induction xs with
  | nil => simp [packNat, bytesNat]
  | cons x xs ih =>
    have hx := h x (by simp)
    have h256 : (2 : Nat) ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]
    rw [h256] at hx
    simp only [List.length_cons, packNat, List.map_cons, List.flatten_cons]
    rw [Nat.succ_mul, Nat.add_comm, h256, bytesNat_append _ _ _ _ hx]
    have ih' := ih (fun y hy => h y (by simp [hy]))
    rw [ih']

/-! ## Integer lanes -/

/-- An array or vector of `n` integer lanes of `w` bits as one `n * w`-bit integer: lane 0 in
the lowest bits (Zig 0.17 `@bitCast` from `[n]uW`/`@Vector(n, uW)`, also signed lanes). -/
def ofLanes {w n : Nat} (v : Vector (BitVec w) n) : BitVec (n * w) :=
  BitVec.ofNat (n * w) (packNat w (v.toList.map BitVec.toNat))

/-- An `n * w`-bit integer as `n` lanes of `w` bits, lane 0 from the lowest bits (Zig 0.17
`@bitCast` to `[n]uW`/`@Vector(n, uW)`). -/
def toLanes {w n : Nat} (x : BitVec (n * w)) : Vector (BitVec w) n :=
  Vector.ofFn fun i => BitVec.ofNat w (x.toNat / 2 ^ (w * i.val))

private theorem lanes_lt {w n : Nat} (v : Vector (BitVec w) n) :
    ∀ x ∈ v.toList.map BitVec.toNat, x < 2 ^ w := by
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  exact b.isLt

theorem toNat_ofLanes {w n : Nat} (v : Vector (BitVec w) n) :
    (ofLanes v).toNat = packNat w (v.toList.map BitVec.toNat) := by
  have hlt := packNat_lt w _ (lanes_lt v)
  simp only [List.length_map, Vector.length_toList] at hlt
  simp [ofLanes, Nat.mod_eq_of_lt hlt]

/-- Bit `w * i + j` of the integer is bit `j` of lane `i`. -/
theorem getLsbD_ofLanes {w n : Nat} (v : Vector (BitVec w) n) (i j : Nat) (hi : i < n)
    (hj : j < w) : (ofLanes v).getLsbD (w * i + j) = v[i].getLsbD j := by
  have hlane := packNat_lane w _ (lanes_lt v) i (by simp [hi])
  simp only [List.getElem_map, Vector.getElem_toList] at hlane
  rw [BitVec.getLsbD, toNat_ofLanes, BitVec.getLsbD, ← hlane, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  simp [hj, Nat.add_comm j]

@[simp] theorem toLanes_ofLanes {w n : Nat} (v : Vector (BitVec w) n) : toLanes (ofLanes v) = v := by
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_toNat_eq
  have hlane := packNat_lane w _ (lanes_lt v) i (by simp [hi])
  simp only [List.getElem_map, Vector.getElem_toList] at hlane
  simp [toLanes, toNat_ofLanes, hlane]

@[simp] theorem ofLanes_toLanes {w n : Nat} (x : BitVec (n * w)) : ofLanes (toLanes x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofLanes]
  have : (toLanes x).toList.map BitVec.toNat =
      List.ofFn fun i : Fin n => x.toNat / 2 ^ (w * i.val) % 2 ^ w := by
    simp [toLanes, Vector.toList_ofFn, List.map_ofFn, Function.comp_def]
  rw [this, packNat_ofFn w n _ x.isLt]

/-! ## `bool` lanes -/

/-- `n` `bool` lanes as an `n`-bit integer: lane `i` is bit `i` (`[n]bool`, `@Vector(n, bool)`). -/
def ofBools {n : Nat} (v : Vector Bool n) : BitVec n :=
  (BitVec.ofBoolListLE v.toList).cast (by simp)

/-- An `n`-bit integer as `n` `bool` lanes: lane `i` is bit `i`. -/
def toBools {n : Nat} (x : BitVec n) : Vector Bool n := Vector.ofFn fun i => x.getLsbD i.val

theorem getLsbD_ofBools {n : Nat} (v : Vector Bool n) (i : Nat) (hi : i < n) :
    (ofBools v).getLsbD i = v[i] := by
  unfold ofBools
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [hi]

@[simp] theorem toBools_ofBools {n : Nat} (v : Vector Bool n) : toBools (ofBools v) = v := by
  apply Vector.ext
  intro i hi
  rw [toBools, Vector.getElem_ofFn]
  exact getLsbD_ofBools v i hi

@[simp] theorem ofBools_toBools {n : Nat} (x : BitVec n) : ofBools (toBools x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBools _ i hi, toBools, Vector.getElem_ofFn]

/-- The model's memory decoder of `@Vector(n, bool)` (its in-memory form is the `uN` of its
lanes, `Vec.packedEnc` with 1-bit lanes) reads that integer and takes lane `i` from bit `i`: the
bool-vector layout already is the logical order. -/
theorem decode_boolVec {n : Nat} (bs : Array Byte) :
    (Enc.decode bs : Result (Vec Bool n)) =
      (do let x ← intOfBytes (n * 1) bs; pure ⟨Vector.ofFn fun i => laneOf 1 x.toNat i == 1#1⟩) := rfl

/-- A 1-bit lane of an integer is that integer's bit (`toBools`' reading). -/
theorem laneOf_one_eq_getLsbD {m : Nat} (x : BitVec m) (i : Nat) :
    (laneOf 1 x.toNat i == 1#1) = x.getLsbD i := by
  unfold laneOf
  rw [BitVec.getLsbD, Nat.mul_one]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat >>> i) with h | h <;>
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, BitVec.ofNat, Fin.ofNat] at h ⊢ <;>
    simp [h] <;> omega

/-- The memory decoder of `@Vector(n, bool)` gives lane `i` the bit `i` of the `uN` it reads, as
`toBools` does: the in-memory order is the bitcast's logical order. -/
theorem decode_boolVec_bits {n : Nat} (bs : Array Byte) :
    (Enc.decode bs : Result (Vec Bool n)) =
      (do let x ← intOfBytes (n * 1) bs; pure ⟨Vector.ofFn fun i => x.getLsbD i.val⟩) := by
  rw [decode_boolVec]
  simp only [laneOf_one_eq_getLsbD]

/-! ## Agreement with the memory encoding (Zig ≤0.16 `@bitCast` through memory) -/

/-- The bytes of a whole-byte integer: each `.int`, little-endian. -/
theorem intBytes_eq_bytesNat {m : Nat} (x : BitVec m) (hm : m % 8 = 0) :
    intBytes x = ((bytesNat (m / 8) x.toNat).map fun b => Byte.int (BitVec.ofNat 8 b)).toArray := by
  apply Array.ext
  · simp [intBytes, bytesNat_length]; omega
  · intro i h₁ h₂
    simp only [intBytes, Array.size_map, Array.size_range] at h₁
    simp only [intBytes, Array.getElem_map, Array.getElem_range, List.getElem_toArray,
      List.getElem_map]
    have hge : ¬ (m - 8 * i < 8) := by omega
    simp only [hge, ↓reduceIte]
    rw [bytesNat_getElem, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- An integer whose bit size fills its ABI size is encoded without padding. -/
theorem encode_bitVec_noPad {w : Nat} (x : BitVec w) (hw : w % 8 = 0) (hsize : intSize w = w / 8) :
    (Enc.encode x : Array Byte) = intBytes x := by
  show padTo (intSize w) (intBytes x) = intBytes x
  have : (intBytes x).size = w / 8 := by simp [intBytes]; omega
  simp [padTo, this, hsize]

/-- **Agreement.** For lanes of `8 * k` bits that fill their ABI size (no padding: 8, 16, 32,
64, 128, … bits), the memory bytes of `[n]uW` are exactly the little-endian bytes of the 0.17
logical integer `ofLanes v`. Zig ≤0.16's `@bitCast` (store the array, load the integer) and Zig
0.17's logical-order `@bitCast` therefore give the same bits on little-endian targets. -/
theorem encode_array_eq_intBytes_ofLanes (k n : Nat) (hsize : intSize (8 * k) = k)
    (v : Vector (BitVec (8 * k)) n) :
    (Enc.encode v : Array Byte) = intBytes (ofLanes v) := by
  have hm : n * (8 * k) % 8 = 0 := by
    rw [Nat.mul_left_comm]; exact Nat.mul_mod_right 8 _
  have hdiv : n * (8 * k) / 8 = n * k := by
    rw [Nat.mul_left_comm]; exact Nat.mul_div_cancel_left _ (by decide)
  rw [intBytes_eq_bytesNat _ hm, hdiv, toNat_ofLanes]
  have hbytes := bytesNat_packNat k (v.toList.map BitVec.toNat) (lanes_lt v)
  simp only [List.length_map, Vector.length_toList] at hbytes
  rw [hbytes]
  show (v.toArray.map Enc.encode).flatten = _
  have henc : ∀ x : BitVec (8 * k), (Enc.encode x : Array Byte) =
      ((bytesNat k x.toNat).map fun b => Byte.int (BitVec.ofNat 8 b)).toArray := by
    intro x
    rw [encode_bitVec_noPad x (Nat.mul_mod_right 8 k) (by rw [hsize]; omega),
      intBytes_eq_bytesNat x (Nat.mul_mod_right 8 k), Nat.mul_div_cancel_left _ (by decide)]
  apply Array.toList_inj.mp
  simp [henc, List.map_flatten, Function.comp_def, Vector.toList_toArray]

/-- `ZigLean/Vec.lean`'s lane packing is `packNat` of the lanes' values. -/
theorem packLanes_eq_packNat {w : Nat} (xs : List (BitVec w)) :
    packLanes xs = packNat w (xs.map BitVec.toNat) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [packLanes, packNat, ih]

/-- The same for a vector `@Vector(n, uW)` whose lanes fill the power-of-2 vector size: its
bit-packed memory image (`Vec.packedEnc`) is the bytes of the 0.17 integer. -/
theorem encode_vec_eq_intBytes_ofLanes (k n : Nat) (_hsize : intSize (8 * k) = k)
    (hvec : vecLayout n k = n * k) (v : Vector (BitVec (8 * k)) n) :
    (Enc.encode (⟨v⟩ : Vec (BitVec (8 * k)) n) : Array Byte) = intBytes (ofLanes v) := by
  have hpack : Vec.packBits (8 * k) id (⟨v⟩ : Vec (BitVec (8 * k)) n) = ofLanes v := by
    simp [Vec.packBits, ofLanes, packLanes_eq_packNat]
  show padTo (packedVecLayout n (8 * k)) (intBytes (Vec.packBits (8 * k) id ⟨v⟩)) = _
  rw [hpack]
  have h8 : n * (8 * k) = 8 * (n * k) := Nat.mul_left_comm n 8 k
  have hlay : packedVecLayout n (8 * k) = n * k := by
    rw [packedVecLayout, show (n * (8 * k) + 7) / 8 = n * k by omega]; exact hvec
  have hlen : (intBytes (ofLanes v)).size = n * k := by
    simp [intBytes]; omega
  simp [padTo, hlay, hlen]

/-- The 0.17 integer has the same memory bytes as the array when it has no padding of its own. -/
theorem encode_ofLanes_eq_encode_array (k n : Nat) (hsize : intSize (8 * k) = k)
    (hint : intSize (n * (8 * k)) = n * k) (v : Vector (BitVec (8 * k)) n) :
    (Enc.encode (ofLanes v) : Array Byte) = Enc.encode v := by
  have hm : n * (8 * k) % 8 = 0 := by
    rw [Nat.mul_left_comm]; exact Nat.mul_mod_right 8 _
  have hdiv : n * (8 * k) / 8 = n * k := by
    rw [Nat.mul_left_comm]; exact Nat.mul_div_cancel_left _ (by decide)
  rw [encode_bitVec_noPad _ hm (by rw [hint, hdiv]), encode_array_eq_intBytes_ofLanes k n hsize v]

end Zig.BitCast
