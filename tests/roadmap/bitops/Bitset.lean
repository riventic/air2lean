import ZigLean

/-! Production-style bitset client over the L02 semantics, after `std.bit_set`.

`IntegerBitSet(2^k)` stores its set in one `BitVec (2^k)` word indexed by the `Log2Int`
shift type `BitVec k`, so one proof covers u8, u16, u32, u64 and u128 words; the narrow,
64-bit and 128-bit instances are kernel-evaluated below. `ArrayBitSet` stores `N` u64 words
and indexes them with a bounded `Fin (64 * N)`. The operations use the same `Zig.shl`,
`Zig.popcount` and `Zig.ctz` definitions the emitter targets, and the generated
`firstSet`/`clearLowest`/`cardinality` fixtures are tied to these lemmas in
`GeneratedBitset.lean`. No `native_decide`, project axiom or proof placeholder is used. -/

namespace BitsetClient

/-- `maskBit(index)`: the single-bit mask of a valid index. -/
def maskBit {k : Nat} (i : BitVec k) : BitVec (2 ^ k) := Zig.shl (1 : BitVec (2 ^ k)) i
def isSet {k : Nat} (x : BitVec (2 ^ k)) (i : BitVec k) : Bool := (x &&& maskBit i) != 0
def set {k : Nat} (x : BitVec (2 ^ k)) (i : BitVec k) : BitVec (2 ^ k) := x ||| maskBit i
def unset {k : Nat} (x : BitVec (2 ^ k)) (i : BitVec k) : BitVec (2 ^ k) := x &&& ~~~maskBit i
def toggle {k : Nat} (x : BitVec (2 ^ k)) (i : BitVec k) : BitVec (2 ^ k) := x ^^^ maskBit i
/-- `count()`: `@popCount` into the checker's `log2(2^k) + 1 = k + 1` result width. -/
def count {k : Nat} (x : BitVec (2 ^ k)) : BitVec (k + 1) := Zig.popcount (k + 1) x
/-- `findFirstSet()`: `null` for the empty set, otherwise `@ctz`. -/
def findFirstSet {k : Nat} (x : BitVec (2 ^ k)) : Option (BitVec (k + 1)) :=
  if x = 0 then none else some (Zig.ctz (k + 1) x)
/-- The iteration step of `std.bit_set.Iterator`: remove the lowest set bit. -/
def clearLowest {n : Nat} (x : BitVec n) : BitVec n := x &&& Zig.subWrap x 1

theorem width_lt (k : Nat) : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_succ (by decide)

/-- Every `Log2Int` index addresses a bit inside the word. -/
theorem index_lt {k : Nat} (i : BitVec k) : i.toNat < 2 ^ k := i.isLt

theorem getLsbD_maskBit {k : Nat} (i : BitVec k) (j : Nat) :
    (maskBit i).getLsbD j = (j == i.toNat) := by
  have hi := index_lt i
  by_cases h : j = i.toNat
  · subst h; simp [maskBit, Zig.shl, hi]
  · simp only [maskBit, Zig.shl, BitVec.getLsbD_shiftLeft]
    rw [beq_false_of_ne h]
    by_cases hj : j < i.toNat
    · simp [hj]
    · have : j - i.toNat ≠ 0 := by omega
      simp [this]

/-- Index equality is bit-position equality. -/
theorem toNat_beq {k : Nat} (i j : BitVec k) : (j.toNat == i.toNat) = (i == j) := by
  by_cases h : i = j
  · subst h; simp
  · rw [beq_false_of_ne h, beq_false_of_ne (fun e => h (BitVec.eq_of_toNat_eq e.symm))]

theorem and_maskBit {k : Nat} (x : BitVec (2 ^ k)) (i : BitVec k) :
    x &&& maskBit i = if x.getLsbD i.toNat then maskBit i else 0 := by
  ext j hj
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  by_cases h : x.getLsbD i.toNat <;> by_cases hji : j = i.toNat <;>
    simp [getLsbD_maskBit, h, hji]

theorem maskBit_ne_zero {k : Nat} (i : BitVec k) : maskBit i ≠ 0 := by
  intro h
  have := getLsbD_maskBit i i.toNat
  simp [h] at this

/-- `isSet` reads exactly the indexed bit. -/
theorem isSet_eq {k : Nat} (x : BitVec (2 ^ k)) (i : BitVec k) :
    isSet x i = x.getLsbD i.toNat := by
  unfold isSet
  rw [and_maskBit]
  by_cases h : x.getLsbD i.toNat
  · simp only [h, ite_true, bne_iff_ne, ne_eq]
    exact maskBit_ne_zero i
  · simp [h]

theorem isSet_set {k : Nat} (x : BitVec (2 ^ k)) (i j : BitVec k) :
    isSet (set x i) j = (i == j || isSet x j) := by
  simp only [isSet_eq, set, BitVec.getLsbD_or, getLsbD_maskBit, toNat_beq, Bool.or_comm]

theorem isSet_unset {k : Nat} (x : BitVec (2 ^ k)) (i j : BitVec k) :
    isSet (unset x i) j = (i != j && isSet x j) := by
  simp only [isSet_eq, unset, BitVec.getLsbD_and, BitVec.getLsbD_not, getLsbD_maskBit, toNat_beq,
    index_lt j, decide_true, Bool.true_and, bne, Bool.and_comm]

theorem isSet_toggle {k : Nat} (x : BitVec (2 ^ k)) (i j : BitVec k) :
    isSet (toggle x i) j = (isSet x j ^^ (i == j)) := by
  simp only [isSet_eq, toggle, BitVec.getLsbD_xor, getLsbD_maskBit, toNat_beq]

@[simp] theorem isSet_empty {k : Nat} (i : BitVec k) : isSet (0 : BitVec (2 ^ k)) i = false := by
  simp [isSet_eq]

@[simp] theorem isSet_full {k : Nat} (i : BitVec k) :
    isSet (BitVec.allOnes (2 ^ k)) i = true := by
  simp [isSet_eq, index_lt i]

/-- The count is exact and bounded by the word width: no truncation in the `k + 1`-bit result. -/
theorem count_toNat {k : Nat} (x : BitVec (2 ^ k)) : (count x).toNat = x.cpop.toNat :=
  Zig.popcount_toNat_of_width x (width_lt k)

theorem count_le {k : Nat} (x : BitVec (2 ^ k)) : (count x).toNat ≤ 2 ^ k :=
  Zig.popcount_le (k + 1) x (width_lt k)

@[simp] theorem count_empty {k : Nat} : count (0 : BitVec (2 ^ k)) = 0 := Zig.popcount_zero _ _

@[simp] theorem count_full {k : Nat} :
    count (BitVec.allOnes (2 ^ k)) = BitVec.ofNat (k + 1) (2 ^ k) := Zig.popcount_allOnes _ _

@[simp] theorem findFirstSet_empty {k : Nat} : findFirstSet (0 : BitVec (2 ^ k)) = none := by
  simp [findFirstSet]

/-- A found index is the lowest member: it is set and no lower index is. -/
theorem findFirstSet_spec {k : Nat} (x : BitVec (2 ^ k)) (r : BitVec (k + 1))
    (h : findFirstSet x = some r) :
    r.toNat < 2 ^ k ∧ x.getLsbD r.toNat = true ∧ ∀ j < r.toNat, x.getLsbD j = false := by
  unfold findFirstSet at h
  by_cases hx : x = 0
  · simp [hx] at h
  · simp only [hx, ite_false, Option.some.injEq] at h
    subst h
    have hb : x.ctz.toNat < 2 ^ (k + 1) :=
      Nat.lt_of_le_of_lt (Zig.ctz_le_width x) (width_lt k)
    refine ⟨?_, Zig.getLsbD_at_ctz _ x hb hx, fun j hj => Zig.getLsbD_below_ctz _ x hb j hj⟩
    rw [Zig.ctz_toNat _ x hb]
    have := BitVec.lt_def.mp (BitVec.ctz_lt_iff_ne_zero.mpr hx)
    simpa [Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := 2 ^ k))] using this

/-- Iteration only removes members... -/
theorem clearLowest_subset {n : Nat} (x : BitVec n) (j : Nat) (h : (clearLowest x).getLsbD j = true) :
    x.getLsbD j = true := by
  simp only [clearLowest, BitVec.getLsbD_and, Bool.and_eq_true] at h
  exact h.1

/-- ...and strictly decreases the word, so the iterator's loop terminates. -/
theorem clearLowest_lt {n : Nat} (x : BitVec n) (hx : x ≠ 0) :
    (clearLowest x).toNat < x.toNat := Zig.and_subWrap_one_lt x hx

@[simp] theorem clearLowest_zero {n : Nat} : clearLowest (0 : BitVec n) = 0 := by
  simp [clearLowest]

/-! `ArrayBitSet(u64, 64 * N)`: index `i` lives in word `i / 64` at bit `i % 64`. -/

abbrev Words (N : Nat) := Vector (BitVec 64) N

theorem word_lt {N : Nat} (i : Fin (64 * N)) : i.val / 64 < N := by omega
def bitIndex {N : Nat} (i : Fin (64 * N)) : BitVec 6 := BitVec.ofNat 6 (i.val % 64)
def word {N : Nat} (w : Words N) (i : Fin (64 * N)) : BitVec 64 := w[i.val / 64]'(word_lt i)

def arrayIsSet {N : Nat} (w : Words N) (i : Fin (64 * N)) : Bool := isSet (word w i) (bitIndex i)
def arraySet {N : Nat} (w : Words N) (i : Fin (64 * N)) : Words N :=
  w.set (i.val / 64) (set (word w i) (bitIndex i)) (word_lt i)
def arrayUnset {N : Nat} (w : Words N) (i : Fin (64 * N)) : Words N :=
  w.set (i.val / 64) (unset (word w i) (bitIndex i)) (word_lt i)

theorem bitIndex_toNat {N : Nat} (i : Fin (64 * N)) : (bitIndex i).toNat = i.val % 64 := by
  simp [bitIndex, Nat.mod_eq_of_lt (Nat.mod_lt i.val (by decide : 64 > 0))]

/-- Two indices that share a word and a bit are equal. -/
theorem index_ext {N : Nat} (i j : Fin (64 * N)) (hw : i.val / 64 = j.val / 64)
    (hb : bitIndex i = bitIndex j) : i = j := by
  have hb' : i.val % 64 = j.val % 64 := by
    rw [← bitIndex_toNat, ← bitIndex_toNat, hb]
  apply Fin.ext
  rw [← Nat.div_add_mod i.val 64, ← Nat.div_add_mod j.val 64, hw, hb']

theorem word_update {N : Nat} (w : Words N) (i j : Fin (64 * N)) (x : BitVec 64) :
    word (w.set (i.val / 64) x (word_lt i)) j = if i.val / 64 = j.val / 64 then x else word w j := by
  simp [word, Vector.getElem_set]

theorem arrayIsSet_set {N : Nat} (w : Words N) (i j : Fin (64 * N)) :
    arrayIsSet (arraySet w i) j = (i == j || arrayIsSet w j) := by
  unfold arrayIsSet arraySet
  rw [word_update]
  split
  · next hw =>
    have hww : word w i = word w j := by simp [word, hw]
    rw [isSet_set, hww]
    by_cases hb : bitIndex i = bitIndex j
    · simp [index_ext i j hw hb]
    · have : i ≠ j := fun e => hb (e ▸ rfl)
      simp only [beq_false_of_ne hb, beq_false_of_ne this]
  · next hw =>
    have : i ≠ j := fun e => hw (e ▸ rfl)
    simp [this]

theorem arrayIsSet_unset {N : Nat} (w : Words N) (i j : Fin (64 * N)) :
    arrayIsSet (arrayUnset w i) j = (i != j && arrayIsSet w j) := by
  unfold arrayIsSet arrayUnset
  rw [word_update]
  split
  · next hw =>
    have hww : word w i = word w j := by simp [word, hw]
    rw [isSet_unset, hww]
    by_cases hb : bitIndex i = bitIndex j
    · simp [index_ext i j hw hb]
    · have : i ≠ j := fun e => hb (e ▸ rfl)
      simp only [bne, beq_false_of_ne hb, beq_false_of_ne this]
  · next hw =>
    have : i ≠ j := fun e => hw (e ▸ rfl)
    simp [this]

/-! Kernel-evaluated instances: u8 (k = 3), u64 (k = 6), u128 (k = 7) and a two-word array. -/

example : isSet (set (0 : BitVec (2 ^ 3)) (7 : BitVec 3)) 7 = true ∧ count (set (0 : BitVec (2 ^ 3)) (7 : BitVec 3)) = 1 := by decide
example : findFirstSet (128 : BitVec (2 ^ 3)) = some 7 ∧ findFirstSet (0 : BitVec (2 ^ 3)) = none := by decide
set_option maxRecDepth 20000 in
example : isSet (set (0 : BitVec (2 ^ 6)) (63 : BitVec 6)) 63 = true ∧
    unset (BitVec.allOnes (2 ^ 6)) (63 : BitVec 6) = 9223372036854775807 ∧
    count (BitVec.allOnes (2 ^ 6)) = 64 ∧ findFirstSet (9223372036854775808 : BitVec (2 ^ 6)) = some 63 ∧
    clearLowest (9223372036854775809 : BitVec (2 ^ 6)) = 9223372036854775808 := by decide
set_option maxRecDepth 20000 in
example : set (0 : BitVec (2 ^ 7)) (127 : BitVec 7) = 170141183460469231731687303715884105728 ∧
    count (BitVec.allOnes (2 ^ 7)) = 128 ∧ toggle (BitVec.allOnes (2 ^ 7)) (0 : BitVec 7) = -2 ∧
    findFirstSet (170141183460469231731687303715884105728 : BitVec (2 ^ 7)) = some 127 := by decide
example : arrayIsSet (arraySet (#v[0, 0] : Words 2) ⟨127, by decide⟩) ⟨127, by decide⟩ = true ∧
    arrayIsSet (arraySet (#v[0, 0] : Words 2) ⟨127, by decide⟩) ⟨63, by decide⟩ = false ∧
    (arraySet (#v[0, 0] : Words 2) ⟨64, by decide⟩)[1] = 1 := by decide

end BitsetClient
