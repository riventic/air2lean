import ZigLean.Basic

/-!
# Reader/writer state and resources

The state word has a reader count in bits 32 through 62, a pending-writer count
in bits 1 through 31, and a writing bit at bit 0. These are logical counts used
by the full-state protocol; operations on the word are the existing native Word
operations. The protocol must relate the counts to its actual admitted handles.
-/

namespace Zig.Full

namespace RwState

/-- One reader in the native 64-bit state word. -/
def readerUnit : Nat := 4294967296

/-- The number of representable readers and pending writers. -/
def countBound : Nat := 2147483648

/-- The encoding of the two counts and the writing bit. -/
def encode (readers writers : Nat) (writing : Bool) : BitVec 64 :=
  BitVec.ofNat 64 (readers * readerUnit + 2 * writers + if writing then 1 else 0)

/-- The count selected by the native reader mask. -/
def readers (s : BitVec 64) : Nat := s.toNat / readerUnit % countBound

/-- The pending-writer count in the low word. -/
def writers (s : BitVec 64) : Nat := s.toNat % readerUnit / 2

/-- Whether the native writing bit is set. -/
def writing (s : BitVec 64) : Bool := s.toNat % 2 == 1

/-- Valid count encodings do not wrap the 64-bit word. -/
theorem encode_toNat {r w : Nat} (hr : r < countBound) (hw : w < countBound)
    (a : Bool) :
    (encode r w a).toNat = r * readerUnit + 2 * w + if a then 1 else 0 := by
  cases a <;> simp only [encode, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
  all_goals
    apply Nat.mod_eq_of_lt
    simp only [countBound] at hr hw
    simp only [readerUnit]
    omega

/-- The native reader mask recovers the represented reader count. -/
theorem readers_encode {r w : Nat} (hr : r < countBound) (hw : w < countBound)
    (a : Bool) : readers (encode r w a) = r := by
  unfold readers
  rw [encode_toNat hr hw]
  have hlow : 2 * w + (if a then 1 else 0) < readerUnit := by
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, readerUnit, countBound] at * <;>
      omega
  have hdiv : (r * readerUnit + 2 * w + (if a then 1 else 0)) / readerUnit = r := by
    simp only [readerUnit] at *
    omega
  rw [hdiv, Nat.mod_eq_of_lt hr]

/-- The low word recovers the represented pending-writer count. -/
theorem writers_encode {r w : Nat} (hr : r < countBound) (hw : w < countBound)
    (a : Bool) : writers (encode r w a) = w := by
  unfold writers
  rw [encode_toNat hr hw]
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, readerUnit, countBound] at * <;>
    omega

/-- The represented writing bit is the native low bit. -/
theorem writing_encode {r w : Nat} (hr : r < countBound) (hw : w < countBound)
    (a : Bool) : writing (encode r w a) = a := by
  cases a <;>
    simp [writing, encode_toNat hr hw, readerUnit, Nat.add_mod, Nat.mul_mod]

/-- The state-value effect of adding a reader is exact, including modular values.
The protocol separately proves representability of the new logical count. -/
theorem add_reader (r w : Nat) (a : Bool) :
    encode r w a + 4294967296 = encode (r + 1) w a := by
  change BitVec.ofNat 64 (r * readerUnit + 2 * w + if a then 1 else 0) +
      BitVec.ofNat 64 readerUnit = _
  rw [← BitVec.ofNat_add]
  exact congrArg (BitVec.ofNat 64) (by simp only [readerUnit]; omega)

/-- A reader's returned handle removes exactly its reader unit. -/
theorem sub_reader (r w : Nat) (a : Bool) :
    encode (r + 1) w a - 4294967296 = encode r w a := by
  rw [← add_reader]
  exact BitVec.add_sub_cancel _ _

/-- Registering a writer adds two in the low word. -/
theorem add_writer (r w : Nat) (a : Bool) :
    encode r w a + 2 = encode r (w + 1) a := by
  change BitVec.ofNat 64 (r * readerUnit + 2 * w + if a then 1 else 0) +
      BitVec.ofNat 64 2 = _
  rw [← BitVec.ofNat_add]
  exact congrArg (BitVec.ofNat 64) (by omega)

/-- The outer holder consumes its pending-writer unit and sets the writing bit. -/
theorem enter_writer (r w : Nat) :
    encode r (w + 1) false + 18446744073709551615 = encode r w true := by
  have he : encode r (w + 1) false = encode r w true + 1 := by
    change BitVec.ofNat 64 (r * readerUnit + 2 * (w + 1) + 0) =
      BitVec.ofNat 64 (r * readerUnit + 2 * w + 1) + BitVec.ofNat 64 1
    rw [← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  rw [he, BitVec.add_assoc]
  simp

/-- The real low-word mask is the low-word remainder. -/
theorem low_mask (s : BitVec 64) :
    (s &&& 4294967295).toNat = s.toNat % readerUnit := by
  rw [BitVec.toNat_and]
  change s.toNat &&& (2 ^ 32 - 1) = s.toNat % (2 ^ 32)
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- A represented low word consists of the pending writers and writing bit. -/
theorem low_encode {r w : Nat} (hr : r < countBound) (hw : w < countBound)
    (a : Bool) :
    (encode r w a &&& 4294967295).toNat = 2 * w + if a then 1 else 0 := by
  rw [low_mask, encode_toNat hr hw]
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, readerUnit, countBound] at * <;>
    omega

/-- The native fast-path guard excludes both a queued writer and a writing holder. -/
theorem read_guard {r w : Nat} (hr : r < countBound) (hw : w < countBound)
    (a : Bool) :
    (encode r w a &&& 4294967295 = 0) ↔ w = 0 ∧ a = false := by
  rw [← BitVec.toNat_inj, low_encode hr hw]
  cases a <;> simp <;> omega

/-- The native reader mask selects exactly the decoder's count, in reader units. -/
theorem reader_mask (s : BitVec 64) :
    (s &&& 9223372032559808512).toNat = readers s * readerUnit := by
  rw [BitVec.toNat_and]
  change s.toNat &&& 9223372032559808512 = readers s * readerUnit
  have hd : (s.toNat &&& 9223372032559808512) / readerUnit = readers s := by
    change (s.toNat &&& 9223372032559808512) / 2 ^ 32 =
      s.toNat / 2 ^ 32 % 2 ^ 31
    rw [Nat.and_div_two_pow]
    change s.toNat / 2 ^ 32 &&& (2 ^ 31 - 1) = _
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have hm : (s.toNat &&& 9223372032559808512) % readerUnit = 0 := by
    change (s.toNat &&& 9223372032559808512) % 2 ^ 32 = 0
    rw [Nat.and_mod_two_pow]
    change s.toNat % 2 ^ 32 &&& 0 = 0
    exact Nat.and_zero _
  have he := Nat.mod_add_div (s.toNat &&& 9223372032559808512) readerUnit
  rw [hd, hm, Nat.zero_add, Nat.mul_comm] at he
  exact he.symm

/-- The old-value reader guard identifies the last represented reader. -/
theorem last_reader_guard {r w : Nat} (hr : r < countBound) (hw : w < countBound)
    (a : Bool) :
    (encode r w a &&& 9223372032559808512 = 4294967296) ↔ r = 1 := by
  rw [← BitVec.toNat_inj, reader_mask, readers_encode hr hw]
  change r * readerUnit = readerUnit ↔ r = 1
  simp only [readerUnit]
  omega

/-- Clearing the writing bit leaves the represented counts unchanged. -/
theorem clear_writer {r w : Nat} (hr : r < countBound) (hw : w < countBound) :
    encode r w true &&& 18446744073709551614 = encode r w false := by
  have hzero : encode r w false &&& 1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, encode_toNat hr hw]
    simp [readerUnit, Nat.add_mod, Nat.mul_mod]
  have hp : encode r w true = encode r w false ||| 1 := by
    calc
      encode r w true = encode r w false + 1 := by
        change BitVec.ofNat 64 (r * readerUnit + 2 * w + 1) =
          BitVec.ofNat 64 (r * readerUnit + 2 * w + 0) + BitVec.ofNat 64 1
        rw [← BitVec.ofNat_add]
      _ = encode r w false ||| 1 := BitVec.add_eq_or_of_and_eq_zero _ _ hzero
  have hkeep : encode r w false &&& ~~~(1 : BitVec 64) = encode r w false := by
    have hsplit : (encode r w false &&& 1) |||
        (encode r w false &&& ~~~(1 : BitVec 64)) = encode r w false := by
      rw [← BitVec.and_or_distrib_left, BitVec.or_not_self, BitVec.and_allOnes]
    rw [hzero] at hsplit
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.zero_or] using hsplit
  change encode r w true &&& ~~~(1 : BitVec 64) = encode r w false
  rw [hp, BitVec.and_or_distrib_right, hkeep, BitVec.and_not_self]
  simp

end RwState

end Zig.Full
