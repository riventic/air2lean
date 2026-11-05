import ZigLean.Range

/-!
# Reader/writer state-value algebra

One count-width family supplies the encoding, masks and native value equations.
The current ABI64 std instance uses reader bits32..62, pending-writer bits1..31
and writing bit0; bit63 is spare, but out-of-range encodings can set it. The
protocol must relate represented counts to its actual admitted handles.
-/

namespace Zig.Full

namespace RwState

/-! The value algebra is parameterized by a count width and spare high bits.
The std layouts are `(31, 1)` on ABI64 and `(15, 1)` on ABI32; this does not
extend the atomic/thread runtime model to a new target. -/
namespace Family

abbrev width (c p : Nat) : Nat := 2 * c + 1 + p
abbrev readerUnit (c : Nat) : Nat := 2 ^ (c + 1)
abbrev countBound (c : Nat) : Nat := 2 ^ c

def raw (c r w : Nat) (a : Bool) : Nat :=
  r * readerUnit c + 2 * w + if a then 1 else 0

def encode (c p r w : Nat) (a : Bool) : BitVec (width c p) := .ofNat _ (raw c r w a)
def readers (c : Nat) (s : BitVec n) : Nat := s.toNat / readerUnit c % countBound c
def writers (c : Nat) (s : BitVec n) : Nat := s.toNat % readerUnit c / 2
def writing (s : BitVec n) : Bool := s.toNat % 2 == 1

def lowMask (c p : Nat) : BitVec (width c p) := .ofNat _ (readerUnit c - 1)
def readerMask (c p : Nat) : BitVec (width c p) := .ofNat _ (2 ^ (2 * c + 1) - readerUnit c)
def clearWriting (c p : Nat) : BitVec (width c p) := .ofNat _ (2 ^ width c p - 2)

/-- The encoding is modular even when either logical count is out of range. -/
theorem encode_toNat' (c p r w : Nat) (a : Bool) :
    (encode c p r w a).toNat = raw c r w a % 2 ^ width c p := rfl

theorem low_lt {c w : Nat} (hw : w < countBound c) (a : Bool) :
    2 * w + (if a then 1 else 0) < readerUnit c := by
  cases a <;> simp only [readerUnit, countBound, Nat.pow_succ,
    Bool.false_eq_true, ↓reduceIte] at * <;> omega

theorem raw_lt {c p r w : Nat} (hr : r < countBound c) (hw : w < countBound c)
    (a : Bool) : raw c r w a < 2 ^ width c p := by
  calc
    raw c r w a = r * readerUnit c + (2 * w + if a then 1 else 0) := by
      unfold raw; omega
    _ < (r + 1) * readerUnit c := by
      simpa only [Nat.add_mul, Nat.one_mul] using Nat.add_lt_add_left (low_lt hw a) (r * readerUnit c)
    _ ≤ countBound c * readerUnit c := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hr)
    _ = 2 ^ (2 * c + 1) := by
      simp only [countBound, readerUnit, ← Nat.pow_add]
      congr 1; omega
    _ ≤ 2 ^ width c p := Nat.pow_le_pow_right (by decide) (by unfold width; omega)

theorem encode_toNat {c p r w : Nat} (hr : r < countBound c) (hw : w < countBound c)
    (a : Bool) : (encode c p r w a).toNat = raw c r w a :=
  Zig.toNat_ofNat_of_lt (raw_lt hr hw a)

theorem low_mod (c p r w : Nat) (a : Bool) :
    (encode c p r w a).toNat % readerUnit c =
      (2 * w + if a then 1 else 0) % readerUnit c := by
  rw [encode_toNat', Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by unfold width; omega))]
  simp [raw, readerUnit, Nat.add_mod, Nat.mul_mod]

theorem readers_encode {c p r w : Nat} (hr : r < countBound c) (hw : w < countBound c)
    (a : Bool) : readers c (encode c p r w a) = r := by
  unfold readers
  rw [encode_toNat hr hw]
  have hu := Nat.two_pow_pos (c + 1)
  have hd : raw c r w a / readerUnit c = r := by
    unfold raw
    rw [Nat.add_assoc, Nat.add_comm (r * readerUnit c), Nat.add_mul_div_right _ _ hu,
      Nat.div_eq_of_lt (low_lt hw a), Nat.zero_add]
  rw [hd, Nat.mod_eq_of_lt hr]

theorem writers_encode {c p r w : Nat} (hw : w < countBound c) (a : Bool) :
    writers c (encode c p r w a) = w := by
  unfold writers
  rw [low_mod, Nat.mod_eq_of_lt (low_lt hw a)]
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem writing_encode (c p r w : Nat) (a : Bool) : writing (encode c p r w a) = a := by
  have hd : 2 ∣ 2 ^ width c p := by
    exact Nat.pow_dvd_pow 2 (show 1 ≤ width c p by unfold width; omega)
  cases a <;>
    simp [writing, encode_toNat', Nat.mod_mod_of_dvd _ hd, raw, readerUnit,
      Nat.pow_succ, Nat.add_mod, Nat.mul_mod]

theorem low_mask (c p : Nat) (s : BitVec (width c p)) :
    (s &&& lowMask c p).toNat = s.toNat % readerUnit c := by
  simpa only [lowMask, readerUnit, Nat.pow_zero, Nat.div_one, Nat.sub_zero, Nat.mul_one]
    using Zig.toNat_and_field s 0 (c + 1) (by omega) (by unfold width; omega)

theorem low_encode {c p r w : Nat} (hw : w < countBound c) (a : Bool) :
    (encode c p r w a &&& lowMask c p).toNat = 2 * w + if a then 1 else 0 := by
  rw [low_mask, low_mod, Nat.mod_eq_of_lt (low_lt hw a)]

theorem read_guard {c p r w : Nat} (hw : w < countBound c) (a : Bool) :
    (encode c p r w a &&& lowMask c p = 0) ↔ w = 0 ∧ a = false := by
  rw [← BitVec.toNat_inj, low_encode hw]
  cases a <;> simp <;> omega

theorem reader_mask (c p : Nat) (s : BitVec (width c p)) :
    (s &&& readerMask c p).toNat = readers c s * readerUnit c := by
  have he : 2 * c + 1 - (c + 1) = c := by omega
  simpa only [readerMask, readers, readerUnit, countBound, he]
    using Zig.toNat_and_field s (c + 1) (2 * c + 1) (by omega) (by unfold width; omega)

theorem last_reader_guard {c p r w : Nat} (hc : 0 < c)
    (hr : r < countBound c) (hw : w < countBound c)
    (a : Bool) :
    (encode c p r w a &&& readerMask c p = BitVec.ofNat (width c p) (readerUnit c)) ↔ r = 1 := by
  have hu : readerUnit c < 2 ^ width c p := by
    exact Nat.pow_lt_pow_right (by decide) (by unfold width; omega)
  rw [← BitVec.toNat_inj, reader_mask, readers_encode hr hw, Zig.toNat_ofNat_of_lt hu]
  simpa only [Nat.one_mul] using
    (Nat.mul_right_cancel_iff (n := r) (k := 1) (Nat.two_pow_pos (c + 1)))

theorem writing_mask (c p : Nat) (s : BitVec (width c p)) :
    (s &&& 1#(width c p)).toNat = s.toNat % 2 := by
  have h := Zig.toNat_and_field s 0 1 (by omega) (by unfold width; omega)
  simp only [Nat.pow_one, Nat.pow_zero, Nat.div_one, Nat.sub_zero, Nat.mul_one] at h
  change (s &&& 1#(width c p)).toNat = s.toNat % 2 at h
  exact h

/-- The second old-value guard of unlockShared, with no count hypotheses. -/
theorem writing_guard (c p : Nat) (s : BitVec (width c p)) :
    (s &&& 1#(width c p) != 0#(width c p)) = writing s := by
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, writing, beq_iff_eq]
  rw [BitVec.toNat_ne, writing_mask]
  exact Nat.mod_two_ne_zero

theorem raw_twice (c r w : Nat) (a : Bool) :
    raw c r w a = (r * 2 ^ c + w) * 2 + if a then 1 else 0 := by
  simp [raw, readerUnit, Nat.pow_succ, Nat.mul_add,
    Nat.mul_comm, Nat.mul_left_comm]

theorem clear_writer (c p r w : Nat) :
    encode c p r w true &&& clearWriting c p = encode c p r w false := by
  have hn : 1 ≤ width c p := by unfold width; omega
  have hp : 2 ^ width c p = 2 * 2 ^ (width c p - 1) := by
    simpa only [Nat.pow_one, Nat.mul_comm] using (Nat.pow_sub_mul_pow 2 hn).symm
  apply BitVec.eq_of_toNat_eq
  rw [clearWriting, show (2 : Nat) = 2 ^ 1 from rfl,
    Zig.toNat_and_field _ 1 (width c p) hn (Nat.le_refl _), encode_toNat', encode_toNat',
    raw_twice, raw_twice]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.pow_one]
  rw [hp, Nat.mod_mul_right_div_self]
  have hd : ((r * 2 ^ c + w) * 2 + 1) / 2 = r * 2 ^ c + w := by omega
  rw [hd, Nat.mod_mod]
  rw [Nat.mul_comm 2, Nat.mul_mod_mul_right]

theorem encode_inj {c p r w r' w' : Nat} (hr : r < countBound c) (hw : w < countBound c)
    (hr' : r' < countBound c) (hw' : w' < countBound c) (a a' : Bool) :
    encode c p r w a = encode c p r' w' a' ↔ r = r' ∧ w = w' ∧ a = a' := by
  constructor
  · intro he
    have er := congrArg (readers c) he
    have ew := congrArg (writers c) he
    have ea := congrArg writing he
    rw [readers_encode hr hw, readers_encode hr' hw'] at er
    rw [writers_encode hw, writers_encode hw'] at ew
    rw [writing_encode, writing_encode] at ea
    exact ⟨er, ew, ea⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- One arithmetic encoding equation serves all additive native operations. -/
theorem encode_add_ofNat (c p r w r' w' : Nat) (a a' : Bool) (k : Nat)
    (h : raw c r' w' a' = raw c r w a + k) :
    encode c p r w a + BitVec.ofNat (width c p) k = encode c p r' w' a' := by
  unfold encode
  rw [← BitVec.ofNat_add, ← h]

theorem add_reader (c p r w : Nat) (a : Bool) :
    encode c p r w a + BitVec.ofNat (width c p) (readerUnit c) =
      encode c p (r + 1) w a := by
  apply encode_add_ofNat
  simp only [raw, Nat.add_mul, Nat.one_mul]
  omega

theorem sub_reader (c p r w : Nat) (a : Bool) :
    encode c p (r + 1) w a - BitVec.ofNat (width c p) (readerUnit c) =
      encode c p r w a := by
  rw [← add_reader]
  exact BitVec.add_sub_cancel _ _

theorem add_writer (c p r w : Nat) (a : Bool) :
    encode c p r w a + 2 = encode c p r (w + 1) a := by
  apply encode_add_ofNat
  simp only [raw, Nat.mul_add, Nat.mul_one]
  omega

theorem enter_writer (c p r w : Nat) :
    encode c p r (w + 1) false + (-1) = encode c p r w true := by
  have he : encode c p r w true + 1 = encode c p r (w + 1) false := by
    apply encode_add_ofNat
    simp only [raw, Nat.mul_add, Nat.mul_one, Bool.false_eq_true, ↓reduceIte]
    omega
  rw [← he, BitVec.add_assoc]
  rw [BitVec.add_right_neg, BitVec.add_zero]

/-- Strict logical room justifies the actual checked Zig addition, separately
from the wrapping RMW equation. -/
theorem checked_add_reader {c p r w : Nat} (hr : r + 1 < countBound c)
    (hw : w < countBound c) (a : Bool) (safe : Bool) :
    Zig.add false (encode c p r w a) (BitVec.ofNat (width c p) (readerUnit c)) safe =
      pure (encode c p (r + 1) w a) := by
  have hsum : (encode c p r w a).toNat +
      (BitVec.ofNat (width c p) (readerUnit c)).toNat < 2 ^ width c p := by
    rw [encode_toNat (by omega : r < countBound c) hw a, BitVec.toNat_ofNat]
    calc
      _ ≤ raw c r w a + readerUnit c := Nat.add_le_add_left (Nat.mod_le _ _) _
      _ = raw c (r + 1) w a := by
        simp only [raw, Nat.add_mul, Nat.one_mul]; omega
      _ < _ := raw_lt hr hw a
  rw [Zig.add_unsigned_of_lt hsum, add_reader]

end Family

/-! ## The ABI64 std layout

Bit 63 is spare. Encoding unbounded counts can still set it; admission must
establish the actual 31-bit reader and pending-writer bounds. -/

abbrev readerUnit : Nat := Family.readerUnit 31
abbrev countBound : Nat := Family.countBound 31
abbrev lowMask : BitVec 64 := Family.lowMask 31 1
abbrev readerMask : BitVec 64 := Family.readerMask 31 1
abbrev writingBit : BitVec 64 := 1
abbrev clearWriting : BitVec 64 := Family.clearWriting 31 1
abbrev writerEntryDelta : BitVec 64 := -1

abbrev encode (r w : Nat) (a : Bool) : BitVec 64 := Family.encode 31 1 r w a
abbrev readers (s : BitVec 64) : Nat := Family.readers 31 s
abbrev writers (s : BitVec 64) : Nat := Family.writers 31 s
abbrev writing (s : BitVec 64) : Bool := Family.writing s

theorem encode_toNat' (r w : Nat) (a : Bool) :
    (encode r w a).toNat = (r * readerUnit + 2 * w + if a then 1 else 0) % 2 ^ 64 :=
  Family.encode_toNat' 31 1 r w a

theorem encode_toNat {r w : Nat} (hr : r < countBound) (hw : w < countBound) (a : Bool) :
    (encode r w a).toNat = r * readerUnit + 2 * w + if a then 1 else 0 :=
  Family.encode_toNat hr hw a

theorem readers_encode {r w : Nat} (hr : r < countBound) (hw : w < countBound)
    (a : Bool) : readers (encode r w a) = r := Family.readers_encode hr hw a

theorem writers_encode {r w : Nat} (hw : w < countBound) (a : Bool) :
    writers (encode r w a) = w := Family.writers_encode hw a

theorem writing_encode (r w : Nat) (a : Bool) : writing (encode r w a) = a :=
  Family.writing_encode 31 1 r w a

theorem add_reader (r w : Nat) (a : Bool) :
    encode r w a + BitVec.ofNat 64 readerUnit = encode (r + 1) w a :=
  Family.add_reader 31 1 r w a

theorem sub_reader (r w : Nat) (a : Bool) :
    encode (r + 1) w a - BitVec.ofNat 64 readerUnit = encode r w a :=
  Family.sub_reader 31 1 r w a

theorem add_writer (r w : Nat) (a : Bool) :
    encode r w a + 2 = encode r (w + 1) a := Family.add_writer 31 1 r w a

theorem enter_writer (r w : Nat) :
    encode r (w + 1) false + writerEntryDelta = encode r w true :=
  Family.enter_writer 31 1 r w

theorem checked_add_reader {r w : Nat} (hr : r + 1 < countBound) (hw : w < countBound)
    (a : Bool) (safe : Bool) :
    Zig.add false (encode r w a) (BitVec.ofNat 64 readerUnit) safe =
      pure (encode (r + 1) w a) := Family.checked_add_reader hr hw a safe

theorem low_mask (s : BitVec 64) : (s &&& lowMask).toNat = s.toNat % readerUnit :=
  Family.low_mask 31 1 s

theorem low_encode {r w : Nat} (hw : w < countBound) (a : Bool) :
    (encode r w a &&& lowMask).toNat = 2 * w + if a then 1 else 0 :=
  Family.low_encode hw a

theorem read_guard {r w : Nat} (hw : w < countBound) (a : Bool) :
    (encode r w a &&& lowMask = 0) ↔ w = 0 ∧ a = false := Family.read_guard hw a

theorem reader_mask (s : BitVec 64) :
    (s &&& readerMask).toNat = readers s * readerUnit := Family.reader_mask 31 1 s

theorem last_reader_guard {r w : Nat} (hr : r < countBound) (hw : w < countBound) (a : Bool) :
    (encode r w a &&& readerMask = BitVec.ofNat 64 readerUnit) ↔ r = 1 :=
  Family.last_reader_guard (by decide) hr hw a

theorem writing_guard (s : BitVec 64) : (s &&& writingBit != 0) = writing s :=
  Family.writing_guard 31 1 s

theorem clear_writer (r w : Nat) :
    encode r w true &&& clearWriting = encode r w false := Family.clear_writer 31 1 r w

theorem encode_inj {r w r' w' : Nat} (hr : r < countBound) (hw : w < countBound)
    (hr' : r' < countBound) (hw' : w' < countBound) (a a' : Bool) :
    encode r w a = encode r' w' a' ↔ r = r' ∧ w = w' ∧ a = a' :=
  Family.encode_inj hr hw hr' hw' a a'

end RwState

end Zig.Full
