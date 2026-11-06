import ZigLean.Sep.Full.RwLock
import ZigLean.Mem.Thread

/- Value algebra controls for the real ABI64 Gen operands and the mathematical
ABI32 layout. The latter does not claim runtime atomic/thread support on ABI32.
The ABI64 instance uses the `Family` lemmas directly through its `abbrev`s.
Run under build-guard after the changed module build:
  lake env lean -R . tests/roadmap/sync-contracts/RwLockState.lean
These are library instances and closed boundary values, not scheduler runs. -/

namespace Zig.Full.RwLockStateTest

open RwState

/-! ## The native operands of the 0.17 Gen bodies -/

theorem rmw_add_reader (r w : Nat) (a : Bool) :
    RmwOp.add.apply false (encode r w a) 4294967296 = encode (r + 1) w a := by
  simp only [RmwOp.apply]
  exact Family.add_reader 31 1 r w a

theorem rmw_sub_reader (r w : Nat) (a : Bool) :
    RmwOp.sub.apply false (encode (r + 1) w a) 4294967296 = encode r w a := by
  simp only [RmwOp.apply]
  exact Family.sub_reader 31 1 r w a

theorem rmw_add_writer (r w : Nat) (a : Bool) :
    RmwOp.add.apply false (encode r w a) 2 = encode r (w + 1) a := by
  simpa only [RmwOp.apply] using Family.add_writer 31 1 r w a

theorem rmw_sub_writer (r w : Nat) (a : Bool) :
    RmwOp.sub.apply false (encode r (w + 1) a) 2 = encode r w a := by
  simpa only [RmwOp.apply] using Family.sub_writer 31 1 r w a

theorem rmw_enter_writer (r w : Nat) :
    RmwOp.add.apply false (encode r (w + 1) false) 18446744073709551615 = encode r w true := by
  simp only [RmwOp.apply]
  exact Family.enter_writer 31 1 r w

theorem rmw_clear_writer (r w : Nat) :
    RmwOp.and.apply false (encode r w true) 18446744073709551614 = encode r w false := by
  simp only [RmwOp.apply]
  exact Family.clear_writer 31 1 r w

/-- `tryLock`'s CAS value `state | is_writing`. -/
theorem try_set_writing (r w : Nat) : encode r w false ||| 1 = encode r w true :=
  Family.set_writing 31 1 r w

theorem checked_reader_add {r w : Nat} (hr : r + 1 < countBound) (hw : w < countBound) (a : Bool) :
    Zig.add false (encode r w a) (4294967296 : BitVec 64) = pure (encode (r + 1) w a) :=
  Family.checked_add_reader hr hw a true

theorem fast_guard {r w : Nat} (hw : w < countBound) (a : Bool) :
    (encode r w a &&& 4294967295 = 0) ↔ w = 0 ∧ a = false :=
  Family.read_guard hw a

theorem old_reader_guard {r w : Nat} (hr : r < countBound) (hw : w < countBound) (a : Bool) :
    (encode r w a &&& 9223372032559808512 = 4294967296) ↔ r = 1 :=
  Family.last_reader_guard (by decide) hr hw a

theorem old_writer_guard (r w : Nat) (a : Bool) : (encode r w a &&& 1 != 0) = a :=
  (Family.writing_guard 31 1 _).trans (Family.writing_encode 31 1 r w a)

/-- `lock`'s drain guard (Gen `lockUncancelable`: `i7 &&& 9223372032559808512 != 0`) on the old
value of its `-1`: the writer waits at the semaphore exactly when readers remain. -/
theorem lock_drain_guard {r w : Nat} (hr : r < countBound) (hw : w + 1 < countBound) :
    (encode r (w + 1) false &&& 9223372032559808512 != 0) = (r != 0) :=
  Family.drain_guard_encode hr hw false

/-- The drain guard holds for any word, in range or not: it reads only the reader field. -/
theorem drain_guard_any (s : BitVec 64) :
    (s &&& 9223372032559808512 != 0) = (readers s != 0) :=
  Family.drain_guard 31 1 s

theorem drain_one_reader : (encode 1 1 false &&& 9223372032559808512 != 0) = true :=
  lock_drain_guard (by decide) (by decide)

theorem drain_no_reader : (encode 0 1 false &&& 9223372032559808512 != 0) = false :=
  lock_drain_guard (by decide) (by decide)

/-- Bit 63 is outside the reader field: the guard lets a writer in past an overflowed count. -/
theorem drain_overflow : ((9223372036854775808 : BitVec 64) &&& 9223372032559808512 != 0) = false := by
  decide +kernel

/-! ## Literal boundary states -/

theorem state_zero :
    encode 0 0 false = 0 ∧ readers 0 = 0 ∧ writers 0 = 0 ∧ writing 0 = false := by
  decide +kernel

theorem state_one_reader :
    encode 1 0 false = 4294967296 ∧ readers 4294967296 = 1 ∧ writers 4294967296 = 0 ∧
      writing 4294967296 = false := by
  decide +kernel

theorem state_max_readers :
    encode (2 ^ 31 - 1) 0 false = 9223372032559808512 ∧
      readers 9223372032559808512 = 2 ^ 31 - 1 ∧ writers 9223372032559808512 = 0 ∧
      writing 9223372032559808512 = false := by
  decide +kernel

theorem state_max_writers :
    encode 0 (2 ^ 31 - 1) false = 4294967294 ∧ readers 4294967294 = 0 ∧
      writers 4294967294 = 2 ^ 31 - 1 ∧ writing 4294967294 = false := by
  decide +kernel

theorem state_writing :
    encode 0 0 true = 1 ∧ readers 1 = 0 ∧ writers 1 = 0 ∧ writing 1 = true := by
  decide +kernel

/-- The overflow value (bit 63 only) decodes as the free lock. -/
theorem state_overflow :
    readers 9223372036854775808 = 0 ∧ writers 9223372036854775808 = 0 ∧
      writing 9223372036854775808 = false := by
  decide +kernel

/-! ## The mathematical ABI32 layout -/

theorem math32_add_reader (r w : Nat) (a : Bool) :
    RmwOp.add.apply false (Family.encode 15 1 r w a) 65536 = Family.encode 15 1 (r + 1) w a := by
  simp only [RmwOp.apply]
  exact Family.add_reader 15 1 r w a

theorem math32_decode {r w : Nat} (hr : r < 32768) (hw : w < 32768) (a : Bool) :
    Family.readers 15 (Family.encode 15 1 r w a) = r ∧
    Family.writers 15 (Family.encode 15 1 r w a) = w ∧
    Family.writing (Family.encode 15 1 r w a) = a :=
  ⟨Family.readers_encode hr hw a, Family.writers_encode hw a, Family.writing_encode 15 1 r w a⟩

theorem math32_masks (s : BitVec 32) :
    (s &&& 2147418112).toNat = Family.readers 15 s * 65536 :=
  Family.reader_mask 15 1 s

theorem math32_checked {r w : Nat} (hr : r + 1 < 32768) (hw : w < 32768) (a : Bool) :
    Zig.add false (Family.encode 15 1 r w a) (65536 : BitVec 32) =
      pure (Family.encode 15 1 (r + 1) w a) :=
  Family.checked_add_reader hr hw a true

/-! ## The carry boundaries (ledger `rwlock-reader-admission-room`) -/

def maxReaders : BitVec 64 := encode (countBound - 1) 0 false
def incremented : BitVec 64 := RmwOp.add.apply false maxReaders 4294967296

theorem max_admission_guard : maxReaders &&& lowMask = 0 :=
  (Family.read_guard (r := countBound - 1) (by decide : 0 < countBound) false).mpr ⟨rfl, rfl⟩

theorem max_add_no_64bit_overflow : maxReaders.toNat + 4294967296 < 2 ^ 64 := by decide +kernel

theorem max_checked_add : Zig.add false maxReaders (4294967296 : BitVec 64) = pure incremented := by
  rw [Zig.add_unsigned_of_lt max_add_no_64bit_overflow]
  rfl

theorem max_add_reserved_bit : incremented.toNat = 2 ^ 63 := by decide +kernel

theorem max_add_reader_mask_zero : incremented &&& readerMask = 0 := by decide +kernel

theorem max_add_reader_decode_zero : readers incremented = 0 := by decide +kernel

def maxWriters : BitVec 64 := encode 0 (countBound - 1) false

theorem writer_overflow_carry : RmwOp.add.apply false maxWriters 2 = encode 1 0 false := by
  calc
    _ = encode 0 (countBound - 1 + 1) false := rmw_add_writer _ _ _
    _ = encode 1 0 false := by decide +kernel

theorem writer_overflow_decoders :
    writers (RmwOp.add.apply false maxWriters 2) = 0 ∧
      readers (RmwOp.add.apply false maxWriters 2) = 1 := by
  rw [writer_overflow_carry]
  exact ⟨Family.writers_encode (by decide) false, Family.readers_encode (by decide) (by decide) false⟩

theorem last_reader_guards :
    encode 1 0 true &&& readerMask = BitVec.ofNat 64 readerUnit ∧
      (encode 1 0 true &&& 1 != 0) = true :=
  ⟨(Family.last_reader_guard (by decide) (by decide) (by decide) true).mpr rfl,
    old_writer_guard 1 0 true⟩

theorem retire_before_writer :
    encode 1 0 false &&& readerMask = BitVec.ofNat 64 readerUnit ∧
      (encode 1 0 false &&& 1 != 0) = false :=
  ⟨(Family.last_reader_guard (by decide) (by decide) (by decide) false).mpr rfl,
    old_writer_guard 1 0 false⟩

end Zig.Full.RwLockStateTest
