import ZigLean.Sep.Full.RwLock
import ZigLean.Sep.Full.RwLockShare
import ZigLean.Mem.Thread

/- Value algebra controls for the real ABI64 Gen operands and the mathematical
ABI32 layout. The latter does not claim runtime atomic/thread support on ABI32.
Run under build-guard after the changed module build:
  lake env lean -R . tests/roadmap/sync-contracts/RwLockState.lean
These are library instances and closed boundary values, not scheduler runs. -/

namespace Zig.Full.RwLockStateTest

theorem rmw_add_reader (r w : Nat) (a : Bool) :
    RmwOp.add.apply false (RwState.encode r w a) 4294967296 =
      RwState.encode (r + 1) w a := by
  simp only [RmwOp.apply]
  exact RwState.add_reader r w a

theorem rmw_sub_reader (r w : Nat) (a : Bool) :
    RmwOp.sub.apply false (RwState.encode (r + 1) w a) 4294967296 =
      RwState.encode r w a := by
  simp only [RmwOp.apply]
  exact RwState.sub_reader r w a

theorem rmw_add_writer (r w : Nat) (a : Bool) :
    RmwOp.add.apply false (RwState.encode r w a) 2 =
      RwState.encode r (w + 1) a := by
  simpa only [RmwOp.apply] using RwState.add_writer r w a

theorem rmw_enter_writer (r w : Nat) :
    RmwOp.add.apply false (RwState.encode r (w + 1) false) 18446744073709551615 =
      RwState.encode r w true := by
  simp only [RmwOp.apply]
  exact RwState.enter_writer r w

theorem rmw_clear_writer (r w : Nat) :
    RmwOp.and.apply false (RwState.encode r w true) 18446744073709551614 =
      RwState.encode r w false := by
  simp only [RmwOp.apply]
  exact RwState.clear_writer r w

theorem checked_reader_add {r w : Nat} (hr : r + 1 < RwState.countBound)
    (hw : w < RwState.countBound) (a : Bool) :
    Zig.add false (RwState.encode r w a) (4294967296 : BitVec 64) =
      pure (RwState.encode (r + 1) w a) :=
  RwState.checked_add_reader hr hw a true

theorem fast_guard {r w : Nat} (hw : w < RwState.countBound) (a : Bool) :
    (RwState.encode r w a &&& 4294967295 = 0) ↔ w = 0 ∧ a = false :=
  RwState.read_guard hw a

theorem old_reader_guard {r w : Nat} (hr : r < RwState.countBound)
    (hw : w < RwState.countBound) (a : Bool) :
    (RwState.encode r w a &&& 9223372032559808512 = 4294967296) ↔ r = 1 :=
  RwState.last_reader_guard hr hw a

theorem old_writer_guard (r w : Nat) (a : Bool) :
    (RwState.encode r w a &&& 1 != 0) = a := by
  rw [RwState.writing_guard, RwState.writing_encode]

theorem decode_reader {r w : Nat} (hr : r < RwState.countBound)
    (hw : w < RwState.countBound) (a : Bool) :
    RwState.readers (RwState.encode r w a) = r := RwState.readers_encode hr hw a

theorem decode_writer {r w : Nat} (hw : w < RwState.countBound) (a : Bool) :
    RwState.writers (RwState.encode r w a) = w := RwState.writers_encode hw a

theorem decode_writing (r w : Nat) (a : Bool) :
    RwState.writing (RwState.encode r w a) = a := RwState.writing_encode r w a

theorem encoding_injective {r w r' w' : Nat} (hr : r < RwState.countBound)
    (hw : w < RwState.countBound) (hr' : r' < RwState.countBound)
    (hw' : w' < RwState.countBound) (a a' : Bool) :
    RwState.encode r w a = RwState.encode r' w' a' ↔ r = r' ∧ w = w' ∧ a = a' :=
  RwState.encode_inj hr hw hr' hw' a a'

theorem math32_add_reader (r w : Nat) (a : Bool) :
    RmwOp.add.apply false (RwState.Family.encode 15 1 r w a) 65536 =
      RwState.Family.encode 15 1 (r + 1) w a := by
  simp only [RmwOp.apply]
  exact RwState.Family.add_reader 15 1 r w a

theorem math32_decode {r w : Nat} (hr : r < 32768) (hw : w < 32768) (a : Bool) :
    RwState.Family.readers 15 (RwState.Family.encode 15 1 r w a) = r ∧
    RwState.Family.writers 15 (RwState.Family.encode 15 1 r w a) = w ∧
    RwState.Family.writing (RwState.Family.encode 15 1 r w a) = a :=
  ⟨RwState.Family.readers_encode hr hw a, RwState.Family.writers_encode hw a,
    RwState.Family.writing_encode 15 1 r w a⟩

theorem math32_masks (s : BitVec 32) :
    (s &&& 2147418112).toNat = RwState.Family.readers 15 s * 65536 :=
  RwState.Family.reader_mask 15 1 s

theorem math32_checked {r w : Nat} (hr : r + 1 < 32768) (hw : w < 32768) (a : Bool) :
    Zig.add false (RwState.Family.encode 15 1 r w a) (65536 : BitVec 32) =
      pure (RwState.Family.encode 15 1 (r + 1) w a) :=
  RwState.Family.checked_add_reader hr hw a true

def maxReaders : BitVec 64 := RwState.encode (RwState.countBound - 1) 0 false
def incremented : BitVec 64 := RmwOp.add.apply false maxReaders 4294967296

theorem max_admission_guard : maxReaders &&& RwState.lowMask = 0 := by
  exact (RwState.read_guard (r := RwState.countBound - 1) (by decide : 0 < RwState.countBound)
    false).mpr ⟨rfl, rfl⟩

theorem max_add_no_64bit_overflow :
    maxReaders.toNat + 4294967296 < 2 ^ 64 := by decide +kernel

theorem max_checked_add : Zig.add false maxReaders (4294967296 : BitVec 64) =
    pure incremented := by
  rw [Zig.add_unsigned_of_lt max_add_no_64bit_overflow]
  rfl

theorem max_add_reserved_bit : incremented.toNat = 2 ^ 63 := by decide +kernel

theorem max_add_reader_mask_zero : incremented &&& RwState.readerMask = 0 := by decide +kernel

theorem max_add_reader_decode_zero : RwState.readers incremented = 0 := by decide +kernel

def maxWriters : BitVec 64 := RwState.encode 0 (RwState.countBound - 1) false

theorem writer_overflow_carry :
    RmwOp.add.apply false maxWriters 2 = RwState.encode 1 0 false := by
  calc
    _ = RwState.encode 0 (RwState.countBound - 1 + 1) false :=
      rmw_add_writer _ _ _
    _ = RwState.encode 1 0 false := by decide +kernel

theorem writer_overflow_decoders :
    RwState.writers (RmwOp.add.apply false maxWriters 2) = 0 ∧
      RwState.readers (RmwOp.add.apply false maxWriters 2) = 1 := by
  rw [writer_overflow_carry]
  exact ⟨RwState.writers_encode (by decide) false,
    RwState.readers_encode (by decide) (by decide) false⟩

theorem last_reader_guards :
    RwState.encode 1 0 true &&& RwState.readerMask = BitVec.ofNat 64 RwState.readerUnit ∧
      (RwState.encode 1 0 true &&& 1 != 0) = true :=
  ⟨(RwState.last_reader_guard (by decide) (by decide) true).mpr rfl,
    old_writer_guard 1 0 true⟩

theorem retire_before_writer :
    RwState.encode 1 0 false &&& RwState.readerMask = BitVec.ofNat 64 RwState.readerUnit ∧
      (RwState.encode 1 0 false &&& 1 != 0) = false :=
  ⟨(RwState.last_reader_guard (by decide) (by decide) false).mpr rfl,
    old_writer_guard 1 0 false⟩

/-- Two readers' halves of the whole protected resource join back to the whole, whose shares are
exact, so a writer after both readers finds every byte held whole. -/
theorem two_readers_join (r : Res) (l : Loc) :
    ((rsum (r.frac Frac.one.half) (r.frac Frac.one.half)).gh.share l).Total := by
  rw [Res.frac_add, Frac.half_add_half]; exact Res.frac_one_total r l

/-- A third reader splits the free half again; the three fractions stay valid. -/
theorem three_readers_valid (r : Res) (l : Loc) :
    ((rsum (r.frac Frac.one.half)
      (rsum (r.frac Frac.one.half.half) (r.frac Frac.one.half.half))).gh.share l).Valid := by
  rw [Res.frac_add, Frac.half_add_half, Res.frac_add, Frac.half_add_half]
  exact FHeap.shares_valid (by decide) r.heap l

end Zig.Full.RwLockStateTest
