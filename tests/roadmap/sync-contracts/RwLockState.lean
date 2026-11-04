import ZigLean.Sep.Full.RwLock
import ZigLean.Mem.Thread

/- State-value controls for the real RwLock word encoding. These check the
native masks and RMW value functions, not a reachable scheduler execution or
the reader/writer protocol's resource invariant. -/

namespace Zig.Full.RwLockStateTest

theorem two_readers :
    RmwOp.add.apply false (RwState.encode 1 0 false) 4294967296 =
      RwState.encode 2 0 false := by decide +kernel

theorem enter_with_readers :
    RmwOp.add.apply false (RwState.encode 2 1 false) 18446744073709551615 =
      RwState.encode 2 0 true := by decide +kernel

theorem last_reader_guards :
    RwState.encode 1 0 true &&& 9223372032559808512 = 4294967296 ∧
      RwState.encode 1 0 true &&& 1 ≠ 0 := by decide +kernel

theorem retire_before_writer :
    RwState.encode 1 0 false &&& 9223372032559808512 = 4294967296 ∧
      RwState.encode 1 0 false &&& 1 = 0 := by decide +kernel

def maxReaders : BitVec 64 := RwState.encode (RwState.countBound - 1) 0 false
def incremented : BitVec 64 := RmwOp.add.apply false maxReaders 4294967296

theorem max_admission_guard : maxReaders &&& 4294967295 = 0 := by decide +kernel

theorem max_add_no_64bit_overflow :
    maxReaders.toNat + 4294967296 < 2 ^ 64 := by decide +kernel

theorem max_add_reserved_bit : incremented.toNat = 2 ^ 63 := by decide +kernel

theorem max_add_reader_mask_zero :
    incremented &&& 9223372032559808512 = 0 := by decide +kernel

theorem max_add_reader_decode_zero : RwState.readers incremented = 0 := by decide +kernel

end Zig.Full.RwLockStateTest
