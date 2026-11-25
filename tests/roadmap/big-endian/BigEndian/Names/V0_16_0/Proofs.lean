import BigEndian.Names.V0_16_0.S390x.Gen
import BigEndian.Names.V0_16_0.Mips64.Gen
import BigEndian.Names.V0_16_0.X64.Gen

/-!
# T03: `@tagName` and `@errorName` at both byte orders

`names.zig` translated from its s390x-linux, mips64-linux (big endian) and x86_64-linux (little
endian) exports by one Zig version (`check.sh`). The file of the 0.17.1 translations is written;
the file of the 0.16.0 ones is it with that version's names (`scripts/fixtures.py instance`).
A name is a slice into a static block of `mem0` whose bytes are the same at both orders: the
returned length is the name's byte count, the bytes read through the slice are the name, index
`len` reads the sentinel and `len + 1` is out of bounds, and an unnamed value of a
non-exhaustive enum (a two-byte tag) has no tag name. A name slice stored in memory has its
`usize` length at the profile's order: byte 7 of the length field at big endian, byte 0 at
little endian.
-/

namespace BigEndian.Names.V0_16_0.Proofs

open Zig BigEndian.Names.V0_16_0

/-- The UTF-8 bytes of `s`. -/
def bytesOf (s : String) : Array (BitVec 8) := s.toUTF8.toList.toArray.map (BitVec.ofNat 8 ·.toNat)

/-! ## s390x-linux (big endian) -/

theorem names_s390x :
    ((do let s ← S390x.colorName .green; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (S390x.mem0 .fresh)).run = some (.ok ((5 : BitVec 64), bytesOf "green")) ∧
    ((do let s ← S390x.levelName S390x.Level.high; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (S390x.mem0 .fresh)).run = some (.ok ((4 : BitVec 64), bytesOf "high")) ∧
    ((S390x.levelName ⟨7⟩).run' (S390x.mem0 .fresh)).run = some (.error .panic) ∧
    ((do let s ← S390x.faultName "TooLong"; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (S390x.mem0 .fresh)).run = some (.ok ((7 : BitVec 64), bytesOf "TooLong")) := by
  decide +kernel

theorem nameByte_s390x :
    ((S390x.nameByte .blue 1).run' (S390x.mem0 .fresh)).run = some (.ok 108) ∧
    ((S390x.nameByte .blue 4).run' (S390x.mem0 .fresh)).run = some (.ok 0) ∧
    ((S390x.nameByte .blue 5).run' (S390x.mem0 .fresh)).run = some (.error .outOfBounds) := by
  decide +kernel

/-- The stored length's last byte is its least significant one. -/
theorem storedLenByte_s390x :
    ((S390x.storedLenByte .green 7).run' (S390x.mem0 .fresh)).run = some (.ok 5) ∧
    ((S390x.storedLenByte .green 0).run' (S390x.mem0 .fresh)).run = some (.ok 0) := by
  decide +kernel

/-! ## mips64-linux (big endian) -/

theorem names_mips64 :
    ((do let s ← Mips64.colorName .green; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (Mips64.mem0 .fresh)).run = some (.ok ((5 : BitVec 64), bytesOf "green")) ∧
    ((do let s ← Mips64.levelName Mips64.Level.high; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (Mips64.mem0 .fresh)).run = some (.ok ((4 : BitVec 64), bytesOf "high")) ∧
    ((Mips64.levelName ⟨7⟩).run' (Mips64.mem0 .fresh)).run = some (.error .panic) ∧
    ((do let s ← Mips64.faultName "TooLong"; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (Mips64.mem0 .fresh)).run = some (.ok ((7 : BitVec 64), bytesOf "TooLong")) := by
  decide +kernel

theorem nameByte_mips64 :
    ((Mips64.nameByte .blue 1).run' (Mips64.mem0 .fresh)).run = some (.ok 108) ∧
    ((Mips64.nameByte .blue 4).run' (Mips64.mem0 .fresh)).run = some (.ok 0) ∧
    ((Mips64.nameByte .blue 5).run' (Mips64.mem0 .fresh)).run = some (.error .outOfBounds) := by
  decide +kernel

theorem storedLenByte_mips64 :
    ((Mips64.storedLenByte .green 7).run' (Mips64.mem0 .fresh)).run = some (.ok 5) ∧
    ((Mips64.storedLenByte .green 0).run' (Mips64.mem0 .fresh)).run = some (.ok 0) := by
  decide +kernel

/-! ## x86_64-linux (little endian) -/

theorem names_x64 :
    ((do let s ← X64.colorName .green; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (X64.mem0 .fresh)).run = some (.ok ((5 : BitVec 64), bytesOf "green")) ∧
    ((do let s ← X64.levelName X64.Level.high; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (X64.mem0 .fresh)).run = some (.ok ((4 : BitVec 64), bytesOf "high")) ∧
    ((X64.levelName ⟨7⟩).run' (X64.mem0 .fresh)).run = some (.error .panic) ∧
    ((do let s ← X64.faultName "TooLong"; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (X64.mem0 .fresh)).run = some (.ok ((7 : BitVec 64), bytesOf "TooLong")) := by
  decide +kernel

theorem nameByte_x64 :
    ((X64.nameByte .blue 1).run' (X64.mem0 .fresh)).run = some (.ok 108) ∧
    ((X64.nameByte .blue 4).run' (X64.mem0 .fresh)).run = some (.ok 0) ∧
    ((X64.nameByte .blue 5).run' (X64.mem0 .fresh)).run = some (.error .outOfBounds) := by
  decide +kernel

/-- The stored length's first byte is its least significant one. -/
theorem storedLenByte_x64 :
    ((X64.storedLenByte .green 0).run' (X64.mem0 .fresh)).run = some (.ok 5) ∧
    ((X64.storedLenByte .green 7).run' (X64.mem0 .fresh)).run = some (.ok 0) := by
  decide +kernel

end BigEndian.Names.V0_16_0.Proofs
