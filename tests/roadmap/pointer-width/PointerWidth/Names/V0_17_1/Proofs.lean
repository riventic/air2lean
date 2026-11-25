import PointerWidth.Names.V0_17_1.Wasm32.Gen
import PointerWidth.Names.V0_17_1.Wasi.Gen
import PointerWidth.Names.V0_17_1.X64.Gen
import ZigLean.Mem.WidthLemmas

/-!
# T02: `@tagName` and `@errorName` under the wasm32 and the x86_64 profile

`names.zig` translated from its Zig 0.17.1 wasm32-freestanding, wasm32-wasi and x86_64-linux
exports (`check.sh`; the 0.16.0 instance is this file renamed, `scripts/fixtures.py instance`).
A name is a `[:0]const u8` into a static block of `mem0`: a `Zig.Slice32` (32-bit `usize`
length) on wasm32, a `Zig.Slice` on x86_64. The same statements hold for both widths: the
returned length is the name's byte count, the bytes read through the slice are the name, the
sentinel index reads 0 and the next index is out of bounds; an unnamed value of a
non-exhaustive enum has no tag name (a safety panic).
-/

namespace PointerWidth.Names.V0_17_1.Proofs

open Zig PointerWidth.Names.V0_17_1

/-- The UTF-8 bytes of `s`. -/
def bytesOf (s : String) : Array (BitVec 8) := s.toUTF8.toList.toArray.map (BitVec.ofNat 8 ·.toNat)

/-! ## wasm32-freestanding -/

theorem colorName_w32 :
    ((do let s ← Wasm32.colorName .green; pure (s.len, ← readSliceOf (BitVec 8) 1 s) : MemM _).run'
      (Wasm32.mem0 .fresh)).run = some (.ok ((5 : BitVec 32), bytesOf "green")) := by
  decide +kernel

theorem levelName_w32 :
    ((do let s ← Wasm32.levelName Wasm32.Level.high; pure (s.len, ← readSliceOf (BitVec 8) 1 s) : MemM _).run'
      (Wasm32.mem0 .fresh)).run = some (.ok ((4 : BitVec 32), bytesOf "high")) ∧
    ((Wasm32.levelName ⟨7⟩).run' (Wasm32.mem0 .fresh)).run = some (.error .panic) := by
  decide +kernel

theorem faultName_w32 :
    ((do let s ← Wasm32.faultName "TooLong"; pure (s.len, ← readSliceOf (BitVec 8) 1 s) : MemM _).run'
      (Wasm32.mem0 .fresh)).run = some (.ok ((7 : BitVec 32), bytesOf "TooLong")) := by
  decide +kernel

/-- Index `len` of a sentinel-terminated name reads the sentinel; `len + 1` is out of bounds. -/
theorem nameByte_w32 :
    ((Wasm32.nameByte .blue 1).run' (Wasm32.mem0 .fresh)).run = some (.ok 108) ∧
    ((Wasm32.nameByte .blue 4).run' (Wasm32.mem0 .fresh)).run = some (.ok 0) ∧
    ((Wasm32.nameByte .blue 5).run' (Wasm32.mem0 .fresh)).run = some (.error .outOfBounds) := by
  decide +kernel

/-! ## wasm32-wasi -/

theorem colorName_wasi :
    ((do let s ← Wasi.colorName .green; pure (s.len, ← readSliceOf (BitVec 8) 1 s) : MemM _).run'
      (Wasi.mem0 .fresh)).run = some (.ok ((5 : BitVec 32), bytesOf "green")) := by
  decide +kernel

theorem levelName_wasi :
    ((do let s ← Wasi.levelName Wasi.Level.high; pure (s.len, ← readSliceOf (BitVec 8) 1 s) : MemM _).run'
      (Wasi.mem0 .fresh)).run = some (.ok ((4 : BitVec 32), bytesOf "high")) ∧
    ((Wasi.levelName ⟨7⟩).run' (Wasi.mem0 .fresh)).run = some (.error .panic) := by
  decide +kernel

theorem faultName_wasi :
    ((do let s ← Wasi.faultName "TooLong"; pure (s.len, ← readSliceOf (BitVec 8) 1 s) : MemM _).run'
      (Wasi.mem0 .fresh)).run = some (.ok ((7 : BitVec 32), bytesOf "TooLong")) := by
  decide +kernel

theorem nameByte_wasi :
    ((Wasi.nameByte .blue 1).run' (Wasi.mem0 .fresh)).run = some (.ok 108) ∧
    ((Wasi.nameByte .blue 4).run' (Wasi.mem0 .fresh)).run = some (.ok 0) ∧
    ((Wasi.nameByte .blue 5).run' (Wasi.mem0 .fresh)).run = some (.error .outOfBounds) := by
  decide +kernel

/-! ## x86_64-linux -/

theorem colorName_x64 :
    ((do let s ← X64.colorName .green; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (X64.mem0 .fresh)).run = some (.ok ((5 : BitVec 64), bytesOf "green")) := by
  decide +kernel

theorem levelName_x64 :
    ((do let s ← X64.levelName X64.Level.high; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (X64.mem0 .fresh)).run = some (.ok ((4 : BitVec 64), bytesOf "high")) ∧
    ((X64.levelName ⟨7⟩).run' (X64.mem0 .fresh)).run = some (.error .panic) := by
  decide +kernel

theorem faultName_x64 :
    ((do let s ← X64.faultName "TooLong"; pure (s.len, ← readSlice (BitVec 8) 1 s) : MemM _).run'
      (X64.mem0 .fresh)).run = some (.ok ((7 : BitVec 64), bytesOf "TooLong")) := by
  decide +kernel

theorem nameByte_x64 :
    ((X64.nameByte .blue 1).run' (X64.mem0 .fresh)).run = some (.ok 108) ∧
    ((X64.nameByte .blue 4).run' (X64.mem0 .fresh)).run = some (.ok 0) ∧
    ((X64.nameByte .blue 5).run' (X64.mem0 .fresh)).run = some (.error .outOfBounds) := by
  decide +kernel

end PointerWidth.Names.V0_17_1.Proofs
