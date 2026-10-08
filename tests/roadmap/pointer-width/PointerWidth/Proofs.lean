import PointerWidth.Wasm32.Gen
import PointerWidth.Wasi.Gen
import PointerWidth.X64.Gen
import ZigLean.Mem.WidthLemmas

/-!
# T02: one client, proved under the wasm32 and the x86_64 profile

`pointer_width.zig` translated from its wasm32-freestanding, wasm32-wasi and x86_64-linux
exports (`check.sh`). The same statements hold with `2 ^ 32` and `2 ^ 64`: `usize`
multiplication and addition overflow, the allocation byte count, slice bounds and the
in-memory layout of a pointer and a slice.
-/

namespace PointerWidth.Proofs

open Zig

/-! ## `usize` arithmetic -/

theorem byteCount_w32 (n : BitVec 32) :
    Wasm32.byteCount n = pure (if 2 ^ 32 ≤ n.toNat * 4 then none else some (n * 4)) := by
  simp only [Wasm32.byteCount, Zig.mulWithOverflow, BitVec.umulOverflow]
  by_cases h : 2 ^ 32 ≤ n.toNat * 4 <;> simp [h, StateT.run', bind, pure] <;> rfl

theorem byteCount_x64 (n : BitVec 64) :
    X64.byteCount n = pure (if 2 ^ 64 ≤ n.toNat * 4 then none else some (n * 4)) := by
  simp only [X64.byteCount, Zig.mulWithOverflow, BitVec.umulOverflow]
  by_cases h : 2 ^ 64 ≤ n.toNat * 4 <;> simp [h, StateT.run', bind, pure] <;> rfl

theorem byteCount_wasi (n : BitVec 32) :
    Wasi.byteCount n = pure (if 2 ^ 32 ≤ n.toNat * 4 then none else some (n * 4)) := by
  simp only [Wasi.byteCount, Zig.mulWithOverflow, BitVec.umulOverflow]
  by_cases h : 2 ^ 32 ≤ n.toNat * 4 <;> simp [h, StateT.run', bind, pure] <;> rfl

/-- The boundary differs: `2 ^ 30` items of 4 bytes overflow a 32-bit `usize` only. -/
theorem byteCount_boundary :
    (Wasm32.byteCount (BitVec.ofNat 32 (2 ^ 30))).run = some (.ok none) ∧
    (Wasm32.byteCount (BitVec.ofNat 32 (2 ^ 30 - 1))).run = some (.ok (some (BitVec.ofNat 32 (2 ^ 32 - 4)))) ∧
    (X64.byteCount (BitVec.ofNat 64 (2 ^ 30))).run = some (.ok (some (BitVec.ofNat 64 (2 ^ 32)))) ∧
    (X64.byteCount (BitVec.ofNat 64 (2 ^ 62))).run = some (.ok none) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem succ_w32 (n : BitVec 32) :
    Wasm32.succ n = if n.toNat + 1 ≥ 2 ^ 32 then throw .overflow else pure (n + 1) := by
  by_cases h : n.toNat + 1 ≥ 2 ^ 32 <;>
    simp [Wasm32.succ, h, StateT.run', bind, pure, throw, throwThe] <;> rfl

theorem succ_x64 (n : BitVec 64) :
    X64.succ n = if n.toNat + 1 ≥ 2 ^ 64 then throw .overflow else pure (n + 1) := by
  by_cases h : n.toNat + 1 ≥ 2 ^ 64 <;>
    simp [X64.succ, h, StateT.run', bind, pure, throw, throwThe] <;> rfl

theorem succ_boundary :
    (Wasm32.succ (BitVec.ofNat 32 (2 ^ 32 - 1))).run = some (.error .overflow) ∧
    (X64.succ (BitVec.ofNat 64 (2 ^ 32 - 1))).run = some (.ok (BitVec.ofNat 64 (2 ^ 32))) := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ## Slice bounds -/

theorem at_w32 (s : Array (BitVec 32)) (i : BitVec 32) (h : s.size < 2 ^ 32) :
    Wasm32.«at» s i = if hi : i.toNat < s.size then pure s[i.toNat] else throw .outOfBounds := by
  have hl : (Zig.lenOf 32 s).toNat = s.size := by simp [Zig.lenOf, Nat.mod_eq_of_lt h]
  by_cases hi : i.toNat < s.size <;>
    simp [Wasm32.«at», zig_unfold, hi, hl, Zig.indexOf]

theorem at_x64 (s : Array (BitVec 32)) (i : BitVec 64) (h : s.size < 2 ^ 64) :
    X64.«at» s i = if hi : i.toNat < s.size then pure s[i.toNat] else throw .outOfBounds := by
  have hl : (Zig.len s).toNat = s.size := by simp [Zig.len, Nat.mod_eq_of_lt h]
  by_cases hi : i.toNat < s.size <;>
    simp [X64.«at», zig_unfold, hi, hl, Zig.index]

/-! ## Allocation byte counts -/

/-- `alloc(u32, n)` with `4 * n ≥ 2 ^ 32` is `error.OutOfMemory` on wasm32, before any
allocator decision: memory is unchanged. -/
theorem zeros_overflow_w32 (a : Allocator) (n : BitVec 32) (m : Mem) (h : 2 ^ 32 ≤ 4 * n.toNat) :
    (Wasm32.zeros a n).run m = pure (.error "OutOfMemory", m) := by
  have ho := Allocator.allocOf_overflow .w32 a 4 4 n h
  simp only [Wasm32.zeros, ho]
  rfl

theorem zeros_overflow_x64 (a : Allocator) (n : BitVec 64) (m : Mem) (h : 2 ^ 64 ≤ 4 * n.toNat) :
    (X64.zeros a n).run m = pure (.error "OutOfMemory", m) := by
  have ho : a.alloc 4 4 n = pure (.error "OutOfMemory") := by simp [Allocator.alloc, h]
  simp only [X64.zeros, ho]
  rfl

/-- The same request, `2 ^ 30` items of 4 bytes: rejected by the 32-bit size check only. -/
theorem zeros_boundary (a : Allocator) (m : Mem) :
    (Wasm32.zeros a (2 ^ 30)).run m = pure (.error "OutOfMemory", m) ∧
    ¬ (2 ^ 64 ≤ 4 * (2 ^ 30 : BitVec 64).toNat) :=
  ⟨zeros_overflow_w32 a _ m (by decide), by decide⟩

/-! ## Layout of a pointer and a slice in memory -/

/-- A `View` stored as global 0, its `first` pointing to global 1 (a `u32`). -/
def wasmMem (len : BitVec 32) : Mem :=
  Mem.ofGlobals [(Enc.encode ({ first := ⟨some 1, 0⟩, rest := ⟨⟨some 1, 0⟩, len⟩ } : Wasm32.View), 4, .global),
    (Enc.encode (7 : BitVec 32), 4, .global)]

def x64Mem (len : BitVec 64) : Mem :=
  Mem.ofGlobals [(Enc.encode ({ first := ⟨some 1, 0⟩, rest := ⟨⟨some 1, 0⟩, len⟩ } : X64.View), 8, .global),
    (Enc.encode (7 : BitVec 32), 4, .global)]

/-- wasm32: 12 bytes; the length at offset 8. x86_64: 24 bytes; the length at offset 16. -/
theorem view_layout :
    (wasmMem 0).blocks[0]?.map (·.bytes.size) = some 12 ∧
      (x64Mem 0).blocks[0]?.map (·.bytes.size) = some 24 := by
  decide +kernel

theorem restLen_w32 : ((Wasm32.restLen ⟨some 0, 0⟩).run' (wasmMem 5)).run = some (.ok 5) := by
  decide +kernel
theorem restLen_x64 : ((X64.restLen ⟨some 0, 0⟩).run' (x64Mem 5)).run = some (.ok 5) := by
  decide +kernel

/-- `setFirst` loads the 4-byte (wasm32) or 8-byte (x86_64) pointer and stores through it. -/
theorem setFirst_w32 :
    (((do Wasm32.setFirst ⟨some 0, 0⟩ 9; load (BitVec 32) 4 ⟨some 1, 0⟩) : MemM _).run'
      (wasmMem 5)).run = some (.ok 9) := by decide +kernel

theorem setFirst_x64 :
    (((do X64.setFirst ⟨some 0, 0⟩ 9; load (BitVec 32) 4 ⟨some 1, 0⟩) : MemM _).run'
      (x64Mem 5)).run = some (.ok 9) := by decide +kernel

end PointerWidth.Proofs
