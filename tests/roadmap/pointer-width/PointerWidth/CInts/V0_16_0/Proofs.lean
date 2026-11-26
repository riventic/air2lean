import PointerWidth.CInts.V0_16_0.Wasm32.Gen
import PointerWidth.CInts.V0_16_0.Wasi.Gen
import PointerWidth.CInts.V0_16_0.X64.Gen
import ZigLean.Mem.WidthLemmas

/-!
# T02: the C integer types under the wasm32 and the x86_64 profile

`c_ints.zig` translated from its wasm32-freestanding, wasm32-wasi and x86_64-linux exports by one
Zig version (`check.sh`). The file of the 0.17.1 translations is written; the file of the 0.16.0
ones is it with that version's names (`scripts/fixtures.py instance`).

The AIR names no C type: a C integer type is the integer of its width and signedness on the
target. So each checked operation is specified once for every width (`ZigLean/Mem/WidthLemmas.lean`
§Integer widths: `succSigned`, `succUnsigned`, `negSigned`, `mulUnsignedOpt` and the closed
forms of `Zig.add`, `Zig.sub` and `Zig.intCast`), and every translation is an instance at its
target's width: `c_char` 8 (signed on all three targets), `c_short` and
`c_ushort` 16, `c_int` and `c_uint` 32, `c_longlong` and `c_ulonglong` 64 bits on all three;
`c_long`, `c_ulong` and `isize` 32 bits on wasm32 (ILP32) and 64 on x86_64 (LP64). The
extern-struct layouts are checked through stored values: `{ int, long, short }` (12 or 24
bytes), `{ char, long long, unsigned short, unsigned long }` (24 or 32 bytes; `long long` at
offset 8 on both) and `{ isize, usize }` (8 or 16). `long double` (`f128` on wasm32, `f80` on
x86_64) is translated (`ldAdd`, `ldV`) and its layout checked by `test_cli.py`; no theorem is
stated about it here, as `assurance/float-semantics.json` labels no wasm32 float target.
-/

namespace PointerWidth.CInts.V0_16_0.Proofs

open Zig PointerWidth.CInts.V0_16_0

/-! ## Checked increments: every C integer type, every profile -/

theorem charSucc_w32 (n : BitVec 8) : Wasm32.charSucc n = succSigned n := by
  simp only [Wasm32.charSucc, add_one_signed_eq (by decide : 2 ≤ 8)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem shortSucc_w32 (n : BitVec 16) : Wasm32.shortSucc n = succSigned n := by
  simp only [Wasm32.shortSucc, add_one_signed_eq (by decide : 2 ≤ 16)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem ushortSucc_w32 (n : BitVec 16) : Wasm32.ushortSucc n = succUnsigned n := by
  simp only [Wasm32.ushortSucc, add_one_unsigned_eq (by decide : 1 ≤ 16)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem intSucc_w32 (n : BitVec 32) : Wasm32.intSucc n = succSigned n := by
  simp only [Wasm32.intSucc, add_one_signed_eq (by decide : 2 ≤ 32)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem uintSucc_w32 (n : BitVec 32) : Wasm32.uintSucc n = succUnsigned n := by
  simp only [Wasm32.uintSucc, add_one_unsigned_eq (by decide : 1 ≤ 32)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem longSucc_w32 (n : BitVec 32) : Wasm32.longSucc n = succSigned n := by
  simp only [Wasm32.longSucc, add_one_signed_eq (by decide : 2 ≤ 32)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem ulongSucc_w32 (n : BitVec 32) : Wasm32.ulongSucc n = succUnsigned n := by
  simp only [Wasm32.ulongSucc, add_one_unsigned_eq (by decide : 1 ≤ 32)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem longlongSucc_w32 (n : BitVec 64) : Wasm32.longlongSucc n = succSigned n := by
  simp only [Wasm32.longlongSucc, add_one_signed_eq (by decide : 2 ≤ 64)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem ulonglongSucc_w32 (n : BitVec 64) : Wasm32.ulonglongSucc n = succUnsigned n := by
  simp only [Wasm32.ulonglongSucc, add_one_unsigned_eq (by decide : 1 ≤ 64)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem isizeSucc_w32 (n : BitVec 32) : Wasm32.isizeSucc n = succSigned n := by
  simp only [Wasm32.isizeSucc, add_one_signed_eq (by decide : 2 ≤ 32)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl

theorem charSucc_wasi (n : BitVec 8) : Wasi.charSucc n = succSigned n := by
  simp only [Wasi.charSucc, add_one_signed_eq (by decide : 2 ≤ 8)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem shortSucc_wasi (n : BitVec 16) : Wasi.shortSucc n = succSigned n := by
  simp only [Wasi.shortSucc, add_one_signed_eq (by decide : 2 ≤ 16)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem ushortSucc_wasi (n : BitVec 16) : Wasi.ushortSucc n = succUnsigned n := by
  simp only [Wasi.ushortSucc, add_one_unsigned_eq (by decide : 1 ≤ 16)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem intSucc_wasi (n : BitVec 32) : Wasi.intSucc n = succSigned n := by
  simp only [Wasi.intSucc, add_one_signed_eq (by decide : 2 ≤ 32)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem uintSucc_wasi (n : BitVec 32) : Wasi.uintSucc n = succUnsigned n := by
  simp only [Wasi.uintSucc, add_one_unsigned_eq (by decide : 1 ≤ 32)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem longSucc_wasi (n : BitVec 32) : Wasi.longSucc n = succSigned n := by
  simp only [Wasi.longSucc, add_one_signed_eq (by decide : 2 ≤ 32)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem ulongSucc_wasi (n : BitVec 32) : Wasi.ulongSucc n = succUnsigned n := by
  simp only [Wasi.ulongSucc, add_one_unsigned_eq (by decide : 1 ≤ 32)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem longlongSucc_wasi (n : BitVec 64) : Wasi.longlongSucc n = succSigned n := by
  simp only [Wasi.longlongSucc, add_one_signed_eq (by decide : 2 ≤ 64)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem ulonglongSucc_wasi (n : BitVec 64) : Wasi.ulonglongSucc n = succUnsigned n := by
  simp only [Wasi.ulonglongSucc, add_one_unsigned_eq (by decide : 1 ≤ 64)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem isizeSucc_wasi (n : BitVec 32) : Wasi.isizeSucc n = succSigned n := by
  simp only [Wasi.isizeSucc, add_one_signed_eq (by decide : 2 ≤ 32)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl

theorem charSucc_x64 (n : BitVec 8) : X64.charSucc n = succSigned n := by
  simp only [X64.charSucc, add_one_signed_eq (by decide : 2 ≤ 8)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem shortSucc_x64 (n : BitVec 16) : X64.shortSucc n = succSigned n := by
  simp only [X64.shortSucc, add_one_signed_eq (by decide : 2 ≤ 16)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem ushortSucc_x64 (n : BitVec 16) : X64.ushortSucc n = succUnsigned n := by
  simp only [X64.ushortSucc, add_one_unsigned_eq (by decide : 1 ≤ 16)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem intSucc_x64 (n : BitVec 32) : X64.intSucc n = succSigned n := by
  simp only [X64.intSucc, add_one_signed_eq (by decide : 2 ≤ 32)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem uintSucc_x64 (n : BitVec 32) : X64.uintSucc n = succUnsigned n := by
  simp only [X64.uintSucc, add_one_unsigned_eq (by decide : 1 ≤ 32)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem longSucc_x64 (n : BitVec 64) : X64.longSucc n = succSigned n := by
  simp only [X64.longSucc, add_one_signed_eq (by decide : 2 ≤ 64)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem ulongSucc_x64 (n : BitVec 64) : X64.ulongSucc n = succUnsigned n := by
  simp only [X64.ulongSucc, add_one_unsigned_eq (by decide : 1 ≤ 64)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem longlongSucc_x64 (n : BitVec 64) : X64.longlongSucc n = succSigned n := by
  simp only [X64.longlongSucc, add_one_signed_eq (by decide : 2 ≤ 64)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem ulonglongSucc_x64 (n : BitVec 64) : X64.ulonglongSucc n = succUnsigned n := by
  simp only [X64.ulonglongSucc, add_one_unsigned_eq (by decide : 1 ≤ 64)]; unfold succUnsigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem isizeSucc_x64 (n : BitVec 64) : X64.isizeSucc n = succSigned n := by
  simp only [X64.isizeSucc, add_one_signed_eq (by decide : 2 ≤ 64)]; unfold succSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl

/-- The boundaries: `c_long`'s and `c_ulong`'s maxima on wasm32 are ordinary values on x86_64;
`c_char` and `c_longlong` overflow at the same value on both. -/
theorem succ_boundary :
    (Wasm32.longSucc (BitVec.ofInt 32 (2 ^ 31 - 1))).run = some (.error .overflow) ∧
    (X64.longSucc (BitVec.ofInt 64 (2 ^ 31 - 1))).run = some (.ok (BitVec.ofInt 64 (2 ^ 31))) ∧
    (Wasm32.ulongSucc (BitVec.ofNat 32 (2 ^ 32 - 1))).run = some (.error .overflow) ∧
    (X64.ulongSucc (BitVec.ofNat 64 (2 ^ 32 - 1))).run = some (.ok (BitVec.ofNat 64 (2 ^ 32))) ∧
    (Wasm32.charSucc 127).run = some (.error .overflow) ∧
    (X64.charSucc 127).run = some (.error .overflow) ∧
    (Wasm32.longlongSucc (BitVec.ofInt 64 (2 ^ 63 - 1))).run = some (.error .overflow) ∧
    (X64.longlongSucc (BitVec.ofInt 64 (2 ^ 63 - 1))).run = some (.error .overflow) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Products, negation and conversions -/

theorem ulongMul_w32 (a b : BitVec 32) : Wasm32.ulongMul a b = pure (mulUnsignedOpt a b) := by
  simp only [Wasm32.ulongMul, Zig.mulWithOverflow, BitVec.umulOverflow, mulUnsignedOpt]
  by_cases h : 2 ^ 32 ≤ a.toNat * b.toNat <;> simp [h, StateT.run', bind, pure] <;> rfl
theorem ulongMul_wasi (a b : BitVec 32) : Wasi.ulongMul a b = pure (mulUnsignedOpt a b) := by
  simp only [Wasi.ulongMul, Zig.mulWithOverflow, BitVec.umulOverflow, mulUnsignedOpt]
  by_cases h : 2 ^ 32 ≤ a.toNat * b.toNat <;> simp [h, StateT.run', bind, pure] <;> rfl
theorem ulongMul_x64 (a b : BitVec 64) : X64.ulongMul a b = pure (mulUnsignedOpt a b) := by
  simp only [X64.ulongMul, Zig.mulWithOverflow, BitVec.umulOverflow, mulUnsignedOpt]
  by_cases h : 2 ^ 64 ≤ a.toNat * b.toNat <;> simp [h, StateT.run', bind, pure] <;> rfl

/-- `2 ^ 16 * 2 ^ 16` does not fit a 32-bit `c_ulong` only. -/
theorem ulongMul_boundary :
    (Wasm32.ulongMul (BitVec.ofNat 32 (2 ^ 16)) (BitVec.ofNat 32 (2 ^ 16))).run = some (.ok none) ∧
    (X64.ulongMul (BitVec.ofNat 64 (2 ^ 16)) (BitVec.ofNat 64 (2 ^ 16))).run =
      some (.ok (some (BitVec.ofNat 64 (2 ^ 32)))) := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem isizeNeg_w32 (n : BitVec 32) : Wasm32.isizeNeg n = negSigned n := by
  simp only [Wasm32.isizeNeg, sub_zero_signed_eq (by decide : 1 ≤ 32)]; unfold negSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem isizeNeg_wasi (n : BitVec 32) : Wasi.isizeNeg n = negSigned n := by
  simp only [Wasi.isizeNeg, sub_zero_signed_eq (by decide : 1 ≤ 32)]; unfold negSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl
theorem isizeNeg_x64 (n : BitVec 64) : X64.isizeNeg n = negSigned n := by
  simp only [X64.isizeNeg, sub_zero_signed_eq (by decide : 1 ≤ 64)]; unfold negSigned
  split <;> simp [StateT.run', bind, pure, throw, throwThe] <;> rfl

/-- `c_long` → `c_int`: the same width on wasm32, so the cast never fails. -/
theorem longToInt_w32 (n : BitVec 32) : Wasm32.longToInt n = pure n := by
  simp only [Wasm32.longToInt, intCast_signed_same (by decide : 1 ≤ 32)]; rfl
theorem longToInt_wasi (n : BitVec 32) : Wasi.longToInt n = pure n := by
  simp only [Wasi.longToInt, intCast_signed_same (by decide : 1 ≤ 32)]; rfl

/-- On x86_64 it is a checked truncation: an overflow outside `c_int`'s range. -/
theorem longToInt_x64 (n : BitVec 64) :
    X64.longToInt n = if -2 ^ 31 ≤ n.toInt ∧ n.toInt ≤ 2 ^ 31 - 1
      then pure (BitVec.ofInt 32 n.toInt) else throw .overflow := by
  by_cases h : (-2147483648 : Int) ≤ n.toInt ∧ n.toInt ≤ 2147483647 <;>
    simp [X64.longToInt, Zig.intCast, Zig.val, intLo, intHi, h, StateT.run', bind, pure, throw,
      throwThe] <;> rfl

theorem longToInt_boundary :
    (Wasm32.longToInt (BitVec.ofInt 32 (2 ^ 31 - 1))).run = some (.ok (BitVec.ofInt 32 (2 ^ 31 - 1))) ∧
    (X64.longToInt (BitVec.ofInt 64 (2 ^ 31))).run = some (.error .overflow) ∧
    (X64.longToInt (BitVec.ofInt 64 (-2 ^ 31))).run = some (.ok (BitVec.ofInt 32 (-2 ^ 31))) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- `c_int` → `c_long`: the identity on wasm32, a sign extension on x86_64. -/
theorem intToLong_w32 (n : BitVec 32) : Wasm32.intToLong n = pure n := rfl
theorem intToLong_wasi (n : BitVec 32) : Wasi.intToLong n = pure n := rfl
theorem intToLong_x64 (n : BitVec 32) : X64.intToLong n = pure (BitVec.ofInt 64 n.toInt) := by
  have hlo := BitVec.le_two_mul_toInt (x := n)
  have hhi := BitVec.two_mul_toInt_lt (x := n)
  have : (-9223372036854775808 : Int) ≤ n.toInt ∧ n.toInt ≤ 9223372036854775807 := by omega
  simp [X64.intToLong, Zig.intCast, Zig.val, intLo, intHi, this, StateT.run', bind, pure]
  rfl

theorem intToLong_boundary :
    (X64.intToLong (BitVec.ofInt 32 (-1))).run = some (.ok (BitVec.ofInt 64 (-1))) := by
  decide +kernel

/-- `@bitCast` `c_long` → `c_ulong` and the coercion `isize` → `c_long` keep the bits, at the
profile's width. -/
theorem longBits_w32 (n : BitVec 32) : Wasm32.longBits n = pure n := rfl
theorem longBits_wasi (n : BitVec 32) : Wasi.longBits n = pure n := rfl
theorem longBits_x64 (n : BitVec 64) : X64.longBits n = pure n := rfl
theorem longOfIsize_w32 (n : BitVec 32) : Wasm32.longOfIsize n = pure n := rfl
theorem longOfIsize_wasi (n : BitVec 32) : Wasi.longOfIsize n = pure n := rfl
theorem longOfIsize_x64 (n : BitVec 64) : X64.longOfIsize n = pure n := rfl

/-! ## Extern-struct layouts in memory -/

/-- A `long long` with distinct bytes: a field read at a wrong offset or width reads others. -/
def ll0 : BitVec 64 := 0x0102030405060708

/-- One block per struct: `Rec`, `Mixed`, `Sizes`. -/
def memW32 : Mem := Mem.ofGlobals .fresh [
  (Enc.encode ({ a := 1, b := 0xfffffffe, c := 0x8003 } : Wasm32.Rec), 4, .global),
  (Enc.encode ({ c := 0xff, ll := ll0, us := 0x1234, ul := 0xfffffffe } : Wasm32.Mixed), 8, .global),
  (Enc.encode ({ i := 0xffffffff, u := 0xfffffffd } : Wasm32.Sizes), 4, .global)]

def memWasi : Mem := Mem.ofGlobals .fresh [
  (Enc.encode ({ a := 1, b := 0xfffffffe, c := 0x8003 } : Wasi.Rec), 4, .global),
  (Enc.encode ({ c := 0xff, ll := ll0, us := 0x1234, ul := 0xfffffffe } : Wasi.Mixed), 8, .global),
  (Enc.encode ({ i := 0xffffffff, u := 0xfffffffd } : Wasi.Sizes), 4, .global)]

def memX64 : Mem := Mem.ofGlobals .fresh [
  (Enc.encode ({ a := 1, b := 0xfffffffffffffffe, c := 0x8003 } : X64.Rec), 8, .global),
  (Enc.encode ({ c := 0xff, ll := ll0, us := 0x1234, ul := 0xfffffffffffffffe } : X64.Mixed), 8,
    .global),
  (Enc.encode ({ i := 0xffffffffffffffff, u := 0xfffffffffffffffd } : X64.Sizes), 8, .global)]

/-- The sizes: `Rec` 12/24, `Mixed` 24/32, `Sizes` 8/16 bytes. -/
theorem layout_sizes :
    memW32.blocks.toList.map (·.bytes.size) = [12, 24, 8] ∧
    memWasi.blocks.toList.map (·.bytes.size) = [12, 24, 8] ∧
    memX64.blocks.toList.map (·.bytes.size) = [24, 32, 16] := by
  decide +kernel

/-- `long` at offset 4 (wasm32) or 8 (x86_64), the `short` after it at 8 or 16. -/
theorem rec_w32 :
    ((do pure (← Wasm32.recB ⟨some 0, 0⟩, ← Wasm32.recC ⟨some 0, 0⟩) : MemM _).run' memW32).run =
      some (.ok (0xfffffffe, 0x8003)) := by decide +kernel
theorem rec_wasi :
    ((do pure (← Wasi.recB ⟨some 0, 0⟩, ← Wasi.recC ⟨some 0, 0⟩) : MemM _).run' memWasi).run =
      some (.ok (0xfffffffe, 0x8003)) := by decide +kernel
theorem rec_x64 :
    ((do pure (← X64.recB ⟨some 0, 0⟩, ← X64.recC ⟨some 0, 0⟩) : MemM _).run' memX64).run =
      some (.ok (0xfffffffffffffffe, 0x8003)) := by decide +kernel

/-- `long long` at offset 8 on both; `unsigned long` at 20 (wasm32) or 24 (x86_64). -/
theorem mixed_w32 :
    ((do pure (← Wasm32.mixedLl ⟨some 1, 0⟩, ← Wasm32.mixedUl ⟨some 1, 0⟩) : MemM _).run'
      memW32).run = some (.ok (ll0, 0xfffffffe)) := by decide +kernel
theorem mixed_wasi :
    ((do pure (← Wasi.mixedLl ⟨some 1, 0⟩, ← Wasi.mixedUl ⟨some 1, 0⟩) : MemM _).run'
      memWasi).run = some (.ok (ll0, 0xfffffffe)) := by decide +kernel
theorem mixed_x64 :
    ((do pure (← X64.mixedLl ⟨some 1, 0⟩, ← X64.mixedUl ⟨some 1, 0⟩) : MemM _).run'
      memX64).run = some (.ok (ll0, 0xfffffffffffffffe)) := by decide +kernel

/-- A store to `us` (offset 16) leaves the `unsigned long` after it unchanged. -/
theorem setMixedUs_w32 :
    ((do Wasm32.setMixedUs ⟨some 1, 0⟩ 7
         pure (← load (BitVec 16) 2 ⟨some 1, 16⟩, ← Wasm32.mixedUl ⟨some 1, 0⟩) : MemM _).run'
      memW32).run = some (.ok (7, 0xfffffffe)) := by decide +kernel
theorem setMixedUs_wasi :
    ((do Wasi.setMixedUs ⟨some 1, 0⟩ 7
         pure (← load (BitVec 16) 2 ⟨some 1, 16⟩, ← Wasi.mixedUl ⟨some 1, 0⟩) : MemM _).run'
      memWasi).run = some (.ok (7, 0xfffffffe)) := by decide +kernel
theorem setMixedUs_x64 :
    ((do X64.setMixedUs ⟨some 1, 0⟩ 7
         pure (← load (BitVec 16) 2 ⟨some 1, 16⟩, ← X64.mixedUl ⟨some 1, 0⟩) : MemM _).run'
      memX64).run = some (.ok (7, 0xfffffffffffffffe)) := by decide +kernel

/-- `usize` at offset 4 (wasm32) or 8 (x86_64). -/
theorem sizesU_w32 : ((Wasm32.sizesU ⟨some 2, 0⟩).run' memW32).run = some (.ok 0xfffffffd) := by
  decide +kernel
theorem sizesU_wasi : ((Wasi.sizesU ⟨some 2, 0⟩).run' memWasi).run = some (.ok 0xfffffffd) := by
  decide +kernel
theorem sizesU_x64 :
    ((X64.sizesU ⟨some 2, 0⟩).run' memX64).run = some (.ok 0xfffffffffffffffd) := by
  decide +kernel

end PointerWidth.CInts.V0_16_0.Proofs
