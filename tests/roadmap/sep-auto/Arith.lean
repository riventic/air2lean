import ZigLean.Sep.Full.Auto

/-!
# `fsym_arith`: the arithmetic solver of `fsym` (`docs/proof-automation.md`)

Word arithmetic of generated code as natural numbers: alignment masks against symbolic powers of
two, overflow bits, shifts, no wrap-around where it cannot happen.
-/

namespace SepAuto.Arith

open Zig

/-- `std.mem.alignForward` on a 64-bit address (`(x + (a - 1)) & ~(a - 1)` with `a = 1 << k`):
a multiple of `2 ^ k`. -/
theorem alignForward_aligned (x : BitVec 64) (k : Nat) (hk : k < 64) (h : x.toNat + 2 ^ k < 2 ^ 64) :
    ((x + (Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)) &&&
      ~~~(Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)).toNat % 2 ^ k = 0 := by
  fsym_arith

/-- … and at most `2 ^ k - 1` above `x`. -/
theorem alignForward_bound (x : BitVec 64) (k : Nat) (hk : k < 64) (h : x.toNat + 2 ^ k < 2 ^ 64) :
    ((x + (Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)) &&&
      ~~~(Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)).toNat < x.toNat + 2 ^ k := by
  fsym_arith

/-- `std.math.isPowerOfTwo` of `1 << k`. -/
theorem isPowerOfTwo_shl (k : Nat) (hk : k < 64) :
    (Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) &&& (Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)) = 0 := by
  fsym_arith

/-- The overflow bit of `@addWithOverflow` is clear when the sum fits. -/
theorem add_no_overflow (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (Zig.addWithOverflow false a b).snd = 0#1 ∧ (Zig.addWithOverflow false a b).fst.toNat = a.toNat + b.toNat := by
  constructor <;> fsym_arith

/-! ## Range conversions (the scenarios of the retired `zig_range`) -/

/-- A sum that fits does not wrap. -/
theorem add_fits (a b : BitVec 8) (h : a.toNat + b.toNat < 200) : (a + b).toNat = a.toNat + b.toNat := by
  fsym_arith

/-- A difference below the minuend does not wrap. -/
theorem sub_fits (a b : BitVec 32) (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  fsym_arith

/-- A natural number below the width, through `Int`. -/
theorem ofInt_natCast (k : Nat) (h : k < 256) : (BitVec.ofInt 8 (k : Int)).toNat = k := by
  fsym_arith

open Zig.Full Zig.Full.FAssn in
/-- A narrowing unsigned `@intCast` of a value that fits succeeds and keeps the value. -/
theorem intCast_fits (P : FAssn) (a : BitVec 64) (h : a.toNat < 256) :
    FTotalTriple P (StateT.lift (Zig.intCast false false 8 a) : MemM (BitVec 8))
      (fun r => ⟪r.toNat = a.toNat⟫ ⋆ P) := by
  fsym

/-- A sum of at most `2 ^ 32` items of width 32 fits in 64 bits (a plain lemma). -/
theorem sum_fits (xs : List (BitVec 32)) (h : xs.length ≤ 2 ^ 32) : (xs.map BitVec.toNat).sum < 2 ^ 64 :=
  sum_toNat_lt (k := 32) xs h

set_option linter.unusedVariables false in
/-- Without a range premise the sum may wrap: nothing is proved. -/
example (a b : BitVec 8) : True := by
  fail_if_success
    have : (a + b).toNat = a.toNat + b.toNat := by fsym_arith
  trivial

open Zig.Full Zig.Full.FAssn in
set_option linter.unusedVariables false in
/-- Without a range premise a narrowing `@intCast` may panic: no step. -/
example (P : FAssn) (a : BitVec 64) : True := by
  fail_if_success
    have : FTotalTriple P (StateT.lift (Zig.intCast false false 8 a) : MemM (BitVec 8))
        (fun r => ⟪r.toNat = a.toNat⟫ ⋆ P) := by
      fsym
  trivial

end SepAuto.Arith
