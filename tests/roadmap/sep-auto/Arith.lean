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

end SepAuto.Arith
