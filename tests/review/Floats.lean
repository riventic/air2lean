import ZigLean.Float

/-! Conversion regressions for the x86_64-linux LLVM baseline target. The source helpers
have the same relevant algorithms in Zig 0.14.1, 0.15.2 and 0.16.0. Results below were
cross-checked against stock Zig 0.15.2; NaN checks assert the class, not payload bits. -/

namespace FloatReview

private def f80 (s : Bool) (exp frac : Nat) : Zig.F80 :=
  Zig.Float.pack .f80 s exp frac

private def f128 (s : Bool) (exp frac : Nat) : Zig.F128 :=
  Zig.Float.pack .f128 s exp frac

private def resultEq {α : Type} [DecidableEq α] (r : Zig.Result α)
    (expected : Except Zig.Error α) : Bool :=
  match r.run, expected with
  | some (.ok a), .ok b => decide (a = b)
  | some (.error a), .error b => decide (a = b)
  | _, _ => false

private def resultNaN {fmt : Zig.FloatFmt} (r : Zig.Result (Zig.Float fmt)) : Bool :=
  match r.run with
  | some (.ok x) => x.isNaN
  | _ => false

-- Noncanonical f80 encodings cannot silently become a different f128 value/class.
example : resultEq (Zig.Float.convChk .f128 (f80 false 0 (2 ^ 63))) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convRtChk .f128 (f80 true 0 (2 ^ 63 + 1))) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convChk .f128 (f80 false 1 1)) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convRtChk .f128 (f80 true 0x7fff 0)) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convChk .f128 (f80 false 1 (2 ^ 63))) (.ok (f128 false 1 0)) = true := by native_decide
example : resultEq (Zig.Float.convChk .f128 (f80 false 0 1)) (.ok (f128 false 0 (2 ^ 49))) = true := by native_decide

-- __truncxfhf2 can read an invalid encoding as finite or infinite. Both modes
-- reject these encodings before either the model or the software port runs.
example : resultEq (Zig.Float.convChk .f16 (f80 false 0x3fff 0)) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convRtChk .f16 (f80 true 0x3fff 0)) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convChk .f16 (f80 false 1 1)) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convRtChk .f16 (f80 true 1 1)) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convChk .f16 (f80 false 0x7fff 0)) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convRtChk .f16 (f80 true 0x7fff 1)) (.error .unspecified) = true := by native_decide
-- Pseudo-denormals retain their class and underflow to signed zero in f16.
example : resultEq (Zig.Float.convChk .f16 (f80 false 0 (2 ^ 63))) (.ok (Zig.Float.zero false)) = true := by native_decide
example : resultEq (Zig.Float.convRtChk .f16 (f80 true 0 (2 ^ 64 - 1))) (.ok (Zig.Float.zero true)) = true := by native_decide

-- A low signaling-NaN payload vanishes in __trunctfxf2. Its first surviving bit
-- and the quiet bit must still produce a NaN without being unnecessarily guarded.
example : resultEq (Zig.Float.convChk .f80 (f128 false 0x7fff 1)) (.error .unspecified) = true := by native_decide
example : resultEq (Zig.Float.convRtChk .f80 (f128 true 0x7fff (2 ^ 49 - 1))) (.error .unspecified) = true := by native_decide
example : resultNaN (Zig.Float.convChk .f80 (f128 false 0x7fff (2 ^ 49))) = true := by native_decide
example : resultNaN (Zig.Float.convRtChk .f80 (f128 true 0x7fff (2 ^ 111))) = true := by native_decide
example : resultEq (Zig.Float.convChk .f80 (f128 false 0x7fff 0)) (.ok (Zig.Float.inf false)) = true := by native_decide

-- IEEE conversion remains correctly rounded; compiler-rt follows the source's
-- cleared integer bit and wrapping sticky-bit test near the f16 subnormal range.
example : (Zig.Float.conv .f16 (f80 false 16368 (2 ^ 63))).bits.toNat = 0x0200 := by native_decide
example : (Zig.Float.convRt .f16 (f80 false 16368 (2 ^ 63))).bits.toNat = 0 := by native_decide
example : (Zig.Float.convRt .f16 (f80 true 16368 (2 ^ 63))).bits.toNat = 0x8000 := by native_decide
example : (Zig.Float.convRt .f16 (f80 false 16368 (2 ^ 63 + 2 ^ 52))).bits.toNat = 1 := by native_decide
example : (Zig.Float.convRt .f16 (f80 false 16368 (2 ^ 64 - 1))).bits.toNat = 0x0400 := by native_decide
example : (Zig.Float.convRt .f16 (f80 false 16369 (2 ^ 63))).bits.toNat = 0x0400 := by native_decide
example : (Zig.Float.convRt .f16 (f80 false 16369 (2 ^ 63 + 2 ^ 52))).bits.toNat = 0x0400 := by native_decide
example : (Zig.Float.convRt .f16 (f80 false 16369 (2 ^ 63 + 2 ^ 52 + 1))).bits.toNat = 0x0401 := by native_decide
example : (Zig.Float.convRt .f16 (f80 false 16369 (2 ^ 63 + 3 * 2 ^ 52))).bits.toNat = 0x0402 := by native_decide
example : (Zig.Float.convRt .f16 (f80 true 16304 (2 ^ 64 - 1))).bits.toNat = 0x8000 := by native_decide
example : (Zig.Float.convRt .f16 (f80 true 16399 (2 ^ 63))).bits.toNat = 0xfc00 := by native_decide
example : (Zig.Float.convRt .f16 (f80 false 16398 (2 ^ 64 - 1))).bits.toNat = 0x7c00 := by native_decide
example : (Zig.Float.convRt .f16 (Zig.Float.zero (fmt := .f80) true)).bits.toNat = 0x8000 := by native_decide
example : (Zig.Float.convRt .f16 (Zig.Float.nan (fmt := .f80))).isNaN = true := by native_decide

-- The new wrappers forward unaffected formats and signed zero unchanged.
example : resultEq (Zig.Float.convRtChk .f80 (f128 true 0 0)) (.ok (Zig.Float.zero true)) = true := by native_decide
example : resultEq (Zig.Float.convChk .f16 (f80 false 16368 (2 ^ 63))) (.ok (Zig.Float.ofBits (fmt := .f16) 0x0200#16)) = true := by native_decide
example : resultEq (Zig.Float.convRtChk .f16 (f80 false 16368 (2 ^ 63))) (.ok (Zig.Float.zero false)) = true := by native_decide

-- __multf3's limb multiply loses a carry for these significands. IEEE multiplication
-- retains its correctly-rounded result; the target port reproduces the missing carry.
example : (Zig.Float.mulRt (f128 false 0x401d (2 ^ 112 - 1))
    (f128 false 0x401d (2 ^ 112 - 1))).bits.toNat =
    0x403cfffffffffffffffffffffffffffd := by native_decide
example : (Zig.Float.mul (f128 false 0x401d (2 ^ 112 - 1))
    (f128 false 0x401d (2 ^ 112 - 1))).bits.toNat =
    0x403cfffffffffffffffffffffffffffe := by native_decide
example : (Zig.Float.mulRt (f128 false 0x401e (2 ^ 112 - 1))
    (f128 false 0x401e (2 ^ 112 - 1))).bits.toNat =
    0x403efffffffffffffffffffffffffffd := by native_decide
example : (Zig.Float.mulRt (f128 false 0x403d (2 ^ 112 - 1))
    (f128 false 0x403d (2 ^ 112 - 1))).bits.toNat =
    0x407cfffffffffffffffffffffffffffd := by native_decide
example : (Zig.Float.mulRt (f128 true 0x403e (2 ^ 112 - 1))
    (f128 false 0x403e (2 ^ 112 - 1))).bits.toNat =
    0xc07efffffffffffffffffffffffffffd := by native_decide
example : (Zig.Float.fmaRt (f128 false 0x401d (2 ^ 112 - 1))
    (f128 false 0x401d (2 ^ 112 - 1)) (Zig.Float.zero false)).bits.toNat =
    0x403cfffffffffffffffffffffffffffd := by native_decide
example : Zig.Float.mulRt (f128 false 1 0) (f128 false 0x3ffe 0) =
    f128 false 0 (2 ^ 111) := by native_decide
example : Zig.Float.mulRt (f128 false 0 1) (f128 false 0x3fff 0) =
    f128 false 0 1 := by native_decide
example : Zig.Float.mulRt (f128 false 0 1) (f128 false 0x3ffe 0) =
    (Zig.Float.zero false) := by native_decide
example : Zig.Float.mulRt (f128 true 0x7ffe (2 ^ 112 - 1)) (f128 false 0x4000 0) =
    (Zig.Float.inf true) := by native_decide
example : (Zig.Float.mulRt (Zig.Float.zero false) (Zig.Float.inf (fmt := .f128) false)).isNaN = true := by native_decide

-- A remainder equal to its numerator keeps the original representation. __fmodx's
-- early comparison also uses the raw encoding, which can disagree with numeric order.
example : Zig.Float.rem (f80 false 0 (2 ^ 63)) (f80 false 0x3fff (2 ^ 63)) =
    f80 false 0 (2 ^ 63) := by native_decide
example : resultEq (Zig.Float.remRtChk (f80 false 0 (2 ^ 63)) (f80 false 0x3fff (2 ^ 63)))
    (.ok (f80 false 0 (2 ^ 63))) = true := by native_decide
example : resultEq (Zig.Float.modRtChk (f80 false 0 (2 ^ 63)) (f80 false 0x3fff (2 ^ 63)))
    (.ok (f80 false 0 (2 ^ 63))) = true := by native_decide
example : Zig.Float.rem (f80 false 0 (2 ^ 63 + 1)) (f80 false 1 (2 ^ 63)) =
    f80 false 0 1 := by native_decide
example : Zig.Float.remRt (f80 false 0 (2 ^ 63 + 1)) (f80 false 1 (2 ^ 63)) =
    f80 false 0 (2 ^ 63 + 1) := by native_decide
example : Zig.Float.remRt (f80 true 0 (2 ^ 63 + 1)) (f80 false 1 (2 ^ 63)) =
    f80 true 0 (2 ^ 63 + 1) := by native_decide

-- Legacy f80 floor/ceil go through __extendxftf2. A zero-fraction pseudo-denormal
-- becomes signed zero there; 0.16.0's direct f80 floor/ceil use its numeric value.
example : resultEq (Zig.Float.ceilRtLegacyChk (f80 false 0 (2 ^ 63)))
    (.ok (Zig.Float.zero false)) = true := by native_decide
example : resultEq (Zig.Float.floorRtLegacyChk (f80 true 0 (2 ^ 63)))
    (.ok (Zig.Float.zero true)) = true := by native_decide
example : resultEq (Zig.Float.ceilChk (f80 false 0 (2 ^ 63)))
    (.ok (f80 false 0x3fff (2 ^ 63))) = true := by native_decide
example : resultEq (Zig.Float.floorChk (f80 true 0 (2 ^ 63)))
    (.ok (f80 true 0x3fff (2 ^ 63))) = true := by native_decide
example : resultEq (Zig.Float.ceilRtLegacyChk (f80 false 0 (2 ^ 63 + 1)))
    (.ok (f80 false 0x3fff (2 ^ 63))) = true := by native_decide

end FloatReview
