import AggregateCasts.Gen
import ZigLean.ReprCast

/-!
# Zig ≤0.16 representation casts and optional pointers, on the retained translation

`AggregateCasts.Gen` is the translation of `air/0.16.0`, the patched 0.16.0 compiler's export
of `aggregate_casts.zig` (the casts of `probe.zig`); the 0.15.2 and 0.14.1 exports translate to
the same text apart from the profile header (`check.sh`). Each `@bitCast` of an array, `extern` struct or `extern` union
is `Zig.reprCast`: the source's memory bytes, padding bytes undefined, decoded as the
destination. A round trip holds when neither side has padding; a destination part that needs a
padding byte throws `.unspecified`. The optional-pointer casts use null = address 0 and
unwrapping requires non-null. `probe.zig`'s native output agrees on every defined byte
(`Model.lean`).
-/

open AggregateCasts Zig

namespace AggregateCastsClients

/-! ## No padding: round trips -/

theorem bytesToU32_roundtrip :
    (bytesToU32 #v[0x11, 0x22, 0x33, 0x44]).run = some (.ok 0x44332211) ∧
      (u32ToBytes 0x44332211).run = some (.ok #v[0x11, 0x22, 0x33, 0x44]) := by
  decide +kernel

theorem pair_roundtrip :
    (pairToU64 ⟨1, 2⟩).run = some (.ok 0x0000000200000001) ∧
      (u64ToPair 0x0000000200000001).run = some (.ok ⟨1, 2⟩) := by
  decide +kernel

/-- `[4]u8 → u32` is the generic cast, so the generic round trip applies under its condition
(the two encodings are the same bytes). -/
theorem bytesToU32_generic (x : Vector (BitVec 8) 4) (y : BitVec 32)
    (h : Enc.encode y = Enc.encode x) :
    bytesToU32 x = pure y ∧ u32ToBytes y = pure x := by
  haveI := lawfulEnc_vector (α := BitVec 8) 4
  obtain ⟨h1, h2⟩ := reprCast_roundtrip h
  constructor
  · simp only [bytesToU32, h1]; rfl
  · simp only [u32ToBytes, h2]; rfl

/-! ## Padding -/

/-- `[8]u8 → Padded` (`extern struct { a: u8, b: u32 }`): bytes 1..3 fall in padding and are
dropped (native: `a = 01`, `b = 05 06 07 08`). -/
theorem bytesToPadded_val :
    (bytesToPadded #v[1, 2, 3, 4, 5, 6, 7, 8]).run = some (.ok ⟨1, 0x08070605⟩) := by
  decide +kernel

/-- `Padded → [8]u8`: items 1..3 are padding bytes, so the array is not defined. The round trip
`[8]u8 → Padded → [8]u8` therefore fails. -/
theorem paddedToBytes_padding :
    (paddedToBytes ⟨1, 0x05040302⟩).run = some (.error .unspecified) ∧
      (bytesToPadded #v[1, 2, 3, 4, 5, 6, 7, 8] >>= paddedToBytes).run =
        some (.error .unspecified) := by
  decide +kernel

/-- `[2]u24 → u56`: byte 3 is item 0's padding. -/
theorem u24x2ToU56_padding :
    (u24x2ToU56 #v[0x112233, 0x445566]).run = some (.error .unspecified) := by
  decide +kernel

/-- `u56 → [2]u24` puts byte 3 into item 0's padding, so it is lost, and casting back fails. -/
theorem u56ToU24x2_lossy :
    (u56ToU24x2 0x44556600112233).run = some (.ok #v[0x112233, 0x445566]) ∧
      (u56ToU24x2 0x44556600112233 >>= u24x2ToU56).run = some (.error .unspecified) := by
  decide +kernel

/-! ## `extern` unions keep their bytes -/

theorem u32ToWord_fields :
    (u32ToWord 0x44332211 >>= Word.get_bytes).run = some (.ok #v[0x11, 0x22, 0x33, 0x44]) ∧
      (u32ToWord 0x44332211 >>= Word.get_int).run = some (.ok 0x44332211) := by
  decide +kernel

/-- `Short` (`extern union { a: u8, b: u32 }`) made from `a` has 3 undefined bytes: its `u32`
is not defined. Made from `b`, it is. -/
theorem shortToU32_padding :
    (shortToU32 ⟨Raw.init 4 (0x11 : BitVec 8)⟩).run = some (.error .unspecified) ∧
      (shortToU32 ⟨Raw.init 4 (0x11 : BitVec 32)⟩).run = some (.ok 0x11) := by
  decide +kernel

/-! ## Optional pointers: null = address 0, unwrap requires non-null -/

theorem optAddr_null (m : Mem) : (optAddr none).run m = pure (0, m) := rfl

theorem optFromAddr_zero (m : Mem) : (optFromAddr 0).run m = pure (none, m) := rfl

/-- The compiler's `@ptrFromInt` to `?*u32` checks alignment first (`bit_and 3`, then the
`incorrectAlignment` panic), which the earlier hand-written AIR lacked: a misaligned address
panics, a multiple of 4 does not. -/
theorem optFromAddr_misaligned (m : Mem) : (optFromAddr 1).run m = throw .panic := rfl

theorem optUnwrap_null (m : Mem) : (optUnwrap none).run m = throw .panic := rfl

/-- The compiler's unwrap (`@ptrCast` of `?*u32` to `*u32`) tests the address first
(`cmp_neq addr 0`, then the `castToNull` panic). A pointer whose address is not 0 mod 2^64
passes the test and is returned unchanged. -/
theorem optUnwrap_some (p : Ptr) (m : Mem) (a : Int)
    (hp : (ptrAddr p).run m = pure (a, m)) (ha : BitVec.ofInt 64 a ≠ 0#64) :
    (optUnwrap (some p)).run m = pure (p, m) := by
  have ha' : (BitVec.ofInt 64 a = 0#64) = False := eq_false ha
  simp [optUnwrap, Zig.callM, Zig.optPtrAddr, hp, Zig.optPtrUnwrap, ha']

theorem ptrWrap_some (p : Ptr) (m : Mem) : (ptrWrap p).run m = pure (some p, m) := rfl

/-- Wrap then unwrap is the pointer, for a pointer with a nonzero address. -/
theorem wrap_unwrap (p : Ptr) (m : Mem) (a : Int)
    (hp : (ptrAddr p).run m = pure (a, m)) (ha : BitVec.ofInt 64 a ≠ 0#64) :
    (ptrWrap p >>= optUnwrap).run m = pure (p, m) := by
  simp [StateT.run_bind, ptrWrap_some, optUnwrap_some p m a hp ha]

end AggregateCastsClients
