import ZigLean.Mem.Witness
import ZigLean.Bit
import ZigLean.Range
import ZigLean.Mem.ErrWidthLemmas
import ZigLean.Mem.NullLemmas
import ZigLean.ReprCast

/-!
# Non-vacuity witnesses: integer, encoding and memory lemmas

Concrete arguments for the premises of the exact-result lemmas of `ZigLean/Bit.lean`,
`ZigLean/Lemmas.lean`, `ZigLean/Range.lean`, `ZigLean/Mem/*Lemmas.lean`, `ZigLean/VecMem.lean`
and `ZigLean/ReprCast.lean` (`docs/claim-strength.md`). They live here, not next to each lemma,
because several of those modules are imported by generated code (`ZigLean.lean`), which must
not import the witness commands, and the rest sit below the concrete memories of
`ZigLean/Mem/Witness.lean`.
-/

namespace Zig.Witness

/-- The four bytes of `0 : u32`, the payload of the memory witnesses below. -/
abbrev w32 : Array Byte := Enc.encode (0 : BitVec 32)

theorem w32_size : w32.size = 4 := LawfulEnc.size_encode _

/-- The `u32` access at `p0` of `mem1 w32`. -/
theorem w32_access : (mem1 w32).access (p0.add 0) (Enc.size (BitVec 32)) 4 = pure (0, blk w32, 0) :=
  mem1_access (by rw [w32_size]; decide) (by decide)

/-- Two live blocks with the bytes `bs`: `0` at 4096 and `1` at 8192. -/
def mem2 (bs : Array Byte) : Mem :=
  { blocks := #[blk bs, { blk bs with addr := 8192 }], nextAddr := 8192 + bs.size + 1 }

theorem w32_access₁ :
    (mem2 w32).access (p0.add 0) (Enc.size (BitVec 32)) 4 = pure (0, blk w32, 0) := by
  with_unfolding_all rfl

theorem w32_access₂ : (mem2 w32).access ⟨some 1, 0⟩ (Enc.size (BitVec 32)) 4 =
    pure (1, { blk w32 with addr := 8192 }, 0) := by
  with_unfolding_all rfl

theorem mem1_single (bs : Array Byte) (kind : BlockKind) : (mem1 bs kind).SingleThread :=
  singleThread_empty rfl Nat.zero_lt_one

/-- A declared error domain with the one error `A`. -/
def domA : ErrorDomain := ⟨#["A"], by decide, by decide⟩

/-- The error table with the one error `A` (code 1). -/
def tableA : ErrorTable := ⟨#["A"], by decide⟩

/-! ## `ZigLean/Bit.lean` -/

nonvacuity_witness shlExact_of_noOverflow := ⟨8, 8, false, 1, 0, by decide, trivial⟩
nonvacuity_witness shlWithOverflow_noOverflow := ⟨8, 8, false, 1, 0, by decide, by decide, trivial⟩
nonvacuity_witness shlWithOverflow_overflow := ⟨8, 8, false, 128, 1, by decide, by decide, trivial⟩
nonvacuity_witness shlWithOverflow_result := ⟨8, 8, false, 1, 0, by decide, trivial⟩
nonvacuity_witness shlWithOverflow_valid := ⟨8, 8, false, 1, 0, Or.inl (by decide), trivial⟩
nonvacuity_witness shlWithOverflow_zero_operand := ⟨8, 8, false, 0, Or.inl (by decide), trivial⟩

/-! ## `ZigLean/Lemmas.lean`, `ZigLean/Range.lean` -/

nonvacuity_witness index_lt := ⟨Unit, #[()], 0, by decide, trivial⟩
nonvacuity_witness intCast_unsigned_widen := ⟨8, 0, 16, by decide, trivial⟩
nonvacuity_witness add_unsigned_of_lt := ⟨8, 1, 2, by decide, trivial⟩
nonvacuity_witness intCast_unsigned_of_lt := ⟨16, 8, 1, by decide, trivial⟩
nonvacuity_witness mul_unsigned_of_lt := ⟨8, 2, 3, by decide, trivial⟩
nonvacuity_witness sub_unsigned_of_le := ⟨8, 3, 2, by decide, trivial⟩

/-! ## `ZigLean/Mem/Lemmas.lean` -/

nonvacuity_witness LawfulEnc.decode_encode := ⟨BitVec 32, _, inferInstance, 0, trivial⟩
nonvacuity_witness Raw.get_init := ⟨BitVec 32, _, inferInstance, 4, 0, by decide +kernel, trivial⟩
nonvacuity_witness Raw.get_set :=
  ⟨BitVec 32, _, inferInstance, 4, Vector.replicate 4 .undef, 0, by decide +kernel, trivial⟩

nonvacuity_witness access_of :=
  ⟨mem1 w32, p0, 4, 4, 0, blk w32, rfl, rfl, rfl, by decide, by simp [blk, w32_size, p0],
    by decide, trivial⟩

nonvacuity_witness access_write_other :=
  ⟨mem1 w32, p0.add 0, 4, 4, #[], 1, 0, blk w32, blk w32, 0, 0, w32_access, by decide, trivial⟩

nonvacuity_witness access_write_same :=
  ⟨mem1 w32, p0.add 0, p0.add 0, 4, 4, 4, w32, 0, blk w32, 0, 0, by rw [w32_size]; exact w32_access,
    w32_access, trivial⟩

nonvacuity_witness access_store_same :=
  ⟨BitVec 32, inferInstance, inferInstance, mem1 w32, p0.add 0, p0.add 0, 4, 4, 4, 0, blk w32, 0, 0,
    0, w32_access, w32_access, trivial⟩

nonvacuity_witness access_store_other :=
  ⟨BitVec 32, inferInstance, mem2 w32, p0.add 0, ⟨some 1, 0⟩, 4, 4, 4, 0, 1, blk w32,
    { blk w32 with addr := 8192 }, 0, 0, 0, w32_access₁, w32_access₂, by decide, trivial⟩

nonvacuity_witness load_run :=
  ⟨BitVec 32, inferInstance, mem1 w32, p0.add 0, 4, 0, blk w32, 0, 0, w32_access,
    by with_unfolding_all rfl, mem1_noRace w32 .heap _ _ _ _, trivial⟩

nonvacuity_witness load_store_same :=
  ⟨BitVec 32, inferInstance, inferInstance, mem1 w32, p0.add 0, 4, 4, 0, blk w32, 0, 0, w32_access,
    w32_access, mem1_noRace w32 .heap _ _ _ _, trivial⟩

nonvacuity_witness load_store_other :=
  ⟨BitVec 32, BitVec 32, inferInstance, inferInstance, inferInstance, mem2 w32, p0.add 0, ⟨some 1, 0⟩,
    4, 4, 0, 1, blk w32, { blk w32 with addr := 8192 }, 0, 0, 0, 0, w32_access₁, w32_access₂,
    Or.inl (by decide), by with_unfolding_all rfl,
    noRace_of_singleThread (singleThread_empty rfl Nat.zero_lt_one) _ _ _ _, trivial⟩

nonvacuity_witness loadBytes_run :=
  ⟨mem1 w32, p0.add 0, 4, 4, 0, blk w32, 0, .read, w32_access, mem1_noRace w32 .heap _ _ _ _, trivial⟩

nonvacuity_witness loadDiscardBytes_run :=
  ⟨mem1 w32, p0.add 0, 4, 4, 0, blk w32, 0, w32_access, mem1_noRace w32 .heap _ _ _ _, trivial⟩

nonvacuity_witness storeBytes_run :=
  ⟨mem1 w32, p0.add 0, 4, w32, 0, blk w32, 0, .write, by rw [w32_size]; exact w32_access,
    by decide, mem1_noRace w32 .heap _ _ _ _, trivial⟩

nonvacuity_witness store_run :=
  ⟨BitVec 32, inferInstance, inferInstance, mem1 w32, p0.add 0, 4, 0, blk w32, 0, 0, w32_access,
    by decide, mem1_noRace w32 .heap _ _ _ _, trivial⟩

nonvacuity_witness recordAccess_run := ⟨mem1 w32, 0, 0, 4, .read, mem1_noRace w32 .heap _ _ _ _, trivial⟩

nonvacuity_witness errorEnc_roundtrip := ⟨domA, "A", by decide +kernel, trivial⟩
nonvacuity_witness optionalErrorEnc_roundtrip := ⟨domA, none, (fun _ h => by cases h), trivial⟩
nonvacuity_witness errUnion_decode_setPayload :=
  ⟨BitVec 32, inferInstance, inferInstance, Array.replicate 8 (.int 0), 0, by decide +kernel,
    by with_unfolding_all rfl, trivial⟩

/-! ## `ZigLean/Mem/ErrWidthLemmas.lean` -/

nonvacuity_witness errOfBytesW_errBytesW := ⟨16, by decide, none, trivial⟩
nonvacuity_witness errOfBytesW_of_extract :=
  ⟨16, by decide, errBytesW 16 none, none, by decide +kernel, trivial⟩
nonvacuity_witness errorCastW_roundtrip := ⟨domA, domA, fun _ h => h, "A", by decide +kernel, trivial⟩
nonvacuity_witness errorCodeOfNat_in_range := ⟨8, 1, by decide, trivial⟩
nonvacuity_witness errorEncW_roundtrip := ⟨16, by decide, domA, "A", by decide +kernel, trivial⟩
nonvacuity_witness optionalErrorEncW_roundtrip :=
  ⟨16, by decide, domA, none, (fun _ h => by cases h), trivial⟩
nonvacuity_witness errorFromIntW_intFromErrorW :=
  ⟨16, tableA, by unfold ErrorTable.fits; decide, "A", by decide +kernel, trivial⟩
nonvacuity_witness intFromErrorW_errorFromIntW :=
  ⟨16, tableA, by unfold ErrorTable.fits; decide, 1, "A", by with_unfolding_all rfl, trivial⟩
nonvacuity_witness load_store_same_of :=
  ⟨BitVec 32, inferInstance, mem1 w32, p0.add 0, 4, 4, 0, blk w32, 0, 0,
    LawfulEnc.size_encode _, LawfulEnc.decode_encode _, w32_access, w32_access,
    mem1_noRace w32 .heap _ _ _ _, trivial⟩

/-! ## `ZigLean/VecMem.lean`, `ZigLean/ReprCast.lean` -/

/-- The bytes of a vector of four `u8`. -/
abbrev v8x4 : Array Byte := Enc.encode (Vec.splat (0 : BitVec 8) : Vec (BitVec 8) 4)

theorem v8x4_access : (mem1 v8x4).access (p0.add 0) (Enc.size (Vec (BitVec 8) 4)) 1 =
    pure (0, blk v8x4, 0) :=
  mem1_access (by rw [LawfulEnc.size_encode]; exact Nat.le_refl _) (by decide)

nonvacuity_witness Vec.load_storeLane :=
  ⟨BitVec 8, 4, inferInstance, inferInstance, mem1 v8x4, p0.add 0, 1, 0, blk v8x4, 0,
    Vec.splat 0, 0, 1, v8x4_access,
    noRace_write.mpr (noRace_of_singleThread
      (singleThread_recordAt (singleThread_recordAt (mem1_single _ _) _ _ _ _) _ _ _ _) _ _ _ _),
    trivial⟩

nonvacuity_witness Vec.storeLane_run :=
  ⟨BitVec 8, 4, inferInstance, inferInstance, mem1 v8x4, p0.add 0, 1, 0, blk v8x4, 0,
    Vec.splat 0, 0, 1, v8x4_access, by with_unfolding_all rfl, by decide,
    mem1_noRace v8x4 .heap _ _ _ _,
    noRace_of_singleThread (singleThread_recordAt (mem1_single _ _) _ _ _ _) _ _ _ _, trivial⟩

nonvacuity_witness intOfBytes_of_extract := ⟨8, 0, intBytes (0 : BitVec 8), by decide +kernel, trivial⟩
nonvacuity_witness foldr_intBytes := ⟨8, 0, 0, 1, by decide, trivial⟩

nonvacuity_witness reprCast_of_encode_eq :=
  ⟨BitVec 32, BitVec 32, inferInstance, inferInstance, inferInstance, 0, 0, rfl, trivial⟩
nonvacuity_witness reprCast_self := ⟨BitVec 32, inferInstance, inferInstance, 0, trivial⟩
nonvacuity_witness list_mapM_pure_of :=
  ⟨Unit, Unit, fun _ => pure (), fun _ => (), [], by simp, trivial⟩

/-! ## `ZigLean/Mem/NullLemmas.lean` -/

theorem p0_addr : (ptrAddr (p0.add 0)).run (mem1 w32) = pure (4096, mem1 w32) := by
  with_unfolding_all rfl

theorem undef8_access : (mem1 (Array.replicate 8 .undef)).access (p0.add 0) 8 8 =
    pure (0, blk (Array.replicate 8 .undef), 0) :=
  mem1_access (by simp) (by decide)

nonvacuity_witness load_store_null :=
  ⟨mem1 (Array.replicate 8 .undef), p0.add 0, 8, 8, 0, blk (Array.replicate 8 .undef), 0,
    undef8_access, undef8_access, mem1_noRace (Array.replicate 8 .undef) .heap _ _ _ _, trivial⟩
nonvacuity_witness ptrIsNull_nonzero := ⟨mem1 w32, p0.add 0, 4096, p0_addr, by decide, trivial⟩
nonvacuity_witness ptrOfOptional_toOptional := ⟨mem1 w32, p0.add 0, 4096, p0_addr, by decide, trivial⟩
nonvacuity_witness ptrProjectNullable_ok :=
  ⟨mem1 w32, p0.add 0, 4096, id, p0_addr, by decide, trivial⟩

end Zig.Witness
