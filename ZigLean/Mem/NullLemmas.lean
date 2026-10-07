import ZigLean.Mem.Lemmas
import ZigLean.Mem.Null

/-!
# Proof rules for stored and projected C/allowzero pointers (L05)

Proof-only: this module imports `ZigLean.Mem.Lemmas`, so it stays out of the `ZigLean`
runtime umbrella (as `ZigLean.VecMem`). The runtime operations are in `ZigLean/Mem/Null.lean`.

* `nullablePtrEnc_lawful`: the storage dictionary reads back what it writes, including
  address zero, so the generic `load_store_same`/`store_run` rules apply to stored C pointers.
* `nullablePtrEnc_encode_eq_optional`: a stored C pointer has exactly the bytes of the
  ordinary optional pointer that `ptrToOptional` gives; null is eight zero bytes.
* `nullablePtrEnc_decode_zero`: zero bytes read as `Ptr.null` (no allocation is invented).
* `load_store_null`: storing null and loading it back gives null; the access premises are the
  usual ones for the *storage* location, never for address zero.
* `ptrProjectNullable_ok`/`projected_access_block`: a projection from a nonnull base is the
  plain offset; an access through any projection succeeds only inside a live block of the
  base's own provenance, so a projection never acquires an allocation.
-/

namespace Zig

private theorem finRange8 : Array.finRange 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem nullablePtrEnc_size : nullablePtrEnc.size = 8 := rfl

theorem nullablePtrEnc_encode_def (p : Ptr) : nullablePtrEnc.encode p =
    if p = Ptr.null then Array.replicate 8 (.int 0) else Enc.encode p := rfl

theorem nullablePtrEnc_decode_def (bs : Array Byte) : nullablePtrEnc.decode bs =
    if bs.extract 0 8 == Array.replicate 8 (.int 0) then pure Ptr.null else Enc.decode bs := rfl

theorem nullablePtrEnc_size_encode (p : Ptr) :
    (nullablePtrEnc.encode p).size = nullablePtrEnc.size := by
  rw [nullablePtrEnc_encode_def, nullablePtrEnc_size]
  split <;> simp [Enc.encode]

theorem nullablePtrEnc_decode_encode (p : Ptr) :
    nullablePtrEnc.decode (nullablePtrEnc.encode p) = pure p := by
  rw [nullablePtrEnc_encode_def, nullablePtrEnc_decode_def]
  by_cases h : p = Ptr.null
  · subst h; simp [pure, ExceptT.pure, ExceptT.mk]
  · have hx : ¬ ((Enc.encode p : Array Byte).extract 0 8 = Array.replicate 8 (.int 0)) := by
      intro he
      have := congrArg (·[0]?) he
      simp [Enc.encode, finRange8] at this
    simp only [h, ite_false, beq_iff_eq, hx]
    exact LawfulEnc.decode_encode p

/-- The C/allowzero storage dictionary is lawful: it reads back every pointer it writes. -/
theorem nullablePtrEnc_lawful : @LawfulEnc Ptr nullablePtrEnc :=
  @LawfulEnc.mk Ptr nullablePtrEnc nullablePtrEnc_size_encode nullablePtrEnc_decode_encode

/-- Stored C pointers and ordinary optional pointers share one byte representation:
address zero is `none`'s eight zero bytes; every other pointer is `some`'s fragments. -/
theorem nullablePtrEnc_encode_eq_optional (p : Ptr) :
    nullablePtrEnc.encode p = Enc.encode (if p = Ptr.null then none else some p : Option Ptr) := by
  rw [nullablePtrEnc_encode_def]
  by_cases h : p = Ptr.null <;> simp [h, Enc.encode]

/-- Eight zero bytes (from `@memset`, a zero-initialised global or a null `?*T`) read as
address zero, never as an allocation. -/
theorem nullablePtrEnc_decode_zero :
    nullablePtrEnc.decode (Array.replicate 8 (.int 0)) = pure Ptr.null := by
  rw [nullablePtrEnc_decode_def]
  simp [pure, ExceptT.pure, ExceptT.mk]

/-- After storing address zero through a valid storage location, a load of the same location
returns address zero. The access premises concern the storage location only. -/
theorem load_store_null {m : Mem} {p : Ptr} {a a' : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p 8 a = pure (b, blk, o)) (h' : m.access p 8 a' = pure (b, blk, o))
    (hnr : NoRace (m.write b blk o (nullablePtrEnc.encode Ptr.null)) b o 8 .read) :
    (@load Ptr nullablePtrEnc a' p).run (m.write b blk o (nullablePtrEnc.encode Ptr.null)) =
      pure (Ptr.null, (m.write b blk o (nullablePtrEnc.encode Ptr.null)).recordAt b o 8 .read) :=
  @load_store_same Ptr nullablePtrEnc nullablePtrEnc_lawful m p a a' b blk o Ptr.null h h' hnr

/-- A projection whose base address is nonzero is exactly the projected pointer; memory is
unchanged. -/
theorem ptrProjectNullable_ok {m : Mem} {p : Ptr} {addr : Int} (project : Ptr → Ptr)
    (ha : (ptrAddr p).run m = pure (addr, m)) (hz : addr ≠ 0) :
    (ptrProjectNullable p project).run m = pure (project p, m) := by
  have hn : (ptrIsNull p).run m = pure (false, m) := by
    simp only [ptrIsNull, StateT.run_bind, ha]
    simp [hz, pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, StateT.run,
      StateT.pure]
  simp only [ptrProjectNullable, StateT.run_bind, hn]
  simp [pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, StateT.run,
    StateT.pure]

/-- An access through any offset of `p` succeeds only inside a live block that is `p`'s own
provenance: a projection never acquires an allocation, in particular not at address zero. -/
theorem projected_access_block {m : Mem} {p : Ptr} {off : Int} {n a : Nat} {b : BlockId}
    {blk : Block} {o : Nat} (h : m.access (p.add off) n a = pure (b, blk, o)) :
    p.block = some b ∧ m.blocks[b]? = some blk ∧ blk.live := by
  obtain ⟨hb, hblk, hl, -⟩ := access_eq h
  exact ⟨hb, hblk, hl⟩

/-- A nonnull C pointer converted to an ordinary optional pointer and back is unchanged. -/
theorem ptrOfOptional_toOptional {m : Mem} {p : Ptr} {addr : Int}
    (ha : (ptrAddr p).run m = pure (addr, m)) (hz : addr ≠ 0) :
    (do pure (ptrOfOptional (← ptrToOptional p)) : MemM Ptr).run m = pure (p, m) := by
  have hn : (ptrIsNull p).run m = pure (false, m) := by
    simp only [ptrIsNull, StateT.run_bind, ha]
    simp [hz, pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, StateT.run,
      StateT.pure]
  simp only [ptrToOptional, StateT.run_bind, hn]
  simp [ptrOfOptional, pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont,
    StateT.run, StateT.pure]

end Zig
