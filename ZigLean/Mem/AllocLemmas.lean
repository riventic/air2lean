import ZigLean.Mem.Alloc
import ZigLean.Mem.Lemmas

/-!
# Facts about `rawAlloc` and `remapByteBuffer` (proof-only)

The failure decision of an allocation attempt (`Mem.allocDenied`) and `rawAlloc` unfolded into
its three outcomes (`rawAlloc_eq`); the byte remap's runs branch by branch
(`remapByteBuffer_default_run`, `_inPlace_throw`, `_inPlace_illegal`, `_inPlace_none`,
`_inPlace_run`). Both logics use them: the legacy rules (`ZigLean/Sep/Alloc.lean`)
and the full-state rules (`ZigLean/Sep/Full/Block.lean`). Proof-only: this module imports
`ZigLean.Mem.Lemmas`, so it stays out of the runtime umbrella.
-/

namespace Zig

/-- Every failure decision of `rawAlloc`: a fixed/legacy rule or the general oracle/budget. -/
def Mem.allocDenied (m : Mem) (n : Nat) : Prop :=
  (m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures) ∨
    m.oracleDenies n = true

/-- `rawAlloc` counts the attempt, then fails without changing the heap (by the failure
decision, or for want of room in the address space: `Mem.roomFor`) or allocates a block. -/
theorem rawAlloc_eq (m : Mem) (n align : Nat) [Decidable (m.allocDenied n)] :
    (rawAlloc n align).run m =
      if m.allocDenied n then pure (none, { m with allocs := m.allocs + 1 })
      else if m.roomFor n align then (some <$> alloc .heap n align).run { m with allocs := m.allocs + 1 }
      else pure (none, { m with allocs := m.allocs + 1 }) := by
  by_cases hc : m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures
  · simp only [show m.allocDenied n from .inl hc, ↓reduceIte]
    simp [rawAlloc, hc, zig_unfold, set, StateT.set, MonadStateOf.set]
  by_cases ho : m.oracleDenies n = true
  · simp only [show m.allocDenied n from .inr ho, ↓reduceIte]
    simp only [not_or] at hc
    simp [rawAlloc, hc, ho, zig_unfold, set, StateT.set, MonadStateOf.set]
  · simp only [show ¬ m.allocDenied n from fun h => h.elim hc ho, ↓reduceIte]
    simp only [not_or] at hc
    cases hr : m.roomFor n align <;>
      simp [rawAlloc, hc, ho, hr, zig_unfold, set, StateT.set, MonadStateOf.set]

/-! ## `remapByteBuffer` (the byte remap of `Allocator.remap`), branch by branch -/

/-- Default remap failure is an exact no-op on all memory, even before success validation.
This preserves the old model's failure-only behavior, including its admitted call scope. -/
theorem remapByteBuffer_default_run {m : Mem} (s : Slice) (n : Nat)
    (hmode : m.allocPolicy.byteRemap = .fail) :
    (remapByteBuffer s n).run m = pure (none, m) := by
  simp [remapByteBuffer, hmode, zig_unfold]

/-- In place, an access that fails fails the remap. -/
theorem remapByteBuffer_inPlace_throw {m : Mem} {s : Slice} {n : Nat}
    (hmode : m.allocPolicy.byteRemap = .inPlace) {e : Error}
    (hacc : m.access s.ptr s.len.toNat 1 = throw e) :
    (remapByteBuffer s n).run m = throw e := by
  simp [remapByteBuffer, hmode, hacc, zig_unfold]

/-- In place, a slice that is not a whole heap block is illegal. -/
theorem remapByteBuffer_inPlace_illegal {m : Mem} {s : Slice} {n : Nat} {b : BlockId} {blk : Block}
    {o : Nat} (hmode : m.allocPolicy.byteRemap = .inPlace)
    (hacc : m.access s.ptr s.len.toNat 1 = pure (b, blk, o))
    (hbad : blk.kind ≠ .heap ∨ o ≠ 0 ∨ blk.bytes.size ≠ s.len.toNat) :
    (remapByteBuffer s n).run m = throw .illegal := by
  simp [remapByteBuffer, hmode, hacc, hbad, zig_unfold]

/-- In place, a request that the policy or the address space refuses returns `none` and leaves
the memory as it is. -/
theorem remapByteBuffer_inPlace_none {m : Mem} {s : Slice} {n : Nat} {b : BlockId} {blk : Block}
    {o : Nat} (hmode : m.allocPolicy.byteRemap = .inPlace)
    (hacc : m.access s.ptr s.len.toNat 1 = pure (b, blk, o))
    (hok : ¬ (blk.kind ≠ .heap ∨ o ≠ 0 ∨ blk.bytes.size ≠ s.len.toNat))
    (hnone : (blk.align ≠ 1 ∨ n = 0 ∨ m.allocPolicy.maxBytes < n) ∨
      (blk.bytes.size < n ∧ m.growFree b blk n ≠ true)) :
    (remapByteBuffer s n).run m = pure (none, m) := by
  rcases hnone with h | h
  · simp [remapByteBuffer, hmode, hacc, hok, h, zig_unfold]
  · by_cases h' : blk.align ≠ 1 ∨ n = 0 ∨ m.allocPolicy.maxBytes < n
    · simp [remapByteBuffer, hmode, hacc, hok, h', zig_unfold]
    · simp [remapByteBuffer, hmode, hacc, hok, h', h, zig_unfold]

/-- The actual in-place runtime branch, with explicit access/race/resource premises.
No undefined byte is decoded, and no external frame assumption is hidden in the run fact. -/
theorem remapByteBuffer_inPlace_run {m : Mem} {s : Slice} {b : BlockId} {blk : Block} {n : Nat}
    (hmode : m.allocPolicy.byteRemap = .inPlace)
    (hacc : m.access s.ptr s.len.toNat 1 = pure (b, blk, 0))
    (hkind : blk.kind = .heap) (hsize : blk.bytes.size = s.len.toNat) (halign : blk.align = 1)
    (hpos : n ≠ 0) (hcap : n ≤ m.allocPolicy.maxBytes)
    (hlatest : blk.bytes.size < n → m.growFree b blk n = true)
    (hrace : NoRace m b 0 blk.bytes.size .write) :
    (remapByteBuffer s n).run m =
      pure (some ⟨s.ptr, BitVec.ofNat 64 n⟩,
        (m.recordAt b 0 blk.bytes.size .write).afterByteRemap b blk n) := by
  have hr := recordAccess_run hrace
  change (recordAccess b 0 blk.bytes.size .write).run m =
    pure ((), m.recordAt b 0 blk.bytes.size .write) at hr
  simp only [StateT.run] at hr
  have hwhole : ¬ (blk.kind ≠ .heap ∨ blk.bytes.size ≠ s.len.toNat) := by
    simp [hkind, hsize]
  have haligned : ¬ (blk.align ≠ 1 ∨ n = 0 ∨ m.allocPolicy.maxBytes < n) := by
    simp [halign, hpos, Nat.not_lt.mpr hcap]
  have hgrowth : ¬ (blk.bytes.size < n ∧ m.growFree b blk n = false) := by
    rintro ⟨hg, hf⟩
    have ht := hlatest hg
    rw [ht] at hf
    cases hf
  simp [remapByteBuffer, hmode, hacc, hwhole, haligned, hgrowth,
    zig_unfold, hr, ExceptT.bindCont, set, StateT.set, MonadStateOf.set]

end Zig
