import Proofs.Layout.Gen
import ZigLean.Mem.Lemmas
import ZigLean.Simp

/-!
# Proofs about `examples/layout/layout.zig`

`Flags` (a packed struct) and its byte are a bijection (`Zig.Packed`), and `setMode` changes
only the `mode` bits. `headerLen` reads the length after the magic number of an `extern struct`
header. An indirect call through the table `ops` calls the function at that index; a pointer that
is not a function throws `.illegal`. The small bit-level facts are `decide` over all values: no
`bv_decide`, whose proofs use the axiom `Lean.ofReduceBool`.
-/

open Layout Zig

/-- The packed round trip: a `Flags` value through its byte and back. -/
theorem Flags.ofBits_toBits (f : Flags) : (Packed.ofBits (Packed.toBits f) : Flags) = f := by
  obtain ⟨r, e, m, c⟩ := f
  revert r e m c
  decide

/-- The other direction: every byte is the byte of one `Flags` value. -/
theorem Flags.toBits_ofBits (b : BitVec 8) : Packed.toBits (Packed.ofBits b : Flags) = b := by
  revert b
  decide

/-- The packed round trip of `Ctl`, which has an enum field. -/
theorem Ctl.ofBits_toBits (c : Ctl) : (Packed.ofBits (Packed.toBits c) : Ctl) = c := by
  obtain ⟨o, md, l⟩ := c
  cases md <;> revert o l <;> decide

/-- A byte is a `Ctl` value if its mode bits (1 and 2) are not 3: `Mode` has no name for 3. -/
theorem Ctl.valid_iff (b : BitVec 8) :
    Packed.valid (α := Ctl) b = true ↔ b.extractLsb' 1 2 ≠ 3 := by
  revert b
  decide

/-- `@bitCast` of a byte with mode 3 to `Ctl` is illegal behaviour. -/
theorem ctlSum_illegal (b : BitVec 8) (h : b.extractLsb' 1 2 = 3) : ctlSum b = throw .illegal := by
  have hv : Packed.valid (α := Ctl) b = false := by
    rw [Bool.eq_false_iff]; intro hv; exact (Ctl.valid_iff b).mp hv h
  simp [ctlSum, zig_unfold, Packed.ofBits?, hv]

/-- `setMode` replaces bits 2 and 3 of `b` with `m` and keeps the other bits. -/
theorem setMode_spec (b : BitVec 8) (m : BitVec 2) :
    setMode b m = pure ((b &&& 0xF3#8) ||| (m.setWidth 8 <<< 2)) := by
  have h : ∀ (b : BitVec 8) (m : BitVec 2),
      Packed.toBits ({ (Packed.ofBits b : Flags) with mode := m } : Flags) =
        (b &&& 0xF3#8) ||| (m.setWidth 8 <<< 2) := by decide
  rw [← h]
  rfl

/-- An indirect call through `ops`: `double`, `square`, `succ`. -/
theorem applyOp_spec (m : Mem) (x : BitVec 32) :
    (applyOp 0 x).run m = pure (x * 2, m) ∧ (applyOp 1 x).run m = pure (x * x, m) ∧
      (applyOp 2 x).run m = pure (x + 1, m) := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- An index past `ops` panics (`outOfBounds`). -/
theorem applyOp_oob (m : Mem) (i : BitVec 64) (x : BitVec 32) (h : 3 ≤ i.toNat) :
    (applyOp i x).run m = throw .outOfBounds := by
  have hlt : ¬ i.toNat < 3 := by omega
  simp [applyOp, zig_unfold, Zig.lt, BitVec.ult, hlt]

/-- A pointer that is not a function (block 3 is no function) throws `.illegal`. -/
theorem applyTwice_illegal (m : Mem) (x : BitVec 32) :
    (applyTwice ⟨some 3, 0⟩ x).run m = throw .illegal := rfl

/-- `twice` passes `&square` or `&double` as a runtime function pointer. -/
theorem twice_spec (m : Mem) (x : BitVec 32) :
    (twice true x).run m = pure (x * x * (x * x), m) ∧
      (twice false x).run m = pure (x * 2 * 2, m) := ⟨rfl, rfl⟩

/-- Fewer than 8 bytes: no header, and no memory access. -/
theorem headerLen_short (m : Mem) (s : Slice) (h : s.len.toNat < 8) :
    (headerLen s).run m = pure (none, m) := by
  simp [headerLen, zig_unfold, Zig.lt, BitVec.ult, h]

/-- `headerLen` from the results of its two loads: the magic number, then the length. -/
theorem headerLen_run {m m₁ m₂ : Mem} {s : Slice} {mg : BitVec 32} {len : BitVec 16}
    (h : 8 ≤ s.len.toNat)
    (hmg : (load (BitVec 32) 1 (s.ptr.add 0)).run m = pure (mg, m₁))
    (hlen : (load (BitVec 16) 1 (s.ptr.add 4)).run m₁ = pure (len, m₂)) :
    (headerLen s).run m =
      if mg = 0x4C524941#32 then pure (some len, m₂) else pure (none, m₁) := by
  have h8 : ¬ s.len.toNat < 8 := by omega
  simp only [StateT.run] at hmg hlen
  by_cases hm : mg = 0x4C524941#32
  · simp [headerLen, zig_unfold, Zig.lt, BitVec.ult, h8, hmg, hlen, hm]
  · simp [headerLen, zig_unfold, Zig.lt, BitVec.ult, h8, hmg, hm]

/-- `headerLen` from the bytes: the length if the first 4 bytes are the magic number. -/
theorem headerLen_spec {m : Mem} {s : Slice} {b b' : BlockId} {blk blk' : Block} {o o' : Nat}
    {mg : BitVec 32} {len : BitVec 16} (h : 8 ≤ s.len.toNat)
    (ha : m.access (s.ptr.add 0) 4 1 = pure (b, blk, o))
    (hmg : Enc.decode (blk.bytes.extract o (o + 4)) = pure mg)
    (hnr : NoRace m b o 4 .read)
    (ha' : (m.recordAt b o 4 .read).access (s.ptr.add 4) 2 1 = pure (b', blk', o'))
    (hlen : Enc.decode (blk'.bytes.extract o' (o' + 2)) = pure len)
    (hnr' : NoRace (m.recordAt b o 4 .read) b' o' 2 .read) :
    (headerLen s).run m =
      if mg = 0x4C524941#32 then pure (some len, (m.recordAt b o 4 .read).recordAt b' o' 2 .read)
      else pure (none, m.recordAt b o 4 .read) :=
  headerLen_run h (load_run (α := BitVec 32) ha hmg hnr) (load_run (α := BitVec 16) ha' hlen hnr')
