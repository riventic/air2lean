import Proofs.Layout.Gen
import ZigLean.Sep.Triple
import ZigLean.Sep.Witness
import ZigLean.Simp

/-!
# Unions and error unions in memory (`examples/layout/layout.zig`)

`Num` is a bare union: in `ReleaseSafe` it has a hidden tag, so the translator makes it a tagged
union. A defined value's encoding reads back as itself (`Num.decode_encode_int`/`_small`; a
payload that a retag left undefined, `undef_*`, encodes as undefined bytes, so `Num` is not
`LawfulEnc`, MM-13), `setNum` writes a value and
`numInt` reads it back. `bump` adds 1 to the payload of an error union in memory
(`LawfulEnc (Except ErrName α)`, `ZigLean/Mem/Lemmas.lean`). A write to the `const` global
`table` throws `.illegal`. The `extern` union facts are general: `Zig.Raw.get_init`,
`Zig.Raw.get_set` (`ZigLean/Mem/Lemmas.lean`).
-/

open Layout Zig

/-- The hidden tag of `Num`: its `BitVec 1`. -/
instance : LawfulEnc NumTag where
  size_encode v := LawfulEnc.size_encode (α := BitVec 1) v.toBits
  decode_encode v := by
    have h : ∀ w : BitVec 1, (Enc.decode (Enc.encode w) : Result (BitVec 1)) = pure w :=
      LawfulEnc.decode_encode
    show (do
      let b : BitVec 1 ← Enc.decode (Enc.encode v.toBits)
      match NumTag.ofInt? (Zig.val false b) with
      | some v => pure v
      | none => throw .illegal : Result NumTag) = pure v
    rw [h]
    cases v <;> rfl

/-- The bytes of `Enc.fields 8 [(4, t), (0, x)]`: the tag `t` at 4, the payload `x` at 0. -/
theorem fields_num {t x : Array Byte} (ht : t.size = 1) (hx : x.size ≤ 4) :
    (Enc.fields 8 [(4, t), (0, x)]).size = 8 ∧
      (Enc.fields 8 [(4, t), (0, x)]).extract 4 (4 + t.size) = t ∧
      (Enc.fields 8 [(4, t), (0, x)]).extract 0 (0 + x.size) = x := by
  have h1 : (writeBytes (Array.replicate 8 Byte.undef) 4 t).size = 8 := by
    rw [writeBytes_size _ _ _ (by simp; omega)]; simp
  simp only [Enc.fields, List.foldl]
  refine ⟨?_, ?_, ?_⟩
  · rw [writeBytes_size _ _ _ (by omega), h1]
  · rw [extract_writeBytes_disjoint _ _ _ _ _ (by omega) (by omega) (by omega)]
    exact extract_writeBytes _ 4 t (by simp; omega)
  · exact extract_writeBytes _ 0 x (by omega)

/-- The bare union `Num` in memory: the hidden tag at byte 4, the payload at byte 0. Every
value, also one whose payload a retag left undefined, has the size of `Num`. -/
theorem Num.size_encode (v : Num) : (Enc.encode v).size = Enc.size Num := by
  cases v with
  | int x => exact (fields_num (LawfulEnc.size_encode (α := NumTag) _)
      (by rw [LawfulEnc.size_encode x]; decide)).1
  | small x => exact (fields_num (LawfulEnc.size_encode (α := NumTag) _)
      (by rw [LawfulEnc.size_encode x]; decide)).1
  | undef_int _ _ =>
    show (Enc.fields 8 [(4, Enc.encode NumTag.int)]).size = 8
    simp only [Enc.fields, List.foldl]
    rw [writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode (α := NumTag)]; simp; decide)]; simp
  | undef_small _ _ =>
    show (Enc.fields 8 [(4, Enc.encode NumTag.small)]).size = 8
    simp only [Enc.fields, List.foldl]
    rw [writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode (α := NumTag)]; simp; decide)]; simp

/-- A `Num` that holds `int` reads back as itself. -/
theorem Num.decode_encode_int (x : BitVec 32) :
    Enc.decode (Enc.encode (Num.int x)) = pure (Num.int x) := by
  obtain ⟨-, ht, hx⟩ := fields_num (LawfulEnc.size_encode (α := NumTag) .int)
    (by rw [LawfulEnc.size_encode x]; decide)
  rw [LawfulEnc.size_encode (α := NumTag), LawfulEnc.size_encode x] at *
  show (do
    let t : NumTag ← Enc.decodeAt (Enc.fields 8 [(4, Enc.encode NumTag.int), (0, Enc.encode x)]) 4
    match t with
    | .int => pure (Num.int (← Enc.decodeAt (Enc.fields 8 [(4, Enc.encode NumTag.int), (0, Enc.encode x)]) 0))
    | .small => pure (Num.small (← Enc.decodeAt (Enc.fields 8 [(4, Enc.encode NumTag.int), (0, Enc.encode x)]) 0)) : Result Num) = pure (Num.int x)
  simp only [Enc.decodeAt]
  rw [ht, hx, LawfulEnc.decode_encode (α := NumTag), LawfulEnc.decode_encode x]; rfl

/-- A `Num` that holds `small` reads back as itself. -/
theorem Num.decode_encode_small (x : BitVec 8) :
    Enc.decode (Enc.encode (Num.small x)) = pure (Num.small x) := by
  obtain ⟨-, ht, hx⟩ := fields_num (LawfulEnc.size_encode (α := NumTag) .small)
    (by rw [LawfulEnc.size_encode x]; decide)
  rw [LawfulEnc.size_encode (α := NumTag), LawfulEnc.size_encode x] at *
  show (do
    let t : NumTag ← Enc.decodeAt (Enc.fields 8 [(4, Enc.encode NumTag.small), (0, Enc.encode x)]) 4
    match t with
    | .int => pure (Num.int (← Enc.decodeAt (Enc.fields 8 [(4, Enc.encode NumTag.small), (0, Enc.encode x)]) 0))
    | .small => pure (Num.small (← Enc.decodeAt (Enc.fields 8 [(4, Enc.encode NumTag.small), (0, Enc.encode x)]) 0)) : Result Num) = pure (Num.small x)
  simp only [Enc.decodeAt]
  rw [ht, hx, LawfulEnc.decode_encode (α := NumTag), LawfulEnc.decode_encode x]; rfl

/-- The payload of a `Num` that holds `int`. -/
theorem Num.decode_int {bs : Array Byte} {x : BitVec 32} (h : (Enc.decode bs : Result Num) = pure (Num.int x)) :
    (Enc.decodeAt bs 0 : Result (BitVec 32)) = pure x := by
  change (do
    let t : NumTag ← Enc.decodeAt bs 4
    match t with
    | .int => pure (Num.int (← Enc.decodeAt bs 0))
    | .small => pure (Num.small (← Enc.decodeAt bs 0)) : Result Num) = _ at h
  generalize (Enc.decodeAt bs 4 : Result NumTag) = rt at h
  generalize (Enc.decodeAt bs 0 : Result (BitVec 32)) = rx at h ⊢
  generalize (Enc.decodeAt bs 0 : Result (BitVec 8)) = ry at h
  match rt, rx, ry, h with
  | some (.ok .int), some (.ok v), _, h => simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h; cases h; rfl
  | some (.ok .int), some (.error _), _, h => simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h <;> cases h
  | some (.ok .int), none, _, h => simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h <;> cases h
  | some (.ok .small), _, some (.ok _), h => simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h <;> cases h
  | some (.ok .small), _, some (.error _), h => simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h <;> cases h
  | some (.ok .small), _, none, h => simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h <;> cases h
  | some (.error _), _, _, h => simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h <;> cases h
  | none, _, _, h => simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h <;> cases h

/-- `numInt` reads the payload of a `Num` that holds `int`. -/
theorem numInt_spec (p : Ptr) (x : BitVec 32) :
    Triple (pts p 4 (Num.int x)) (numInt p) (fun r => ⌜r = x⌝ ∗ pts p 4 (Num.int x)) := by
  apply Triple.of_run
  intro m hP hF hd hm hp hst
  obtain ⟨mA, hl, hmA, hstA⟩ := pts_load_run hp hm (by decide) hst
  obtain ⟨A, S, K, bs, ha, hs, hv, hb, -⟩ := id hp
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ := bytesAt_access (q := p.add 0) (k := 0) (n := 4) (a := 4)
    hb hmA (by simp [Ptr.add]) (by decide) (by rw [hs]; decide) (by simpa using ha)
  have hv' : Enc.decode (blk.bytes.extract (p.off.toNat + 0) (p.off.toNat + 0 + Enc.size (BitVec 32))) =
      pure x := by
    rw [show Enc.size (BitVec 32) = 4 from rfl, hx]; exact Num.decode_int hv
  have hl2 := load_run (α := BitVec 32) hacc hv' (noRace_of_singleThread hstA.single _ _ _ _)
  refine ⟨x, mA.recordAt b (p.off.toNat + 0) (Enc.size (BitVec 32)) .read, hP, ?_, hd, ?_,
    sep_lift.mpr ⟨rfl, hp⟩, hstA.recordAt _ _ _ _⟩
  · simp only [StateT.run, Ptr.add_zero] at hl hl2
    simp [numInt, zig_unfold, hl, hl2, Num.tag]
  · funext l; rw [Mem.heap_recordAt]; exact congrFun hmA l

/-- A `Num` from its tag and payload bytes. -/
theorem Num.decode_of_int {bs : Array Byte} {x : BitVec 32}
    (ht : (Enc.decodeAt bs 4 : Result NumTag) = pure .int)
    (hx : (Enc.decodeAt bs 0 : Result (BitVec 32)) = pure x) :
    (Enc.decode bs : Result Num) = pure (Num.int x) := by
  change (do
    let t : NumTag ← Enc.decodeAt bs 4
    match t with
    | .int => pure (Num.int (← Enc.decodeAt bs 0))
    | .small => pure (Num.small (← Enc.decodeAt bs 0)) : Result Num) = _
  rw [ht, hx]; rfl

/-- `setNum p true x` writes the tag `int` and the payload `x`: the old value does not matter. -/
theorem setNum_spec (p : Ptr) (n : Num) (x : BitVec 32) :
    Triple (pts p 4 n) (setNum p true x) (fun _ => pts p 4 (Num.int x)) := by
  apply Triple.of_run
  intro m hP hF hd hm hp hst
  obtain ⟨A, S, K, bs, ha, hs, -, hb, hK⟩ := hp
  have hs8 : bs.size = 8 := hs
  have ht1 : (Enc.encode NumTag.int).size = 1 := LawfulEnc.size_encode _
  have hx4 : (Enc.encode x).size = 4 := LawfulEnc.size_encode x
  -- The compiler stores the tag and the payload in either order (disjoint bytes).
  first
  | -- Tag first (0.16.0, 0.15.2).
      obtain ⟨m₁, hr₁, hst₁, h₁, hd₁, hm₁, hb₁⟩ := bytesAt_store (q := p.add 4) (k := 4) (a := 1)
        (bs' := Enc.encode NumTag.int) hb hm hd rfl (by omega) (by omega) (Nat.mod_one _) hst hK
      have hs₁ : (writeBytes bs 4 (Enc.encode NumTag.int)).size = 8 := by
        rw [writeBytes_size _ _ _ (by omega), hs8]
      obtain ⟨m₂, hr₂, hst₂, h₂, hd₂, hm₂, hb₂⟩ := bytesAt_store (q := p.add 0) (k := 0) (a := 4)
        (bs' := Enc.encode x) hb₁ hm₁ hd₁ rfl (by omega) (by omega) (by simpa using ha) hst₁ hK
      refine ⟨(), m₂, h₂, ?_, hd₂, hm₂, ⟨A, S, K, _, ha, ?_, ?_, hb₂, hK⟩, hst₂⟩
      · have e₁ : (store 1 (p.add 4) NumTag.int).run m = pure ((), m₁) := hr₁
        have e₂ : (store 4 (p.add 0) x).run m₁ = pure ((), m₂) := hr₂
        simp only [StateT.run, Ptr.add_zero] at e₁ e₂
        simp [setNum, zig_unfold, e₁, e₂]
      · rw [writeBytes_size _ _ _ (by omega), hs₁]; rfl
      · apply Num.decode_of_int
        · have e := extract_writeBytes_disjoint (writeBytes bs 4 (Enc.encode NumTag.int)) 0
            (Enc.encode x) 4 1 (by omega) (by omega) (by omega)
          have e' := extract_writeBytes bs 4 (Enc.encode NumTag.int) (by omega)
          rw [ht1] at e'
          simp only [Enc.decodeAt]
          rw [show (4 : Nat) + Enc.size NumTag = 4 + 1 from rfl, e, e']
          exact LawfulEnc.decode_encode _
        · have e := extract_writeBytes (writeBytes bs 4 (Enc.encode NumTag.int)) 0 (Enc.encode x)
            (by omega)
          rw [hx4] at e
          simp only [Enc.decodeAt]
          rw [show (0 : Nat) + Enc.size (BitVec 32) = 0 + 4 from rfl, e]
          exact LawfulEnc.decode_encode x
  |   -- Payload first (0.14.1).
    obtain ⟨m₁, hr₁, hst₁, h₁, hd₁, hm₁, hb₁⟩ := bytesAt_store (q := p.add 0) (k := 0) (a := 4)
      (bs' := Enc.encode x) hb hm hd rfl (by omega) (by omega) (by simpa using ha) hst hK
    have hs₁ : (writeBytes bs 0 (Enc.encode x)).size = 8 := by
      rw [writeBytes_size _ _ _ (by omega), hs8]
    obtain ⟨m₂, hr₂, hst₂, h₂, hd₂, hm₂, hb₂⟩ := bytesAt_store (q := p.add 4) (k := 4) (a := 1)
      (bs' := Enc.encode NumTag.int) hb₁ hm₁ hd₁ rfl (by omega) (by omega) (Nat.mod_one _) hst₁ hK
    refine ⟨(), m₂, h₂, ?_, hd₂, hm₂, ⟨A, S, K, _, ha, ?_, ?_, hb₂, hK⟩, hst₂⟩
    · have e₁ : (store 4 (p.add 0) x).run m = pure ((), m₁) := hr₁
      have e₂ : (store 1 (p.add 4) NumTag.int).run m₁ = pure ((), m₂) := hr₂
      simp only [StateT.run, Ptr.add_zero] at e₁ e₂
      simp [setNum, zig_unfold, e₁, e₂]
    · rw [writeBytes_size _ _ _ (by omega), hs₁]; rfl
    · apply Num.decode_of_int
      · have e := extract_writeBytes (writeBytes bs 0 (Enc.encode x)) 4 (Enc.encode NumTag.int)
          (by omega)
        rw [ht1] at e
        simp only [Enc.decodeAt]
        rw [show (4 : Nat) + Enc.size NumTag = 4 + 1 from rfl, e]
        exact LawfulEnc.decode_encode _
      · have e := extract_writeBytes_disjoint (writeBytes bs 0 (Enc.encode x)) 4
          (Enc.encode NumTag.int) 0 4 (by omega) (by omega) (by omega)
        have e' := extract_writeBytes bs 0 (Enc.encode x) (by omega)
        rw [hx4] at e'
        simp only [Enc.decodeAt]
        rw [show (0 : Nat) + Enc.size (BitVec 32) = 0 + 4 from rfl, e, e']
        exact LawfulEnc.decode_encode x

/-- `bump` adds 1 to the payload of an error union in memory (`ParseError!u8`: the error code
at 0, the payload at 2). -/
theorem bump_ok_spec (p : Ptr) (x : BitVec 8) :
    Triple (pts p 2 (Except.ok x : Except ErrName (BitVec 8))) (bump p)
      (fun _ => pts p 2 (Except.ok (x + 1) : Except ErrName (BitVec 8))) := by
  apply Triple.of_run
  intro m hP hF hd hm hp hst
  let domain : ErrorDomain := { names := #["Empty", "TooBig"], unique := by decide, bounded := by decide }
  let enc : Enc (Except ErrName (BitVec 8)) := errorUnionEnc domain inferInstance
  have hpFinite : @pts (Except ErrName (BitVec 8)) enc p 2 (.ok x) hP := by
    obtain ⟨A, S, K, bs, ha, hs, hv, hb, hK⟩ := hp
    refine ⟨A, S, K, bs, ha, hs, ?_, hb, hK⟩
    have hlegacy : (Enc.errorUnionWith (inferInstance : Enc (BitVec 8))).decode bs =
        pure (.ok x) := hv
    change (errorUnionEnc domain (inferInstance : Enc (BitVec 8))).decode bs = pure (.ok x)
    unfold errorUnionEnc
    dsimp only [Enc.decode]
    rw [hlegacy]
    rfl
  have hloadFinite : ∃ mA, (@load (Except ErrName (BitVec 8)) enc 2 p).run m =
      pure (.ok x, mA) ∧ mA.heap = hP ∪ hF ∧ mA.Seq := by
    letI : Enc (Except ErrName (BitVec 8)) := enc
    exact pts_load_run hpFinite hm (by decide) hst
  obtain ⟨mA, hl, hmA, hstA⟩ := hloadFinite
  obtain ⟨A, S, K, bs, ha, hs, hv, hb, hK⟩ := hp
  have hs4 : bs.size = 4 := hs
  have hpo : (errUnionOffsets (Enc.size (BitVec 8)) (Enc.align (BitVec 8))).2 = 2 := by decide
  have heo : (errUnionOffsets (Enc.size (BitVec 8)) (Enc.align (BitVec 8))).1 = 0 := by decide
  obtain ⟨hcode, hpay⟩ := errUnion_decode_ok hv
  rw [hpo] at hpay
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ := bytesAt_access (q := p.add 2) (k := 2) (n := 1) (a := 1)
    hb hmA rfl (by decide) (by omega) (Nat.mod_one _)
  have hv' : Enc.decode (blk.bytes.extract (p.off.toNat + 2) (p.off.toNat + 2 + Enc.size (BitVec 8))) =
      pure x := by
    rw [show Enc.size (BitVec 8) = 1 from rfl, hx]; exact hpay
  have hl2 := load_run (α := BitVec 8) hacc hv' (noRace_of_singleThread hstA.single _ _ _ _)
  have hmB : (mA.recordAt b (p.off.toNat + 2) (Enc.size (BitVec 8)) .read).heap = hP ∪ hF := by funext l; rw [Mem.heap_recordAt]; exact congrFun hmA l
  have hx1 : (Enc.encode (x + 1)).size = 1 := LawfulEnc.size_encode _
  obtain ⟨mC, hr₃, hstC, h₃, hd₃, hm₃, hb₃⟩ := bytesAt_store (q := p.add 2) (k := 2) (a := 1)
    (bs' := Enc.encode (x + 1)) hb hmB hd rfl (by omega) (by omega) (Nat.mod_one _)
    (hstA.recordAt _ _ _ _) hK
  refine ⟨(), mC, h₃, ?_, hd₃, hm₃, ⟨A, S, K, _, ha, ?_, ?_, hb₃, hK⟩, hstC⟩
  · have e₃ : (store 1 (p.add 2) (x + 1#8)).run
        (mA.recordAt b (p.off.toNat + 2) (Enc.size (BitVec 8)) .read) = pure ((), mC) := hr₃
    have hpp : errPayloadPtr (BitVec 8) p = p.add 2 := by simp [errPayloadPtr, hpo]
    have hpr := ptrProject_run (m := mA) (errPayloadPtr (BitVec 8)) rfl
      (by simpa using bytesAt_inBounds hb hmA (k := 0) (by omega) (by omega))
      (by rw [hpp]; exact bytesAt_inBounds hb hmA (k := 2) (by omega) (by omega))
    simp only [StateT.run] at hl hl2 e₃ hpr
    simp [bump, zig_unfold, hl, enc, domain, hpr, hpp, hl2, Zig.isNonErr, Zig.isErr, Zig.addWrap, e₃]
  · rw [writeBytes_size _ _ _ (by omega)]; exact hs
  · have := errUnion_decode_setPayload (bs := bs) (x + 1) hs hcode
    rwa [hpo] at this

/-- A write to the `const` table through `@constCast` throws `.illegal`: its block (3) is
read-only. This holds for every placement: the item's address is aligned because the block is. -/
theorem writeTable_illegal (σ : Placement) (i : BitVec 64) (v : BitVec 32) (h : i.toNat < 3) :
    (writeTable i v).run (mem0 σ) = throw .illegal := by
  obtain ⟨A, hb⟩ : ∃ A, (mem0 σ).blocks[3]? = some ⟨Enc.encode (#v[(10 : BitVec 32),
      (20 : BitVec 32), (30 : BitVec 32)] : Vector (BitVec 32) 3), 4, .constGlobal, true, A⟩ :=
    ⟨_, by simp [mem0, Mem.ofGlobals_getElem?]; rfl⟩
  have hA : A % 4 = 0 := by simpa using Mem.ofGlobals_addr_mod hb (by simp)
  have hi63 : i.toInt = (i.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hacc : (mem0 σ).access ((⟨some 3, 0⟩ : Ptr).elem 4 i) (Enc.size (BitVec 32)) 4 =
      pure (3, _, ((⟨some 3, 0⟩ : Ptr).elem 4 i).off.toNat) :=
    access_of rfl hb rfl (by simp [Ptr.elem, hi63, Ptr.add]; omega)
      (by simp [Ptr.elem, hi63, Ptr.add, Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign,
        alignUp]; omega)
      (by simp [Ptr.elem, hi63, Ptr.add]; omega)
  have hst := store_constGlobal v hacc rfl
  have hpr := ptrProject_run (m := mem0 σ) (·.elem 4 i) (p := ⟨some 3, 0⟩) rfl
    (inBounds_of rfl hb (by decide) (by simp [Enc.encode, padTo, intBytes, intSize,
      intAlign, alignUp]))
    (inBounds_of rfl hb (by simp [Ptr.elem, hi63, Ptr.add]; omega) (by
      simp [Ptr.elem, hi63, Ptr.add, Enc.encode, padTo, intBytes, intSize, intAlign, alignUp]
      omega))
  simp only [StateT.run] at hst hpr
  simp [writeTable, zig_unfold, Zig.lt, BitVec.ult, h, hst, hpr]

/-! ## Non-vacuity and liveness witnesses: one value in one block -/

nonvacuity_witness Num.decode_int := ⟨Enc.encode (Num.int 0), 0, Num.decode_encode_int 0, trivial⟩
nonvacuity_witness Num.decode_of_int :=
  ⟨Enc.encode (Num.int 0), 0, by with_unfolding_all rfl, by with_unfolding_all rfl, trivial⟩

theorem numInt_pre : pts Witness.p0 4 (Num.int 0) (Witness.mem1 (Enc.encode (Num.int 0))).heap :=
  Witness.mem1_pts (Num.size_encode _) (Num.decode_encode_int 0) (by decide) (by decide)

nonvacuity_witness numInt_spec := ⟨Witness.p0, 0, Witness.Admit.of_heap numInt_pre (Witness.mem1_seq _ _)⟩
liveness_witness numInt_spec :=
  ⟨Witness.p0, 0,
    Witness.Live.of_heap numInt_pre (Witness.mem1_seq _ _) (Witness.ok_of_okb (by decide +kernel))⟩

nonvacuity_witness setNum_spec :=
  ⟨Witness.p0, Num.int 0, 1, Witness.Admit.of_heap numInt_pre (Witness.mem1_seq _ _)⟩
liveness_witness setNum_spec :=
  ⟨Witness.p0, Num.int 0, 1,
    Witness.Live.of_heap numInt_pre (Witness.mem1_seq _ _) (Witness.ok_of_okb (by decide +kernel))⟩

theorem bump_pre : pts Witness.p0 2 (Except.ok 0 : Except ErrName (BitVec 8))
    (Witness.mem1 (Enc.encode (Except.ok 0 : Except ErrName (BitVec 8)))).heap :=
  Witness.mem1_pts' _ (by decide)

nonvacuity_witness bump_ok_spec := ⟨Witness.p0, 0, Witness.Admit.of_heap bump_pre (Witness.mem1_seq _ _)⟩
liveness_witness bump_ok_spec :=
  ⟨Witness.p0, 0,
    Witness.Live.of_heap bump_pre (Witness.mem1_seq _ _) (Witness.ok_of_okb (by decide +kernel))⟩
