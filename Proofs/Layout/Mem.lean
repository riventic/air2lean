import Proofs.Layout.Gen
import ZigLean.Sep.Full.AutoAll
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

The triples are total, in the full-state logic, walked by `fsym` with the library's typed-value
rules (`ZigLean/Sep/Full/Typed.lean`): a field read given the field's value, a tag and payload
write through the bytes view (`up_pts_iff`). The strength log
(`tests/roadmap/strength-log/ProofsLayout.lean`) gives back the legacy statements.
-/

open Layout Zig Zig.Full FAssn

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
    FTotalTriple (up (pts p 4 (Num.int x))) (numInt p)
      (fun r => ⟪r = x⟫ ⋆ up (pts p 4 (Num.int x))) := by
  fsym [FTotalTriple.field_load0 (v := x) (hv := fun _ _ h => Num.decode_int h)]

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

/-- The tag `int` and the payload `x` written over any 8 bytes, in either order, are `Num.int x`. -/
theorem Num.decode_set_int {bs : Array Byte} (hs : bs.size = 8) (x : BitVec 32) :
    (Enc.decode (writeBytes (writeBytes bs 4 (Enc.encode NumTag.int)) 0 (Enc.encode x)) : Result Num) =
        pure (Num.int x) ∧
      (Enc.decode (writeBytes (writeBytes bs 0 (Enc.encode x)) 4 (Enc.encode NumTag.int)) : Result Num) =
        pure (Num.int x) := by
  have ht1 : (Enc.encode NumTag.int).size = 1 := LawfulEnc.size_encode _
  have hx4 : (Enc.encode x).size = 4 := LawfulEnc.size_encode x
  have hs₁ : (writeBytes bs 4 (Enc.encode NumTag.int)).size = 8 := by
    rw [writeBytes_size _ _ _ (by omega), hs]
  have hs₂ : (writeBytes bs 0 (Enc.encode x)).size = 8 := by
    rw [writeBytes_size _ _ _ (by omega), hs]
  refine ⟨Num.decode_of_int ?_ ?_, Num.decode_of_int ?_ ?_⟩
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

/-- `setNum p true x` writes the tag `int` and the payload `x`: the old value does not matter.
The value is undecodable between the two stores, so they run on its bytes (`up_pts_iff`). -/
theorem setNum_spec (p : Ptr) (n : Num) (x : BitVec 32) :
    FTotalTriple (up (pts p 4 n)) (setNum p true x) (fun _ => up (pts p 4 (Num.int x))) := by
  refine (FTotalTriple.ex fun bs => FTotalTriple.lift fun ⟨hs, _⟩ => ?_).pre
    fun _ h => up_pts_iff.mp h
  have hs8 : bs.size = 8 := hs
  have ht : (Enc.encode NumTag.int).size = 1 := LawfulEnc.size_encode _
  have hx : (Enc.encode x).size = 4 := LawfulEnc.size_encode x
  -- The compiler stores the tag and the payload in either order (disjoint bytes).
  first
  | -- Tag first (0.16.0, 0.15.2).
    refine (?_ : FTotalTriple _ _ fun _ => up (Zig.region p 4
        (writeBytes (writeBytes bs 4 (Enc.encode NumTag.int)) 0 (Enc.encode x)))).post
      fun _ _ h => up_pts_of_region (by simp only [size_writeBytes, ht, hx, hs8]; rfl)
        (Num.decode_set_int hs8 x).1 h
    fsym
    done
  | -- Payload first (0.14.1).
    refine (?_ : FTotalTriple _ _ fun _ => up (Zig.region p 4
        (writeBytes (writeBytes bs 0 (Enc.encode x)) 4 (Enc.encode NumTag.int)))).post
      fun _ _ h => up_pts_of_region (by simp only [size_writeBytes, ht, hx, hs8]; rfl)
        (Num.decode_set_int hs8 x).2 h
    fsym

/-- `bump` adds 1 to the payload of an error union in memory (`ParseError!u8`: the error code
at 0, the payload at 2). -/
theorem bump_ok_spec (p : Ptr) (x : BitVec 8) :
    FTotalTriple (up (pts p 2 (Except.ok x : Except ErrName (BitVec 8)))) (bump p)
      (fun _ => up (pts p 2 (Except.ok (x + 1) : Except ErrName (BitVec 8)))) := by
  fsym

/-- A write to the `const` table through `@constCast` throws `.illegal`: its block (3) is
read-only. This holds for every placement: the item's address is aligned because the block is. -/
theorem writeTable_illegal (σ : Placement) (i : BitVec 64) (v : BitVec 32) (h : i.toNat < 3) :
    (writeTable i v).run (mem0 σ) = throw .illegal := by
  obtain ⟨A, hb⟩ : ∃ A, (mem0 σ).blocks[3]? = some ⟨Enc.encode (#v[(10 : BitVec 32),
      (20 : BitVec 32), (30 : BitVec 32)] : Vector (BitVec 32) 3), 4, .constGlobal, true, A⟩ :=
    ⟨_, by simp [mem0, Mem.ofGlobals_getElem?]; rfl⟩
  have hA : A % 4 = 0 := by simpa using Mem.ofGlobals_addr_mod hb (by simp)
  have hacc : (mem0 σ).access ((⟨some 3, 0⟩ : Ptr).elem 4 i) (Enc.size (BitVec 32)) 4 =
      pure (3, _, ((⟨some 3, 0⟩ : Ptr).elem 4 i).off.toNat) :=
    access_of rfl hb rfl (by simp [Ptr.elem, Ptr.add]; omega)
      (by simp [Ptr.elem, Ptr.add, Enc.encode, Enc.size, padTo, intBytes, intSize, intAlign,
        alignUp]; omega)
      (by simp [Ptr.elem, Ptr.add]; omega)
  have hst := store_constGlobal v hacc rfl
  have hpr := ptrProject_run (m := mem0 σ) (·.elem 4 i) (p := ⟨some 3, 0⟩) rfl
    (inBounds_of rfl hb (by decide) (by simp [Enc.encode, padTo, intBytes, intSize,
      intAlign, alignUp]))
    (inBounds_of rfl hb (by simp [Ptr.elem, Ptr.add]; omega) (by
      simp [Ptr.elem, Ptr.add, Enc.encode, padTo, intBytes, intSize, intAlign, alignUp]
      omega))
  simp only [StateT.run] at hst hpr
  simp [writeTable, zig_unfold, Zig.lt, BitVec.ult, h, hst, hpr, checkIndex]

/-! ## Non-vacuity witnesses: one value in one block

The triples are total: the return is part of the claim, so they need no liveness witness. -/

nonvacuity_witness Num.decode_int := ⟨Enc.encode (Num.int 0), 0, Num.decode_encode_int 0, trivial⟩
nonvacuity_witness Num.decode_of_int :=
  ⟨Enc.encode (Num.int 0), 0, by with_unfolding_all rfl, by with_unfolding_all rfl, trivial⟩

theorem numInt_pre : Witness.FAdmit (up (pts Witness.p0 4 (Num.int 0))) :=
  Witness.FAdmit.up
    (Witness.mem1_pts (kind := .heap) (Num.size_encode _) (Num.decode_encode_int 0) (by decide) (by decide))
    (Witness.mem1_fseq _ _ (by decide +kernel))

nonvacuity_witness numInt_spec := ⟨Witness.p0, 0, numInt_pre⟩
nonvacuity_witness setNum_spec := ⟨Witness.p0, Num.int 0, 1, numInt_pre⟩

theorem bump_pre : Witness.FAdmit (up (pts Witness.p0 2 (Except.ok 0 : Except ErrName (BitVec 8)))) :=
  Witness.FAdmit.up (Witness.mem1_pts' _ (by decide)) (Witness.mem1_fseq _ _ (by decide +kernel))

nonvacuity_witness bump_ok_spec := ⟨Witness.p0, 0, bump_pre⟩
