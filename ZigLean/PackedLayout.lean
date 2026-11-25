import ZigLean.PackedRepr

/-!
# Packed layouts: a packed value's bits read back (engine ledger #packed-roundtrip)

**`LawfulPacked α n`**: bits that are a value (`valid`) are the bits of the value they make
(`toBits_ofBits`, the bits direction `LawfulPackedBits`), and a value whose bits are all
determined (`mask`) is the value of its bits, which are valid (`ofBits_toBits`, the value
direction `LawfulPackedVal`); `LawfulPacked` is both. Integers, `bool`, `void` and floats are
lawful by the instances here (a float's `ofBits_toBits` asks for determined bits: a NaN has none,
so the law says nothing of it). An exhaustive enum is lawful by its tags (`EnumTags.lawful`); a
non-exhaustive one, whose value is its bits, by definition. An array or vector has each direction
its lanes have (one instance per direction, every lane type and width). A packed union has the
bits direction only (`PackedU.bitsOf_intBytes`; ledger #packed-lawful-split).

**`PackedLayout α n`** describes a packed struct as the translator generates it, once for all
packed structs: its fields (`PField`: the type's representation, the bit offset and the value),
in order from bit 0, tile the backing integer (`PTiles`); `toBits` ors each field's bits at its
offset (`toBits_eq`), `ofBits` reads each field at its offset (`ofBits_read`), the bits are valid
exactly when each field's are (`valid_iff`), every bit is determined only if each field's are
(`mask_full`), and a value is its fields (`ext`). `PackedLayout.lawfulBits`/`lawfulVal` prove
each direction once for every layout whose fields all have it, `PackedLayout.lawful` both. The
per-type obligations (the layout's fields) are discharged by `fsym` from the generated instance
(`lawfulPackedOf?`, `Auto.lean`), which derives the whole law (`LawfulPacked`). A type without
it gets no instance, and the rules that need one do not apply (fail closed).
-/

namespace Zig

/-- **The bits direction**: valid bits are the bits of the value they make. -/
class LawfulPackedBits (α : Type) (n : Nat) [Packed α n] : Prop where
  toBits_ofBits : ∀ b : BitVec n, Packed.valid (α := α) b = true →
    Packed.toBits (Packed.ofBits b : α) = b

/-- **The value direction**: a value with every bit determined is the value of its bits, which
are valid. -/
class LawfulPackedVal (α : Type) (n : Nat) [Packed α n] : Prop where
  ofBits_toBits : ∀ v : α, Packed.mask v = BitVec.allOnes n →
    Packed.valid (α := α) (Packed.toBits v) = true ∧ Packed.ofBits (Packed.toBits v) = v

/-- **A packable type's bits read back**, both directions (`LawfulPackedBits` and
`LawfulPackedVal`, by the instances below and `LawfulPacked.of`). -/
class LawfulPacked (α : Type) (n : Nat) [Packed α n] : Prop where
  toBits_ofBits : ∀ b : BitVec n, Packed.valid (α := α) b = true →
    Packed.toBits (Packed.ofBits b : α) = b
  ofBits_toBits : ∀ v : α, Packed.mask v = BitVec.allOnes n →
    Packed.valid (α := α) (Packed.toBits v) = true ∧ Packed.ofBits (Packed.toBits v) = v

instance LawfulPacked.bits {α : Type} {n : Nat} [Packed α n] [h : LawfulPacked α n] :
    LawfulPackedBits α n := ⟨h.toBits_ofBits⟩

instance LawfulPacked.val {α : Type} {n : Nat} [Packed α n] [h : LawfulPacked α n] :
    LawfulPackedVal α n := ⟨h.ofBits_toBits⟩

/-- Both directions are the law. -/
theorem LawfulPacked.of {α : Type} {n : Nat} [Packed α n] [hb : LawfulPackedBits α n]
    [hv : LawfulPackedVal α n] : LawfulPacked α n :=
  ⟨hb.toBits_ofBits, hv.ofBits_toBits⟩

instance {n : Nat} : LawfulPacked (BitVec n) n where
  toBits_ofBits _ _ := rfl
  ofBits_toBits _ _ := ⟨rfl, rfl⟩

instance : LawfulPacked Bool 1 where
  toBits_ofBits b _ := by
    show (if b == 1#1 then 1#1 else 0#1) = b
    rcases (by decide : ∀ c : BitVec 1, c = 0#1 ∨ c = 1#1) b with rfl | rfl <;> rfl
  ofBits_toBits v _ := by cases v <;> exact ⟨rfl, rfl⟩

instance lawfulPackedFloat {fmt : FloatFmt} : LawfulPacked (Float fmt) fmt.width where
  toBits_ofBits _ _ := rfl
  ofBits_toBits _ _ := ⟨rfl, rfl⟩

instance : LawfulPacked Unit 0 where
  toBits_ofBits b _ := (BitVec.eq_nil b).symm
  ofBits_toBits _ _ := ⟨rfl, rfl⟩

/-! ## Exhaustive enums -/

private theorem val_inj {s : Bool} {n : Nat} {a b : BitVec n} (h : val s a = val s b) : a = b := by
  cases s
  · simp only [val, Bool.false_eq_true, ↓reduceIte, Int.natCast_inj] at h
    exact BitVec.eq_of_toNat_eq h
  · simp only [val, ↓reduceIte] at h
    exact BitVec.eq_of_toInt_eq h

/-- An exhaustive enum's tags, as the generated instance reads them (`signed`: the tag type's
signedness; `ofInt?`: the value of a tag): each value's tag reads back as it (`tag`), and a tag
read as a value is that value's (`of_tag`). -/
structure EnumTags (α : Type) (n : Nat) [Packed α n] [Inhabited α] where
  signed : Bool
  ofInt? : Int → Option α
  ofBits_eq : ∀ b, (Packed.ofBits b : α) = (ofInt? (val signed b)).getD default
  valid_eq : ∀ b, Packed.valid (α := α) b = (ofInt? (val signed b)).isSome
  tag : ∀ v : α, ofInt? (val signed (Packed.toBits v)) = some v
  of_tag : ∀ x (v : α), ofInt? x = some v → x = val signed (Packed.toBits v)

/-- **An exhaustive enum is lawful.** -/
theorem EnumTags.lawful {α : Type} {n : Nat} [Packed α n] [Inhabited α] (E : EnumTags α n) :
    LawfulPacked α n where
  toBits_ofBits b hb := by
    rw [E.valid_eq] at hb
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hb
    rw [E.ofBits_eq, hv, Option.getD_some]
    exact (val_inj (E.of_tag _ v hv)).symm
  ofBits_toBits v _ := by
    rw [E.valid_eq, E.ofBits_eq, E.tag v]
    exact ⟨rfl, rfl⟩

/-! ## Packed structs -/

/-- A field of a packed value: its type's representation, its bit offset and its value. -/
structure PField : Type 1 where
  U : Type
  w : Nat
  inst : Packed U w
  off : Nat
  val : U

/-- Where a field lies: its type's representation and its bit offset (the field without its
value). -/
structure PSlot : Type 1 where
  U : Type
  w : Nat
  inst : Packed U w
  off : Nat

namespace PField

def slot (f : PField) : PSlot := ⟨f.U, f.w, f.inst, f.off⟩

/-- The field's bits. -/
def toBits (f : PField) : BitVec f.w := @Packed.toBits f.U f.w f.inst f.val

/-- The field's determined bits. -/
def mask (f : PField) : BitVec f.w := @Packed.mask f.U f.w f.inst f.val

/-- The field's bits at its offset in an `n`-bit backing integer (as the generated `toBits`
writes them). -/
def bits (n : Nat) (f : PField) : BitVec n := f.toBits.setWidth n <<< f.off

/-- The field's determined bits at its offset in an `n`-bit backing integer (as the generated
`mask` writes them). -/
def maskBits (n : Nat) (f : PField) : BitVec n := f.mask.setWidth n <<< f.off

/-- The field is the value of its bits of `b` (as the generated `ofBits` reads it). -/
def Read {n : Nat} (b : BitVec n) (f : PField) : Prop :=
  f.val = @Packed.ofBits f.U f.w f.inst (b.extractLsb' f.off f.w)

/-- The field's bits of `b` are a value of its type. -/
def Valid {n : Nat} (b : BitVec n) (f : PField) : Prop :=
  @Packed.valid f.U f.w f.inst (b.extractLsb' f.off f.w) = true

/-- Every bit of the field is determined. -/
def Full (f : PField) : Prop := f.mask = BitVec.allOnes f.w

/-- The field's type is lawful. -/
def Lawful (f : PField) : Prop := @LawfulPacked f.U f.w f.inst

/-- The field's type has the bits direction of the law. -/
def LawfulBits (f : PField) : Prop := @LawfulPackedBits f.U f.w f.inst

/-- The field's type has the value direction of the law. -/
def LawfulVal (f : PField) : Prop := @LawfulPackedVal f.U f.w f.inst

end PField

/-- Every item of the list has `P`. -/
def PAll {α : Type 1} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ PAll P xs

theorem PAll.mem {α : Type 1} {P : α → Prop} : ∀ {xs : List α}, PAll P xs → ∀ x ∈ xs, P x
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, hs⟩, x, .tail _ hx => PAll.mem hs x hx

theorem PAll.of_mem {α : Type 1} {P : α → Prop} : ∀ {xs : List α}, (∀ x ∈ xs, P x) → PAll P xs
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (.head _), PAll.of_mem fun x hx => h x (.tail _ hx)⟩

theorem PAll.imp {α : Type 1} {P Q : α → Prop} (h : ∀ x, P x → Q x) {xs : List α}
    (hp : PAll P xs) : PAll Q xs :=
  PAll.of_mem fun x hx => h x (hp.mem x hx)

/-- Bit vectors or-ed in order: `x₀ ||| x₁ ||| …` (`|||` associates to the left). -/
def orAll {n : Nat} : List (BitVec n) → BitVec n
  | [] => 0
  | x :: xs => xs.foldl (· ||| ·) x

/-- The ranges `(offset, width)` tile the bits `[c, n)` in order. -/
def PTiles (n : Nat) : Nat → List (Nat × Nat) → Bool
  | c, [] => c == n
  | c, (o, w) :: ps => o == c && PTiles n (c + w) ps

/-- **The layout of a packed type** (module doc). -/
structure PackedLayout (α : Type) (n : Nat) [Packed α n] where
  fields : α → List PField
  slots : List PSlot
  slots_eq : ∀ v, (fields v).map PField.slot = slots
  tiles : PTiles n 0 (slots.map fun s => (s.off, s.w)) = true
  toBits_eq : ∀ v, Packed.toBits v = orAll ((fields v).map (PField.bits n))
  ofBits_read : ∀ b, PAll (PField.Read b) (fields (Packed.ofBits b))
  valid_iff : ∀ b, Packed.valid (α := α) b = true ↔ PAll (PField.Valid b) (fields (Packed.ofBits b))
  mask_full : ∀ v, Packed.mask v = BitVec.allOnes n → PAll PField.Full (fields v)
  ext : ∀ v v', fields v = fields v' → v = v'

/-! ### Bits of tiled fields -/

section Tiled

theorem getLsbD_foldl_or {n : Nat} (j : Nat) :
    ∀ (xs : List (BitVec n)) (a : BitVec n),
      (xs.foldl (· ||| ·) a).getLsbD j = (a.getLsbD j || xs.any (·.getLsbD j))
  | [], a => by simp
  | x :: xs, a => by
    rw [List.foldl_cons, getLsbD_foldl_or j xs, BitVec.getLsbD_or, List.any_cons, Bool.or_assoc]

theorem getLsbD_orAll {n : Nat} (j : Nat) :
    ∀ xs : List (BitVec n), (orAll xs).getLsbD j = xs.any (·.getLsbD j)
  | [] => by simp [orAll]
  | x :: xs => by rw [orAll, getLsbD_foldl_or, List.any_cons]

/-- The fields of a tiling from `c` lie in `[c, n)`. -/
theorem PTiles.mem {n : Nat} :
    ∀ {c : Nat} {fs : List PField}, PTiles n c (fs.map fun f => (f.off, f.w)) = true →
      ∀ f ∈ fs, c ≤ f.off ∧ f.off + f.w ≤ n
  | c, [], _, _, h => nomatch h
  | c, g :: fs, h, f, hf => by
    simp only [List.map_cons, PTiles, Bool.and_eq_true, beq_iff_eq] at h
    have hle : ∀ {c fs}, PTiles n c (List.map (fun f : PField => (f.off, f.w)) fs) = true → c ≤ n := by
      intro c fs h
      induction fs generalizing c with
      | nil => simp only [List.map_nil, PTiles, beq_iff_eq] at h; omega
      | cons g fs ih =>
        simp only [List.map_cons, PTiles, Bool.and_eq_true, beq_iff_eq] at h
        have := ih h.2; omega
    rcases List.mem_cons.mp hf with rfl | hf
    · have := hle h.2; omega
    · have := PTiles.mem h.2 f hf; omega

/-- Every bit of `[c, n)` lies in a field of a tiling from `c`. -/
theorem PTiles.cover {n : Nat} :
    ∀ {c : Nat} {fs : List PField}, PTiles n c (fs.map fun f => (f.off, f.w)) = true →
      ∀ j, c ≤ j → j < n → ∃ f ∈ fs, f.off ≤ j ∧ j < f.off + f.w
  | c, [], h, j, h1, h2 => by simp only [List.map_nil, PTiles, beq_iff_eq] at h; omega
  | c, g :: fs, h, j, h1, h2 => by
    simp only [List.map_cons, PTiles, Bool.and_eq_true, beq_iff_eq] at h
    by_cases hj : j < c + g.w
    · exact ⟨g, List.mem_cons_self .., by omega, by omega⟩
    · obtain ⟨f, hf, h3⟩ := PTiles.cover h.2 j (by omega) h2
      exact ⟨f, List.mem_cons_of_mem _ hf, h3⟩

/-- **A field's bits of tiled fields' bits** are its own: `g f`, for each field `f`'s bits `g f`. -/
theorem PTiles.extract {n : Nat} (g : (f : PField) → BitVec f.w) :
    ∀ {c : Nat} {fs : List PField}, PTiles n c (fs.map fun f => (f.off, f.w)) = true →
      ∀ f ∈ fs, (orAll (fs.map fun f => (g f).setWidth n <<< f.off)).extractLsb' f.off f.w = g f := by
  intro c fs ht f hf
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', getLsbD_orAll, List.any_map]
  simp only [hi, decide_true, Bool.true_and, Function.comp_def]
  -- only `f` covers bit `f.off + i`
  induction fs generalizing c with
  | nil => nomatch hf
  | cons h fs ih =>
    have hm := PTiles.mem ht
    simp only [List.map_cons, PTiles, Bool.and_eq_true, beq_iff_eq] at ht
    have hrest := PTiles.mem ht.2
    rw [List.any_cons]
    rcases List.mem_cons.mp hf with rfl | hf'
    · have hn := hm f (List.mem_cons_self ..)
      have hnone : (fs.any fun x => ((g x).setWidth n <<< x.off).getLsbD (f.off + i)) = false := by
        rw [List.any_eq_false]
        intro x hx
        have := hrest x hx
        simp [BitVec.getLsbD_shiftLeft, show f.off + i < x.off by omega]
      rw [hnone, Bool.or_false]
      simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      have e : f.off + i - f.off = i := by omega
      rw [e]; simp [show f.off + i < n by omega, show i < n by omega]
    · have hn := hrest f hf'
      have hh := hm h (List.mem_cons_self ..)
      have hhead : ((g h).setWidth n <<< h.off).getLsbD (f.off + i) = false := by
        simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
        rw [BitVec.getLsbD_of_ge (g h) _ (by omega)]
        simp
      rw [hhead, Bool.false_or]
      exact ih ht.2 hf'

end Tiled

namespace PackedLayout

variable {α : Type} {n : Nat} [Packed α n]

theorem fields_tiles (L : PackedLayout α n) (v : α) :
    PTiles n 0 ((L.fields v).map fun f => (f.off, f.w)) = true := by
  have e : (L.fields v).map (fun f => (f.off, f.w)) = L.slots.map fun s => (s.off, s.w) := by
    rw [← L.slots_eq v, List.map_map]; rfl
  rw [e]; exact L.tiles

/-- A field's bits of a value's bits are its own. -/
theorem extract_toBits (L : PackedLayout α n) (v : α) :
    ∀ f ∈ L.fields v, (Packed.toBits v).extractLsb' f.off f.w = f.toBits := by
  intro f hf
  rw [L.toBits_eq]
  exact PTiles.extract PField.toBits (L.fields_tiles v) f hf

/-- **Valid bits read back**, for a layout of fields with the bits direction. -/
theorem toBits_ofBits (L : PackedLayout α n) (hl : ∀ v, PAll PField.LawfulBits (L.fields v))
    (b : BitVec n) (hb : Packed.valid (α := α) b = true) :
    Packed.toBits (Packed.ofBits b : α) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨f, hf, h1, h2⟩ := PTiles.cover (L.fields_tiles (Packed.ofBits b)) j (Nat.zero_le _) hj
  have hr := (L.ofBits_read b).mem f hf
  have hv := ((L.valid_iff b).mp hb).mem f hf
  have hlf := (hl _).mem f hf
  have hfb : f.toBits = b.extractLsb' f.off f.w := by
    unfold PField.toBits; rw [hr]; exact @LawfulPackedBits.toBits_ofBits f.U f.w f.inst hlf _ hv
  have e := congrArg (·.getLsbD (j - f.off)) (L.extract_toBits (Packed.ofBits b) f hf)
  simp only [hfb, BitVec.getLsbD_extractLsb', show j - f.off < f.w by omega, decide_true,
    Bool.true_and, show f.off + (j - f.off) = j by omega] at e
  exact e

/-- `fields` of the value of a value's bits, field by field. -/
private theorem read_eq (b : BitVec n) :
    ∀ (fs' fs : List PField), fs'.map PField.slot = fs.map PField.slot →
      (∀ f ∈ fs, b.extractLsb' f.off f.w = f.toBits ∧
        @Packed.valid f.U f.w f.inst f.toBits = true ∧ @Packed.ofBits f.U f.w f.inst f.toBits = f.val) →
      PAll (PField.Read b) fs' → fs' = fs ∧ PAll (PField.Valid b) fs'
  | [], [], _, _, _ => ⟨rfl, trivial⟩
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h
  | ⟨U', w', i', o', x'⟩ :: fs', ⟨U, w, i, o, x⟩ :: fs, hs, hf, ⟨hr, hrs⟩ => by
    simp only [List.map_cons, List.cons.injEq, PField.slot, PSlot.mk.injEq] at hs
    obtain ⟨⟨rfl, rfl, hi, rfl⟩, hs⟩ := hs
    cases eq_of_heq hi
    obtain ⟨he, hv, ho⟩ := hf _ (List.mem_cons_self ..)
    obtain ⟨ih, hvs⟩ := read_eq b fs' fs hs (fun f h => hf f (List.mem_cons_of_mem _ h)) hrs
    refine ⟨?_, ⟨?_, hvs⟩⟩
    · subst ih
      have : x' = x := by
        unfold PField.Read at hr; simp only at hr he; rw [hr, he]; exact ho
      rw [this]
    · show @Packed.valid U' w' i' (b.extractLsb' o' w') = true
      simp only at he; rw [he]; exact hv

/-- **A value with every bit determined is the value of its bits**, which are valid, for a layout
of fields with the value direction. -/
theorem ofBits_toBits (L : PackedLayout α n) (hl : ∀ v, PAll PField.LawfulVal (L.fields v))
    (v : α) (hm : Packed.mask v = BitVec.allOnes n) :
    Packed.valid (α := α) (Packed.toBits v) = true ∧ Packed.ofBits (Packed.toBits v) = v := by
  have hfull := L.mask_full v hm
  have hf : ∀ f ∈ L.fields v, (Packed.toBits v).extractLsb' f.off f.w = f.toBits ∧
      @Packed.valid f.U f.w f.inst f.toBits = true ∧ @Packed.ofBits f.U f.w f.inst f.toBits = f.val := by
    intro f hf
    have := @LawfulPackedVal.ofBits_toBits f.U f.w f.inst ((hl v).mem f hf) f.val (hfull.mem f hf)
    exact ⟨L.extract_toBits v f hf, this⟩
  have hs : (L.fields (Packed.ofBits (Packed.toBits v))).map PField.slot = (L.fields v).map PField.slot := by
    rw [L.slots_eq, L.slots_eq]
  obtain ⟨he, hv⟩ := read_eq (Packed.toBits v) _ _ hs hf (L.ofBits_read _)
  exact ⟨(L.valid_iff _).mpr hv, L.ext _ _ he⟩

/-- `mask_full` of fields that tile the backing integer and whose determined bits at their offsets
are the value's (`mask` as the translator writes it for a struct with a float or packed-union
field). -/
theorem mask_full_of {fields : α → List PField}
    (ht : ∀ v, PTiles n 0 ((fields v).map fun f => (f.off, f.w)) = true)
    (hm : ∀ v, Packed.mask v = orAll ((fields v).map (PField.maskBits n))) :
    ∀ v, Packed.mask v = BitVec.allOnes n → PAll PField.Full (fields v) := by
  intro v hv
  refine PAll.of_mem fun f hf => ?_
  have e := PTiles.extract PField.mask (ht v) f hf
  have hb := PTiles.mem (ht v) f hf
  have e' : (fields v).map (fun f => f.mask.setWidth n <<< f.off) = (fields v).map (PField.maskBits n) := rfl
  rw [e', ← hm v, hv] at e
  unfold PField.Full
  rw [← e]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and,
    decide_eq_true_eq]
  omega

/-- **A packed struct whose fields all have the bits direction has it.** -/
theorem lawfulBits (L : PackedLayout α n) (hl : ∀ v, PAll PField.LawfulBits (L.fields v)) :
    LawfulPackedBits α n :=
  ⟨L.toBits_ofBits hl⟩

/-- **A packed struct whose fields all have the value direction has it.** -/
theorem lawfulVal (L : PackedLayout α n) (hl : ∀ v, PAll PField.LawfulVal (L.fields v)) :
    LawfulPackedVal α n :=
  ⟨L.ofBits_toBits hl⟩

/-- **A packed struct of lawful fields is lawful.** -/
theorem lawful (L : PackedLayout α n) (hl : ∀ v, PAll PField.Lawful (L.fields v)) :
    LawfulPacked α n :=
  ⟨L.toBits_ofBits fun v => (hl v).imp fun f h => @LawfulPacked.bits f.U f.w f.inst h,
    L.ofBits_toBits fun v => (hl v).imp fun f h => @LawfulPacked.val f.U f.w f.inst h⟩

end PackedLayout

/-! ## Arrays and vectors

An array or vector of lanes (`Vector α k`, `Vec α k`, `ZigLean/PackedRepr.lean`: the lanes' bits
concatenated, lane 0 lowest) has each direction of the law its lanes have, for every lane width
and lane type, by one instance per direction. -/

section Lanes

variable {α : Type} {w k : Nat} [Packed α w]

/-- The lanes of a value's bits are its lanes' bits. -/
private theorem lanesOf_toBits (v : Vector α k) :
    lanesOf k (Packed.toBits v) = v.map Packed.toBits :=
  BitCast.toLanes_ofLanes _

/-- Every bit of an array is determined only if every bit of each lane is. -/
private theorem lane_mask_full (v : Vector α k) (h : Packed.mask v = BitVec.allOnes (k * w))
    (i : Nat) (hi : i < k) : Packed.mask v[i] = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have e := BitCast.getLsbD_ofLanes (v.map Packed.mask) i j hi hj
  have hlt : w * i + j < k * w := by
    have : w * i + w ≤ k * w := by rw [Nat.mul_comm k w, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    omega
  change (Packed.mask v).getLsbD (w * i + j) = _ at e
  rw [h, BitVec.getLsbD_allOnes, decide_eq_true hlt, Vector.getElem_map] at e
  rw [← e, BitVec.getLsbD_allOnes, decide_eq_true hj]

instance [LawfulPackedBits α w] : LawfulPackedBits (Vector α k) (k * w) where
  toBits_ofBits b hb := by
    change BitCast.ofLanes (((lanesOf k b).map Packed.ofBits).map Packed.toBits) = b
    have hv : ∀ i (hi : i < k), Packed.valid (α := α) (lanesOf k b)[i] = true := by
      change (lanesOf (w := w) k b).all (Packed.valid (α := α)) = true at hb
      exact Vector.all_eq_true.mp hb
    have e : ((lanesOf k b).map Packed.ofBits).map (Packed.toBits (α := α)) = lanesOf k b := by
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_map, Vector.getElem_map]
      exact LawfulPackedBits.toBits_ofBits _ (hv i hi)
    rw [e]
    exact BitCast.ofLanes_toLanes b

instance [LawfulPackedVal α w] : LawfulPackedVal (Vector α k) (k * w) where
  ofBits_toBits v h := by
    have hl : ∀ i (hi : i < k), Packed.valid (α := α) (Packed.toBits v[i]) = true ∧
        Packed.ofBits (Packed.toBits v[i]) = v[i] :=
      fun i hi => LawfulPackedVal.ofBits_toBits _ (lane_mask_full v h i hi)
    constructor
    · change (lanesOf (w := w) k (Packed.toBits v)).all (Packed.valid (α := α)) = true
      rw [lanesOf_toBits]
      exact Vector.all_eq_true.mpr fun i hi => by rw [Vector.getElem_map]; exact (hl i hi).1
    · change (lanesOf k (Packed.toBits v)).map Packed.ofBits = v
      rw [lanesOf_toBits]
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_map, Vector.getElem_map]
      exact (hl i hi).2

instance [LawfulPacked α w] : LawfulPacked (Vector α k) (k * w) := LawfulPacked.of

instance [LawfulPackedBits α w] : LawfulPackedBits (Vec α k) (k * w) where
  toBits_ofBits b hb := LawfulPackedBits.toBits_ofBits (α := Vector α k) b hb

instance [LawfulPackedVal α w] : LawfulPackedVal (Vec α k) (k * w) where
  ofBits_toBits v h := by
    obtain ⟨h1, h2⟩ := LawfulPackedVal.ofBits_toBits (α := Vector α k) v.lanes h
    refine ⟨h1, ?_⟩
    cases v
    exact congrArg Vec.mk h2

instance [LawfulPacked α w] : LawfulPacked (Vec α k) (k * w) := LawfulPacked.of

/-- All bits of an array are valid when all bits of a lane are (a packed struct's array field:
its `PField.Valid`). -/
theorem Packed.valid_lanes_of (h : ∀ b : BitVec w, Packed.valid (α := α) b = true)
    (b : BitVec (k * w)) : Packed.valid (α := Vector α k) b = true := by
  change (lanesOf (w := w) k b).all (Packed.valid (α := α)) = true
  exact Vector.all_eq_true.mpr fun _ _ => h _

/-- `Packed.valid_lanes_of` for a vector. -/
theorem Packed.valid_vec_of (h : ∀ b : BitVec w, Packed.valid (α := α) b = true)
    (b : BitVec (k * w)) : Packed.valid (α := Vec α k) b = true :=
  Packed.valid_lanes_of h b

/-- Every bit of an array is determined when every bit of each lane value is (a packed struct's
array field: its `PField.Full`). -/
theorem Packed.mask_lanes_of (h : ∀ x : α, Packed.mask x = BitVec.allOnes w) (v : Vector α k) :
    Packed.mask v = BitVec.allOnes (k * w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hw : 0 < w := Nat.pos_of_ne_zero fun h0 => by simp [h0] at ht
  have hi : t / w < k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ht)
  have hj : t % w < w := Nat.mod_lt _ hw
  have e := BitCast.getLsbD_ofLanes (v.map Packed.mask) (t / w) (t % w) hi hj
  rw [Nat.div_add_mod] at e
  change (Packed.mask v).getLsbD t = _ at e
  rw [e, Vector.getElem_map, h, BitVec.getLsbD_allOnes, BitVec.getLsbD_allOnes, decide_eq_true hj,
    decide_eq_true ht]

/-- `Packed.mask_lanes_of` for a vector. -/
theorem Packed.mask_vec_of (h : ∀ x : α, Packed.mask x = BitVec.allOnes w) (v : Vec α k) :
    Packed.mask v = BitVec.allOnes (k * w) :=
  Packed.mask_lanes_of h v.lanes

end Lanes

/-! ## Packed unions

A packed union (generated `structure U where bytes : Vector Byte size`, `ZigLean/PackedRepr.lean`)
has the bits direction for every union: `ofBits` writes the bits as the integer's bytes and
`toBits` reads them back (`PackedU.bitsOf_intBytes`). It has no value direction: a byte whose bits
are all determined in a form other than `.int` (`.mask 0xFF x`, never made by `ofBits`) reads as
`x` and is rebuilt as `.int x`. -/

/-- Bit `j` of an integer's bytes is the integer's bit `j`. -/
theorem hostBit_intBytes {n : Nat} (b : BitVec n) {j : Nat} (hj : j < n) :
    hostBit (intBytes b) j = some (b.getLsbD j) := by
  have hi : j / 8 < (n + 7) / 8 := by omega
  have hsz : j / 8 < (intBytes b).size := by simp [intBytes]; omega
  unfold hostBit
  rw [Array.getElem?_eq_getElem hsz]
  simp only [intBytes, Array.getElem_map, Array.getElem_range]
  have hjm : j % 8 < 8 := Nat.mod_lt _ (by omega)
  have hbit : (BitVec.ofNat 8 ((b.toNat >>> (8 * (j / 8))) % 256)).getLsbD (j % 8) = b.getLsbD j := by
    rw [BitVec.getLsbD_ofNat, BitVec.getLsbD]
    simp only [hjm, decide_true, Bool.true_and, Nat.shiftRight_eq_div_pow]
    rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [hjm, decide_true, Bool.true_and]
    congr 1
    omega
  split
  · simp only [Byte.bit, Byte.defBits, BitVec.getLsbD_and]
    have hm : (lowMask8 (n - 8 * (j / 8))).getLsbD (j % 8) = true := by
      simp only [lowMask8, BitVec.getLsbD_ofNat, hjm, decide_true, Bool.true_and,
        Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      omega
    simp only [hm, ↓reduceIte, Bool.and_true, hbit]
  · simp only [Byte.bit, Byte.defBits, BitVec.getLsbD_allOnes, hjm, decide_true, ↓reduceIte, hbit]

/-- **A packed union's bits read back**: the union of an integer's bytes (`ofBits`, at least as
many bytes as the integer has) has the integer's bits (`toBits`). -/
theorem PackedU.bitsOf_intBytes {n k : Nat} (b : BitVec n) (hk : (n + 7) / 8 ≤ k) :
    PackedU.bitsOf n (Raw.ofArray k (intBytes b)).toArray = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hjk : j / 8 < k := by omega
  have hsz : j / 8 < (intBytes b).size := by simp [intBytes]; omega
  have e : hostBit (Raw.ofArray k (intBytes b)).toArray j = hostBit (intBytes b) j := by
    unfold hostBit
    rw [Array.getElem?_eq_getElem (by simpa using hjk), Array.getElem?_eq_getElem hsz]
    simp [Raw.ofArray, Array.getD, hsz]
  simp only [PackedU.bitsOf, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some, e,
    hostBit_intBytes b hj]

/-- **Valid bits read back** (`LawfulPackedBits`): the rewrite of the arithmetic normal form. -/
theorem Packed.toBits_ofBits_of {α : Type} {n : Nat} [Packed α n] [LawfulPackedBits α n]
    {b : BitVec n} (h : Packed.valid (α := α) b = true) : Packed.toBits (Packed.ofBits b : α) = b :=
  LawfulPackedBits.toBits_ofBits b h

/-- **A value with every bit determined reads back** (`LawfulPackedVal`): the rewrite of the
arithmetic normal form. -/
theorem Packed.ofBits_toBits_of {α : Type} {n : Nat} [Packed α n] [LawfulPackedVal α n] {v : α}
    (h : Packed.mask v = BitVec.allOnes n) : (Packed.ofBits (Packed.toBits v) : α) = v :=
  (LawfulPackedVal.ofBits_toBits v h).2

/-- **The bits of a value with every bit determined are valid** (`LawfulPackedVal`): the rewrite
of the arithmetic normal form. -/
theorem Packed.valid_toBits_of {α : Type} {n : Nat} [Packed α n] [LawfulPackedVal α n] {v : α}
    (h : Packed.mask v = BitVec.allOnes n) : Packed.valid (α := α) (Packed.toBits v) = true :=
  (LawfulPackedVal.ofBits_toBits v h).1

end Zig
