import ZigLean.PackedRepr

/-!
# Packed layouts: a packed value's bits read back (engine ledger #packed-roundtrip)

**`LawfulPacked α n`**: bits that are a value (`valid`) are the bits of the value they make
(`toBits_ofBits`), and a value whose bits are all determined (`mask`) is the value of its bits,
which are valid (`ofBits_toBits`). Integers, `bool` and floats are lawful by the instances here
(a float's `ofBits_toBits` asks for determined bits: a NaN has none, so the law says nothing of
it). An exhaustive enum is lawful by its tags (`EnumTags.lawful`); a non-exhaustive one, whose
value is its bits, by definition.

**`PackedLayout α n`** describes a packed struct as the translator generates it, once for all
packed structs: its fields (`PField`: the type's representation, the bit offset and the value),
in order from bit 0, tile the backing integer (`PTiles`); `toBits` ors each field's bits at its
offset (`toBits_eq`), `ofBits` reads each field at its offset (`ofBits_read`), the bits are valid
exactly when each field's are (`valid_iff`), every bit is determined only if each field's are
(`mask_full`), and a value is its fields (`ext`). `PackedLayout.lawful` proves the round trip once
for every layout whose fields are lawful. The per-type obligations (the layout's fields) are
discharged by `fsym` from the generated instance (`lawfulPackedOf?`, `Auto.lean`). A type of
another shape (a packed union, an array) gets no instance, and the rules that need one do not
apply (fail closed).
-/

namespace Zig

/-- **A packable type's bits read back**: valid bits are the bits of the value they make, and a
value with every bit determined is the value of its bits, which are valid. -/
class LawfulPacked (α : Type) (n : Nat) [Packed α n] : Prop where
  toBits_ofBits : ∀ b : BitVec n, Packed.valid (α := α) b = true →
    Packed.toBits (Packed.ofBits b : α) = b
  ofBits_toBits : ∀ v : α, Packed.mask v = BitVec.allOnes n →
    Packed.valid (α := α) (Packed.toBits v) = true ∧ Packed.ofBits (Packed.toBits v) = v

instance {n : Nat} : LawfulPacked (BitVec n) n where
  toBits_ofBits _ _ := rfl
  ofBits_toBits _ _ := ⟨rfl, rfl⟩

instance : LawfulPacked Bool 1 where
  toBits_ofBits b _ := by
    show (if b == 1#1 then 1#1 else 0#1) = b
    rcases (by decide : ∀ c : BitVec 1, c = 0#1 ∨ c = 1#1) b with rfl | rfl <;> rfl
  ofBits_toBits v _ := by cases v <;> exact ⟨rfl, rfl⟩

instance {fmt : FloatFmt} : LawfulPacked (Float fmt) fmt.width where
  toBits_ofBits _ _ := rfl
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

/-- **Valid bits read back**, for a layout of lawful fields. -/
theorem toBits_ofBits (L : PackedLayout α n) (hl : ∀ v, PAll PField.Lawful (L.fields v))
    (b : BitVec n) (hb : Packed.valid (α := α) b = true) :
    Packed.toBits (Packed.ofBits b : α) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨f, hf, h1, h2⟩ := PTiles.cover (L.fields_tiles (Packed.ofBits b)) j (Nat.zero_le _) hj
  have hr := (L.ofBits_read b).mem f hf
  have hv := ((L.valid_iff b).mp hb).mem f hf
  have hlf := (hl _).mem f hf
  have hfb : f.toBits = b.extractLsb' f.off f.w := by
    unfold PField.toBits; rw [hr]; exact @LawfulPacked.toBits_ofBits f.U f.w f.inst hlf _ hv
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
of lawful fields. -/
theorem ofBits_toBits (L : PackedLayout α n) (hl : ∀ v, PAll PField.Lawful (L.fields v))
    (v : α) (hm : Packed.mask v = BitVec.allOnes n) :
    Packed.valid (α := α) (Packed.toBits v) = true ∧ Packed.ofBits (Packed.toBits v) = v := by
  have hfull := L.mask_full v hm
  have hf : ∀ f ∈ L.fields v, (Packed.toBits v).extractLsb' f.off f.w = f.toBits ∧
      @Packed.valid f.U f.w f.inst f.toBits = true ∧ @Packed.ofBits f.U f.w f.inst f.toBits = f.val := by
    intro f hf
    have := @LawfulPacked.ofBits_toBits f.U f.w f.inst ((hl v).mem f hf) f.val (hfull.mem f hf)
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

/-- **A packed struct of lawful fields is lawful.** -/
theorem lawful (L : PackedLayout α n) (hl : ∀ v, PAll PField.Lawful (L.fields v)) :
    LawfulPacked α n :=
  ⟨L.toBits_ofBits hl, L.ofBits_toBits hl⟩

end PackedLayout

/-- **Valid bits read back** (`LawfulPacked`): the rewrite of the arithmetic normal form. -/
theorem Packed.toBits_ofBits_of {α : Type} {n : Nat} [Packed α n] [LawfulPacked α n] {b : BitVec n}
    (h : Packed.valid (α := α) b = true) : Packed.toBits (Packed.ofBits b : α) = b :=
  LawfulPacked.toBits_ofBits b h

end Zig
