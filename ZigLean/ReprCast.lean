import ZigLean.Mem.Repr
import ZigLean.VecMem

/-!
# Representation casts: round trips and padding

`Zig.reprCast` (`ZigLean/Mem/Repr.lean`) is the Zig ≤0.16 `@bitCast` of an array, `extern`
struct or `extern` union: the destination decoded from the source's memory bytes, padding bytes
undefined (`docs/aggregate-casts.md`). Proof-only (it imports `ZigLean.Mem.Lemmas`), so it is
not part of the `ZigLean` umbrella.

* `reprCast_of_encode_eq`, `reprCast_roundtrip`: if the source's bytes are exactly the
  encoding of a destination value (no padding byte of either type, every byte defined), the cast
  gives that value and casting back gives the source. This is the stated representation
  condition; without it no round trip is claimed.
* `intOfBytes_undef`, `reprCast_int_undef`: a destination integer that needs an undefined
  (padding-derived) byte throws `.unspecified`.
* `lawfulEnc_bitVec`, `lawfulEnc_vector`: integers of every width and arrays of lawful items
  read back as stored, so `reprCast_roundtrip` applies to arrays.
* Concrete cases (by kernel evaluation): `[4]u8 ↔ u32` round-trips; `[2]u24 → u56` reads the
  padding byte of item 0 and throws; `u56 → [2]u24` loses byte 3, so casting back throws.
-/

namespace Zig

theorem padTo_of_size {bs : Array Byte} {n : Nat} (h : bs.size = n) : padTo n bs = bs := by
  subst h; simp [padTo]

/-- The cast lands on any destination value whose encoding is the source's bytes. -/
theorem reprCast_of_encode_eq {α β : Type} [Enc α] [Enc β] [LawfulEnc β] {x : α} {y : β}
    (h : Enc.encode y = Enc.encode x) : reprCast β x = pure y := by
  unfold reprCast
  rw [← h, padTo_of_size (LawfulEnc.size_encode y), LawfulEnc.decode_encode]

/-- The cast to the source's own type is the identity. -/
theorem reprCast_self {α : Type} [Enc α] [LawfulEnc α] (x : α) : reprCast α x = pure x :=
  reprCast_of_encode_eq rfl

/-- Round trip under the stated representation condition: `x` and `y` have the same bytes. -/
theorem reprCast_roundtrip {α β : Type} [Enc α] [LawfulEnc α] [Enc β] [LawfulEnc β]
    {x : α} {y : β} (h : Enc.encode y = Enc.encode x) :
    reprCast β x = pure y ∧ reprCast α y = pure x :=
  ⟨reprCast_of_encode_eq h, reprCast_of_encode_eq h.symm⟩

/-! ## Undefined bytes -/

private abbrev intStep (n : Nat) (trunc : Bool) :
    Byte × Nat → Result (BitVec n) → Result (BitVec n) :=
  fun (b, i) acc => do
    let hi ← acc
    match byteBits n i trunc b with
    | some x => pure (BitVec.ofNat n (x.toNat + 256 * hi.toNat))
    | none => throw .unspecified

/-- `intOfBytes`' fold only returns a value or `.unspecified`. -/
private theorem intFold_cases (n : Nat) (trunc : Bool) (l : List (Byte × Nat)) :
    (∃ v, l.foldr (intStep n trunc) (pure 0) = pure v) ∨
      l.foldr (intStep n trunc) (pure 0) = throw .unspecified := by
  induction l with
  | nil => exact .inl ⟨0, rfl⟩
  | cons p t ih =>
    obtain ⟨b, i⟩ := p
    simp only [List.foldr_cons]
    rcases ih with ⟨v, hv⟩ | hv <;> rw [hv]
    · have e : intStep n trunc (b, i) (pure v) = (match byteBits n i trunc b with
          | some x => pure (BitVec.ofNat n (x.toNat + 256 * v.toNat))
          | none => throw .unspecified : Result (BitVec n)) := rfl
      rw [e]; split
      · exact .inl ⟨_, rfl⟩
      · exact .inr rfl
    · exact .inr rfl

private theorem intFold_bad (n : Nat) (trunc : Bool) (l : List (Byte × Nat)) (b : Byte) (i : Nat)
    (hm : (b, i) ∈ l) (hb : byteBits n i trunc b = none) :
    l.foldr (intStep n trunc) (pure 0) = throw .unspecified := by
  induction l with
  | nil => cases hm
  | cons p t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hm with rfl | ht
    · rcases intFold_cases n trunc t with ⟨v, hv⟩ | hv <;> rw [hv]
      · show (match byteBits n i trunc b with
          | some x => pure (BitVec.ofNat n (x.toNat + 256 * v.toNat))
          | none => throw .unspecified : Result (BitVec n)) = _
        rw [hb]
      · rfl
    · rw [ih ht]; rfl

/-- An integer that needs an undefined byte throws `.unspecified`. -/
theorem intOfBytes_undef {n : Nat} {bs : Array Byte} {i : Nat} (trunc : Bool)
    (hi : i < (n + 7) / 8) (hb : bs[i]? = some .undef) :
    intOfBytes n bs trunc = throw .unspecified := by
  unfold intOfBytes
  rw [← Array.foldr_toList]
  apply intFold_bad n trunc _ .undef i _ rfl
  have hs : i < bs.size := by
    rcases Nat.lt_or_ge i bs.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hb
  rw [Array.mem_toList_iff, Array.mem_zipIdx_iff_getElem?]
  have hb' : bs[i] = .undef := by simpa [Array.getElem?_eq_getElem hs] using hb
  simp [Nat.lt_min, hi, hs, hb']

/-- A cast to an integer that reads a padding (undefined) byte of the source throws
`.unspecified`. -/
theorem reprCast_int_undef {α : Type} [Enc α] {n : Nat} (x : α) {i : Nat}
    (hi : i < (n + 7) / 8) (hb : (padTo (intSize n) (Enc.encode x))[i]? = some .undef) :
    reprCast (BitVec n) x = throw .unspecified :=
  intOfBytes_undef false hi hb

/-! ## Lawful integers and arrays -/

theorem intBytes_size {n : Nat} (v : BitVec n) : (intBytes v).size = (n + 7) / 8 := by
  simp [intBytes]

theorem intBytes_le_intSize (n : Nat) : (n + 7) / 8 ≤ intSize n := by
  unfold intSize; exact le_alignUp _ _

/-- Integers of every width read back as stored. -/
theorem lawfulEnc_bitVec (n : Nat) : LawfulEnc (BitVec n) where
  size_encode v := by
    show (padTo (intSize n) (intBytes v)).size = intSize n
    simp [padTo, intBytes_size]; have := intBytes_le_intSize n; omega
  decode_encode v := by
    show intOfBytes n (padTo (intSize n) (intBytes v)) = pure v
    apply intOfBytes_of_extract
    simp [padTo, Array.extract_append, intBytes_size]

private theorem list_chunk {s : Nat} : ∀ (l : List (List Byte)) (i : Nat), (∀ a ∈ l, a.length = s) →
    (hi : i < l.length) → ((l.flatten.drop (i * s)).take s) = l[i]
  | [], _, _, hi => by simp at hi
  | a :: t, 0, h, _ => by
    have ha := h a (by simp)
    simp [List.flatten_cons, ← ha]
  | a :: t, i + 1, h, hi => by
    have ha := h a (by simp)
    rw [List.flatten_cons, show (i + 1) * s = a.length + i * s by rw [ha, Nat.succ_mul]; omega,
      ← List.drop_drop, List.drop_left]
    exact list_chunk t i (fun b hb => h b (by simp [hb])) (by simpa using hi)

/-- Item `i` of a concatenation of `s`-byte items. -/
theorem flatten_chunk {s : Nat} (l : Array (Array Byte)) (i : Nat) (h : ∀ a ∈ l, a.size = s)
    (hi : i < l.size) : l.flatten.extract (i * s) ((i + 1) * s) = l[i] := by
  apply Array.ext'
  rw [Array.toList_extract, Array.toList_flatten, List.extract_eq_take_drop, show (i + 1) * s - i * s = s by
    rw [Nat.succ_mul]; omega]
  have := list_chunk (s := s) (l.toList.map Array.toList) i
    (by intro a ha; simp at ha; obtain ⟨b, hb, rfl⟩ := ha; simpa using h b (by simpa using hb))
    (by simpa using hi)
  simpa using this

theorem list_mapM_pure_of {α β : Type} {f : α → Result β} {g : α → β} :
    ∀ (l : List α), (∀ x ∈ l, f x = pure (g x)) → l.mapM f = pure (l.map g)
  | [], _ => rfl
  | x :: t, h => by
    rw [List.mapM_cons, h x (by simp), list_mapM_pure_of t (fun y hy => h y (by simp [hy]))]
    simp

/-- `[n]T` of lawful items reads back as stored. -/
theorem lawfulEnc_vector {α : Type} [Enc α] [LawfulEnc α] (n : Nat) : LawfulEnc (Vector α n) where
  size_encode v := by
    show ((v.toArray.map Enc.encode).flatten).size = n * Enc.size α
    rw [← Array.length_toList, Array.toList_flatten]
    simp [List.length_flatten, Function.comp_def, LawfulEnc.size_encode, List.map_const',
      List.sum_replicate_nat]
  decode_encode v := by
    show (do
      let xs ← (Array.range n).mapM fun i =>
        (Enc.decode (((v.toArray.map Enc.encode).flatten).extract (i * Enc.size α) ((i + 1) * Enc.size α)) : Result α)
      if h : xs.size = n then pure ⟨xs, h⟩ else (throw Error.unspecified : Result (Vector α n))) = pure v
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : v = #v[] := by ext i hi; omega
      subst this
      rw [show Array.range 0 = #[] from rfl, Array.mapM_empty]
      rfl
    haveI : Inhabited α := ⟨v[0]⟩
    have hm : (Array.range n).mapM (fun i =>
        (Enc.decode (((v.toArray.map Enc.encode).flatten).extract (i * Enc.size α) ((i + 1) * Enc.size α)) : Result α))
        = pure v.toArray := by
      have hv : ((List.range n).map fun i => v.toArray[i]!).toArray = v.toArray := by
        apply Array.ext
        · simp
        · intro i h1 h2
          have : i < n := by simpa using h1
          simp [this]
      rw [Array.mapM_eq_mapM_toList, list_mapM_pure_of (g := fun i => v.toArray[i]!)]
      · simp only [Array.toList_range, map_pure, hv]
      · intro i hi
        have hi : i < n := by simpa using hi
        rw [flatten_chunk _ i (by simp [LawfulEnc.size_encode]) (by simpa using hi)]
        simp [LawfulEnc.decode_encode, hi]
    rw [hm]
    simp [bind, ExceptT.bind, pure, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]

/-! ## Padding: concrete cases -/

section
attribute [local instance] lawfulEnc_bitVec lawfulEnc_vector

/-- No padding: `[4]u8 → u32` is the little-endian integer, and the round trip holds. -/
theorem reprCast_bytes_u32 :
    reprCast (BitVec 32) (#v[0x11, 0x22, 0x33, 0x44] : Vector (BitVec 8) 4) = pure 0x44332211 ∧
      reprCast (Vector (BitVec 8) 4) (0x44332211 : BitVec 32) = pure #v[0x11, 0x22, 0x33, 0x44] :=
  reprCast_roundtrip (by decide +kernel)

/-- `[2]u24 → u56` (`@bitSizeOf` 56 on both sides): byte 3 is item 0's padding, so the integer
is not defined (natively an unspecified byte: `0x44556600112233` on aarch64-macos). -/
theorem reprCast_u24x2_u56 :
    reprCast (BitVec 56) (#v[0x112233, 0x445566] : Vector (BitVec 24) 2) = throw .unspecified :=
  reprCast_int_undef _ (i := 3) (by decide) (by decide +kernel)

/-- `u56 → [2]u24` drops byte 3 into item 0's padding, so the round trip fails. -/
theorem reprCast_u56_roundtrip_fails :
    (reprCast (Vector (BitVec 24) 2) (0x44556600112233 : BitVec 56)).run =
        some (.ok #v[0x112233, 0x445566]) ∧
      (reprCast (Vector (BitVec 24) 2) (0x44556600112233 : BitVec 56) >>=
        reprCast (BitVec 56)).run = some (.error .unspecified) := by
  decide +kernel

end
end Zig
