import ZigLean.Packed

/-!
# Bit-pointer accesses: defined-bit masks (L08)

The frame of a bit-pointer store (`Zig.storeBits`, `Zig.storeUndefBits`), on the host bytes
(`writeField`):

* `writeField_byte_of_mask_zero`: a host byte with no bit of the field is unchanged;
* `hostBit_writeField_outside`: every bit outside the field keeps its state (defined with its
  value, or undefined), also in a byte that the field shares;
* `hostBit_writeField_inside`: a field bit is the stored value's bit, or undefined for
  `undefined` (`none`): never the whole byte, never a default;
* `defBits_writeBits_none`: `undefined` clears exactly the field's bits of the defined-bit mask;
* `readBits_writeField_same`, `readBits_writeField_disjoint`: a load of the field reads the
  stored value back, and a load of a disjoint field (an adjacent one too) reads what it read
  before the store, whatever the other bits are.

`fieldMaskByte_getLsbD` and `fieldValByte_getLsbD` are the host-width/bit-offset encoding: bit
`k` of host byte `i` is host bit `8 * i + k`, field bit `8 * i + k - o`.
-/

namespace Zig

theorem defBits_ofDefBits (d x : BitVec 8) :
    (Byte.ofDefBits d x).defBits = some (d, x &&& d) := by
  unfold Byte.ofDefBits
  split
  · subst_vars; simp only [Byte.defBits, BitVec.and_allOnes]
  · split
    · subst_vars; simp [Byte.defBits]
    · split
      · rename_i m hm
        have h := List.find?_some hm
        simp only [decide_eq_true_eq] at h
        simp [Byte.defBits, h, BitVec.and_assoc]
      · simp [Byte.defBits, BitVec.and_assoc]

theorem bit_ofDefBits (d x : BitVec 8) (k : Nat) :
    (Byte.ofDefBits d x).bit k = if d.getLsbD k then some (x.getLsbD k) else none := by
  simp only [Byte.bit, defBits_ofDefBits, BitVec.getLsbD_and]
  by_cases h : d.getLsbD k <;> simp [h]

/-- A byte without field bits is unchanged. -/
theorem writeBits_zero (v : Option (BitVec 8)) (b : Byte) : b.writeBits 0 v = b := by
  simp [Byte.writeBits]

private theorem bit_of_defBits_getD (b : Byte) (k : Nat) :
    b.bit k = (let (d, x) := b.defBits.getD (0, 0); if d.getLsbD k then some (x.getLsbD k) else none) := by
  unfold Byte.bit
  cases b.defBits <;> simp

/-- A bit outside the mask keeps its state. -/
theorem bit_writeBits_out {f : BitVec 8} {k : Nat} (hk : f.getLsbD k = false)
    (v : Option (BitVec 8)) (b : Byte) : (b.writeBits f v).bit k = b.bit k := by
  unfold Byte.writeBits
  split
  · rfl
  · rw [bit_of_defBits_getD b k]
    obtain ⟨d, x⟩ := b.defBits.getD (0, 0)
    rcases Nat.lt_or_ge k 8 with hk8 | hk8
    · have hk' : f[k] = false := by simpa [BitVec.getLsbD_eq_getElem hk8] using hk
      cases v <;> simp [bit_ofDefBits, hk', hk8]
    · have hd : d.getLsbD k = false := BitVec.getLsbD_of_ge d k hk8
      cases v <;> simp [bit_ofDefBits, hd, BitVec.getLsbD_of_ge _ k hk8]

/-- A bit in the mask is the new bit, or undefined. -/
theorem bit_writeBits_in {f : BitVec 8} {k : Nat} (hk : f.getLsbD k = true)
    (v : Option (BitVec 8)) (b : Byte) :
    (b.writeBits f v).bit k = v.map (·.getLsbD k) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hk
  have hk8 : k < 8 := by
    rcases Nat.lt_or_ge k 8 with h | h
    · exact h
    · rw [BitVec.getLsbD_of_ge f k h] at hk; cases hk
  have hk' : f[k] = true := by simpa [BitVec.getLsbD_eq_getElem hk8] using hk
  unfold Byte.writeBits
  split
  · contradiction
  · obtain ⟨d, x⟩ := b.defBits.getD (0, 0)
    cases v <;> simp [bit_ofDefBits, hk', hk8]

/-- `undefined` clears exactly the mask's bits of the defined-bit mask (per bit, not per byte). -/
theorem defBits_writeBits_none {f d x : BitVec 8} {b : Byte} (hf : f ≠ 0)
    (hb : b.defBits = some (d, x)) :
    (b.writeBits f none).defBits = some (d &&& ~~~f, x &&& ~~~f &&& (d &&& ~~~f)) := by
  unfold Byte.writeBits
  split
  · contradiction
  · simp [hb, defBits_ofDefBits]

/-- The host-width/bit-offset encoding of the field mask: bit `k` of byte `i` is in the
`n`-bit field at bit `o` iff host bit `8 * i + k` is. -/
theorem fieldMaskByte_getLsbD (o n i k : Nat) :
    (fieldMaskByte o n i).getLsbD k = (decide (k < 8) && decide (o ≤ 8 * i + k) &&
      decide (8 * i + k < o + n)) := by
  simp only [fieldMaskByte, BitVec.getLsbD_ofNat, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : k < 8 <;> by_cases h2 : o ≤ 8 * i + k <;> simp [h1, h2] <;> omega

theorem fieldValByte_getLsbD {n : Nat} (v : BitVec n) (o i k : Nat) (hk : k < 8)
    (ho : o ≤ 8 * i + k) : (fieldValByte v o i).getLsbD k = v.getLsbD (8 * i + k - o) := by
  rw [fieldValByte, BitVec.getLsbD_ofNat, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  simp [hk, ho, BitVec.getLsbD]

@[simp] theorem size_writeField {n : Nat} (bs : Array Byte) (o : Nat) (v : Option (BitVec n)) :
    (writeField bs o v).size = bs.size := by
  simp [writeField]

theorem getElem_writeField {n : Nat} (bs : Array Byte) (o : Nat) (v : Option (BitVec n)) (i : Nat)
    (h : i < (writeField bs o v).size) :
    (writeField bs o v)[i] = (bs[i]'(by simpa using h)).writeBits (fieldMaskByte o n i)
      (v.map (fieldValByte · o i)) := by
  simp [writeField]

/-- A host byte that has no bit of the field is the same byte after the store. -/
theorem writeField_byte_of_mask_zero {n : Nat} (bs : Array Byte) (o : Nat) (v : Option (BitVec n))
    (i : Nat) (h : i < bs.size) (hm : fieldMaskByte o n i = 0) :
    (writeField bs o v)[i]'(by simpa using h) = bs[i] := by
  rw [getElem_writeField, hm, writeBits_zero]

private theorem hostBit_writeField {n : Nat} (bs : Array Byte) (o : Nat) (v : Option (BitVec n))
    (j : Nat) : hostBit (writeField bs o v) j =
      match bs[j / 8]? with
      | some b => (b.writeBits (fieldMaskByte o n (j / 8)) (v.map (fieldValByte · o (j / 8)))).bit (j % 8)
      | none => none := by
  unfold hostBit
  by_cases h : j / 8 < bs.size
  · rw [Array.getElem?_eq_getElem (by simpa using h), Array.getElem?_eq_getElem h,
      getElem_writeField]
  · rw [Array.getElem?_eq_none (by simpa using h), Array.getElem?_eq_none (by omega)]

/-- **Adjacent bits remain unchanged**: every host bit outside the field keeps its state, defined
or undefined, after a store of a value or of `undefined` (`none`). -/
theorem hostBit_writeField_outside {n : Nat} (bs : Array Byte) (o : Nat) (v : Option (BitVec n))
    (j : Nat) (hj : j < o ∨ o + n ≤ j) : hostBit (writeField bs o v) j = hostBit bs j := by
  rw [hostBit_writeField]
  unfold hostBit
  cases bs[j / 8]? with
  | none => rfl
  | some b =>
    apply bit_writeBits_out
    rw [fieldMaskByte_getLsbD]
    have : 8 * (j / 8) + j % 8 = j := Nat.div_add_mod j 8
    rcases hj with hj | hj <;> simp [this] <;> omega

/-- A field bit after the store: the value's bit, or undefined for `undefined` (`none`). -/
theorem hostBit_writeField_inside {n : Nat} (bs : Array Byte) (o : Nat) (v : Option (BitVec n))
    (j : Nat) (hj : o ≤ j ∧ j < o + n) (hs : j / 8 < bs.size) :
    hostBit (writeField bs o v) j = v.map (·.getLsbD (j - o)) := by
  rw [hostBit_writeField, Array.getElem?_eq_getElem hs]
  have hjk : 8 * (j / 8) + j % 8 = j := Nat.div_add_mod j 8
  have hm : (fieldMaskByte o n (j / 8)).getLsbD (j % 8) = true := by
    rw [fieldMaskByte_getLsbD]; simp [hjk]; omega
  simp only
  rw [bit_writeBits_in hm]
  cases v with
  | none => rfl
  | some v =>
    simp only [Option.map_some]
    rw [fieldValByte_getLsbD v o (j / 8) (j % 8) (Nat.mod_lt _ (by decide)) (by omega), hjk]

/-- `readBits` is `some w` exactly when each of the `n` bits is defined with `w`'s bit. -/
theorem readBits_eq_some {bs : Array Byte} {o : Nat} :
    ∀ {n : Nat} {w : BitVec n},
      readBits bs o n = some w ↔ ∀ k < n, hostBit bs (o + k) = some (w.getLsbD k)
  | 0, w => by simp [readBits, Subsingleton.elim w 0#0]
  | n + 1, w => by
    constructor
    · intro h k hk
      simp only [readBits, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨hi, hhi, lo, hlo, rfl⟩ := h
      have ih := (readBits_eq_some (n := n)).mp hlo
      rw [BitVec.getLsbD_cons]
      split
      · subst_vars; exact hhi
      · exact ih k (by omega)
    · intro h
      have hlo : readBits bs o n = some (w.setWidth n) :=
        (readBits_eq_some (n := n)).mpr fun k hk => by
          rw [h k (by omega), BitVec.getLsbD_setWidth]; simp [hk]
      have hw : w = BitVec.cons (w.getLsbD n) (w.setWidth n) := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        rw [BitVec.getLsbD_cons]
        split
        · subst_vars; rfl
        · rw [BitVec.getLsbD_setWidth]; simp; omega
      simp only [readBits, hlo, h n (by omega), Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]
      exact congrArg some hw.symm

/-- `readBits` depends only on the host bits that it reads. -/
theorem readBits_congr {bs bs' : Array Byte} {o : Nat} :
    ∀ {n : Nat}, (∀ k < n, hostBit bs (o + k) = hostBit bs' (o + k)) →
      readBits bs o n = readBits bs' o n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [readBits, h n (by omega), readBits_congr (n := n) fun k hk => h k (by omega)]

/-- **A store reads back**: a load of the field after a store of `v` is `v`. -/
theorem readBits_writeField_same {n : Nat} (bs : Array Byte) (o : Nat) (v : BitVec n)
    (hs : o + n ≤ 8 * bs.size) : readBits (writeField bs o (some v)) o n = some v := by
  rw [readBits_eq_some]
  intro k hk
  rw [hostBit_writeField_inside bs o (some v) (o + k) ⟨by omega, by omega⟩ (by omega)]
  simp

/-- **A disjoint field is unaffected**: after a store to the field at `o` (a value, or
`undefined`), a load of a disjoint field at `o'` (adjacent or not, in the same bytes or not)
reads what it read before, defined or not. -/
theorem readBits_writeField_disjoint {n n' : Nat} (bs : Array Byte) (o o' : Nat)
    (v : Option (BitVec n)) (h : o' + n' ≤ o ∨ o + n ≤ o') :
    readBits (writeField bs o v) o' n' = readBits bs o' n' :=
  readBits_congr fun k hk => hostBit_writeField_outside bs o v (o' + k) (by omega)

/-- **`undefined` makes the field undefined**: a load of the field after a store of
`undefined` throws (`readBits` is `none`), whatever was there before. -/
theorem readBits_writeField_none {n : Nat} (bs : Array Byte) (o : Nat) (hn : 0 < n)
    (hs : o + n ≤ 8 * bs.size) : readBits (writeField bs o (none : Option (BitVec n))) o n = none := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [readBits]
  rw [hostBit_writeField_inside bs o none (o + m) ⟨by omega, by omega⟩ (by omega)]
  rfl

end Zig
