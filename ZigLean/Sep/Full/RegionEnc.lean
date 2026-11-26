import ZigLean.Sep.Full.Region
import ZigLean.VecMem
import ZigLean.ReprCast
import ZigLean.Float.Ops

/-!
# Items of any encoding in a byte region

`Region.lean`'s item rules (`regionStore`, `regionLoadWritten`) ask for `LawfulEnc T`: every
value of `T` reads back from its bytes. A float type has no such instance: a NaN's bytes are
undefined (`Float.detMask`), so a load of them is `.unspecified`. The rules here ask for what
one step needs, as facts about the one value:

* a **store** needs the size of the value's bytes (`regionStoreEnc`): the region holds the bytes
  afterwards, whatever they are (as `Auto.Bytes.storeEnc_region` at a region's start);
* a **load** of bytes a store wrote needs that this value reads back (`regionLoadEnc`).

Both hold for every `LawfulEnc` type, so the rules cover `Region.lean`'s. A proof whose items have
no `LawfulEnc` instance names them: `fsym [regionStoreEnc, regionLoadEnc]`.

For a float of every format: its bytes have the format's size (`Float.size_encode`), and it reads
back exactly when it is not a NaN (`Float.decode_encode_eq`; decidable so,
`Float.decidableReadsBack`: a float constant's read-back is its NaN check, which evaluates); the
float with the bits `0` is not a NaN
(`Float.isNaN_ofBits_zero`), and a float that is not a NaN equals itself (`Float.eq_self`).

An optional pointer item's `==` (`optPtrEqAddr`, a `[:null]?*T`'s sentinel check) is normalized by
the shape of its operands (`optPtrEqAddr_none_none` and its three siblings).
-/

namespace Zig

/-! ## A float's bytes -/

/-- A float's encoding has its format's size: the NaN's too (undefined bytes). -/
@[fsym_arith] theorem Float.size_encode {fmt : FloatFmt} (x : Float fmt) :
    (Enc.encode x).size = Enc.size (Float fmt) := by
  have h := intBytes_le_intSize fmt.width
  show (padTo (intSize fmt.width) (maskedBytes x.bits x.detMask)).size = intSize fmt.width
  simp only [padTo, Array.size_append, Array.size_replicate, maskedBytes, Array.size_map,
    Array.size_range]
  omega

/-- A float that is not a NaN reads back from its bytes. -/
theorem Float.decode_encode {fmt : FloatFmt} {x : Float fmt} (h : x.isNaN = false) :
    Enc.decode (Enc.encode x) = pure x := by
  show (do pure ⟨← intOfBytes fmt.width
    (padTo (intSize fmt.width) (maskedBytes x.bits x.detMask))⟩ : Result (Float fmt)) = pure x
  rw [Float.maskedBytes_of_not_isNaN h, intOfBytes_of_extract x.bits (by
    rw [padTo, Array.extract_append]
    simp [intBytes_size, Array.extract_eq_self_of_le])]
  rfl

/-- A float reads back from its bytes exactly when it is not a NaN: a NaN's bits are undefined in
memory (`docs/floats.md` §NaN in memory), so its load is `.unspecified`. -/
theorem Float.decode_encode_eq {fmt : FloatFmt} (x : Float fmt) :
    (Enc.decode (Enc.encode x) = pure x) = (x.isNaN = false) := by
  refine propext ⟨fun h => ?_, Float.decode_encode⟩
  cases hn : x.isNaN with
  | false => rfl
  | true =>
    exfalso
    have hw : 0 < (fmt.width + 7) / 8 := by cases fmt <;> decide
    have e : intOfBytes fmt.width
        (padTo (intSize fmt.width) (maskedBytes x.bits x.detMask)) = throw .unspecified :=
      intOfBytes_undef false (i := 0) hw (by
        rw [Float.maskedBytes_of_isNaN hn, padTo, Array.getElem?_append_left (by simpa using hw)]
        simp [hw])
    have h' : (do pure ⟨← intOfBytes fmt.width
        (padTo (intSize fmt.width) (maskedBytes x.bits x.detMask))⟩ : Result (Float fmt)) =
        pure x := h
    rw [e] at h'
    cases h'

/-- Whether a float reads back is its NaN check: for a float constant it evaluates (`decide`), so
`regionLoadEnc`'s read-back premise of a float sentinel is a closed fact. -/
instance Float.decidableReadsBack {fmt : FloatFmt} (x : Float fmt) :
    Decidable (Enc.decode (Enc.encode x) = pure x) :=
  decidable_of_iff (x.isNaN = false) (by rw [Float.decode_encode_eq])

/-- The float with the bits `0` (`+0.0`) is not a NaN, in every format. -/
@[simp, fsym_arith] theorem Float.isNaN_ofBits_zero {fmt : FloatFmt} :
    (Float.ofBits (0 : BitVec fmt.width)).isNaN = false := by
  cases fmt <;> decide

/-- A float that is not a NaN equals itself (the sentinel check of a `[:z]fN`). -/
@[fsym_arith] theorem Float.eq_self {fmt : FloatFmt} {x : Float fmt} (h : x.isNaN = false) :
    Float.eq x x = true := by
  unfold Float.isNaN at h
  unfold Float.eq
  cases hc : x.classify <;> simp_all

/-! ## `==` on optional pointers

`optPtrEqAddr` by the shape of its operands, as program normalization (`fsym_norm`): two nulls are
equal and a null and a pointer are not, without a step; two pointers compare as `ptrEqAddr`,
which the pointer rules execute. -/

@[fsym_norm] theorem optPtrEqAddr_none_none : optPtrEqAddr none none = pure true := rfl

@[fsym_norm] theorem optPtrEqAddr_none_some (q : Ptr) : optPtrEqAddr none (some q) = pure false :=
  rfl

@[fsym_norm] theorem optPtrEqAddr_some_none (p : Ptr) : optPtrEqAddr (some p) none = pure false :=
  rfl

@[fsym_norm] theorem optPtrEqAddr_some_some (p q : Ptr) :
    optPtrEqAddr (some p) (some q) = ptrEqAddr p q := rfl

namespace Full
namespace FTotalTriple

open FAssn

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}

/-- **Store an item** `v` of any encoding at item `i` of a region (aligned to `al`): its bytes are
`v`'s. `hsz` is the one fact about `v`'s encoding the step needs. -/
theorem regionStoreEnc {T : Type} [Enc T] {i : BitVec 64} {al : Nat} (v : T)
    (hsz : (Enc.encode v).size = Enc.size T) (hpos : 0 < Enc.size T)
    (ho : Enc.size T * i.toNat + Enc.size T ≤ bs.size) (hal : al ∣ a)
    (halo : al ∣ Enc.size T * i.toNat) :
    FTotalTriple (up (regionIn p A S K a bs)) (Zig.store al (p.elem (Enc.size T) i) v)
      (fun _ => up (regionIn p A S K a (writeBytes bs (Enc.size T * i.toNat) (Enc.encode v)))) := by
  rw [Ptr.elem_eq]
  exact region_of' fun hA hK => store_bytesAt v (by rw [hsz]; exact hpos)
    (by rw [hsz]; exact ho) (mod_add_dvd hA hal halo) hK

/-- **Load an item a store wrote** (at item `i`, byte `o`), for a value `v` that reads back from
its bytes (`hdec`): its value. -/
theorem regionLoadEnc {T : Type} [Enc T] {i : BitVec 64} {al o : Nat} {v : T}
    (hsz : (Enc.encode v).size = Enc.size T) (hdec : Enc.decode (Enc.encode v) = pure v)
    (hpos : 0 < Enc.size T) (ho : o + Enc.size T ≤ bs.size) (hoi : Enc.size T * i.toNat = o)
    (hal : al ∣ a) (halo : al ∣ o) :
    FTotalTriple (up (regionIn p A S K a (writeBytes bs o (Enc.encode v))))
      (Zig.load T al (p.elem (Enc.size T) i))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K a (writeBytes bs o (Enc.encode v)))) := by
  have hs : (writeBytes bs o (Enc.encode v)).size = bs.size := writeBytes_size _ _ _ (by omega)
  rw [Ptr.elem_eq, hoi]
  refine region_of fun hA _ => load_bytesAt hpos (by omega) (mod_add_dvd hA hal halo) ?_
  have e := extract_writeBytes bs o (Enc.encode v) (by omega)
  rw [hsz] at e
  rw [e]; exact hdec

end FTotalTriple
end Full
end Zig
