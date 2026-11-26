import ZigLean.Sep.Full.Region
import ZigLean.ReprCast

/-!
# Items of any encoding in a byte region

`Region.lean`'s item rules (`regionStore`, `regionLoadWritten`) ask for `LawfulEnc T`: every
value of `T` reads back from its bytes. Not every item type has that instance: a float's NaN has
undefined bytes (`Float.detMask`), so a load of them is `.unspecified`. The rules here are stated
for every `Enc T` and ask for what one step needs, as facts about the one value:

* a **store** needs the size of the value's bytes (`regionStoreEnc`): the region holds the bytes
  afterwards, whatever they are (as `Auto.Bytes.storeEnc_region` at a region's start);
* a **load** of bytes a store wrote needs that this value reads back (`regionLoadEnc`).

Both facts hold for every value of a `LawfulEnc` type, so the rules cover `Region.lean`'s. A proof
whose items have no `LawfulEnc` instance names them: `fsym [regionStoreEnc, regionLoadEnc]`. For
a float the two facts are `Float.size_encode` and the decidable read-back
`Float.decidableReadsBack` (`ZigLean/ReprCast.lean`): a float constant's is its NaN check.

An optional pointer item's `==` (`optPtrEqAddr`, a `[:null]?*T`'s sentinel check) is normalized by
the shape of its operands (`optPtrEqAddr_none_none` and its three siblings).
-/

namespace Zig

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
