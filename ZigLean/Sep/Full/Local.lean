import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AutoAttr

/-!
# Escaping locals in the full-state logic (library `Full/Local`)

A local whose address escapes is a stack block (`allocStack`): `fsym` holds its bytes and its
full extent, `up (bytesAt p A S K bs) ⋆ bext b S K`, until `FTotalTriple.free` gives the block
back. The `@[fsym]` rules here are the stores and loads at the start of such a block:
`storeBlock`, `loadBlock` and `loadBlock_stored` (a load of what a store wrote). They are the
native byte rules of `Full/Ops` (`storeBytes_bytesAt`, `load_bytesAt`, no legacy lifting) at
byte 0, with the extent framed.
-/

namespace Zig
namespace Full

open FAssn

section Block

variable {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
  {al : Nat}

/-- **A store at the start of a block's bytes** held with the block's extent (an escaping local):
the bytes become the value's, followed by the rest. -/
@[fsym] theorem FTotalTriple.storeBlock (w : T) (_hpb : p.block = some b)
    (hn : 0 < (Enc.encode w).size) (hk : (Enc.encode w).size ≤ bs.size)
    (ha : (A + p.off.toNat) % al = 0) (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.store al p w)
      (fun _ => up (bytesAt p A S K (writeBytes bs 0 (Enc.encode w))) ⋆ bext b S K) := by
  have t := (FTotalTriple.store_bytesAt (q := p) (k := 0) (bs := bs) (A := A) (S := S) (K := K)
    w hn (by omega) (by simpa using ha) hK).frame (R := bext b S K)
  simpa only [Int.natCast_zero, Ptr.add_zero] using t

/-- **A load at the start of a block's bytes** held with the block's extent, whose first bytes
decode to `v`. -/
@[fsym] theorem FTotalTriple.loadBlock {v : T} (_hpb : p.block = some b) (hn : 0 < Enc.size T)
    (hk : Enc.size T ≤ bs.size) (hv : Enc.decode (bs.extract 0 (Enc.size T)) = pure v)
    (ha : (A + p.off.toNat) % al = 0) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.load T al p)
      (fun x => ⟪x = v⟫ ⋆ (up (bytesAt p A S K bs) ⋆ bext b S K)) := by
  have t := (FTotalTriple.load_bytesAt (q := p) (k := 0) (al := al) (bs := bs) (A := A) (S := S)
    (K := K) hn (by omega) (by simpa using ha) (by simpa using hv)).frame (R := bext b S K)
  simp only [Int.natCast_zero, Ptr.add_zero] at t
  exact t.post fun _ _ h => sep_assoc h

/-- **A load of the value stored at the start of a block's bytes** (`storeBlock`, then
`loadBlock`): it reads back what was stored. -/
@[fsym] theorem FTotalTriple.loadBlock_stored [LawfulEnc T] {w : T} (hpb : p.block = some b)
    (hn : 0 < Enc.size T) (hk : Enc.size T ≤ bs.size) (ha : (A + p.off.toNat) % al = 0) :
    FTotalTriple (up (bytesAt p A S K (writeBytes bs 0 (Enc.encode w))) ⋆ bext b S K)
      (Zig.load T al p)
      (fun x => ⟪x = w⟫ ⋆ (up (bytesAt p A S K (writeBytes bs 0 (Enc.encode w))) ⋆ bext b S K)) := by
  have hs := LawfulEnc.size_encode w
  refine FTotalTriple.loadBlock hpb hn (by rw [writeBytes_size _ _ _ (by omega)]; omega) ?_ ha
  have e := extract_writeBytes bs 0 (Enc.encode w) (by omega)
  rw [hs, Nat.zero_add] at e
  rw [e]; exact LawfulEnc.decode_encode w

end Block

end Full
end Zig
