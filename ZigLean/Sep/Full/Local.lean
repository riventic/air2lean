import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoAttr

/-!
# Escaping locals in the full-state logic (library `Full/Local`)

A local whose address escapes is a stack block (`allocStack`): `fsym` holds its bytes and its
full extent, `up (bytesAt p A S K bs) ⋆ bext b S K`, until `FTotalTriple.free` gives the block
back. The `@[fsym]` rules here are the stores and loads at the start of such a block:
`storeBytesBlock` (raw bytes, `storeUndef`), `storeBlock`, `loadBlock`, `loadBlock_stored` (a
load of what a store wrote) and `loadBlock_u8` (the first item of a `u8` buffer). They are the
native byte rules of `Full/Ops` (`storeBytes_bytesAt`, `load_bytesAt`, no legacy lifting) at
byte 0, with the extent framed.

The same holds in a thread: `FTTriple.storeBytesAt`, `storeAt` and `ptrProjectAt` are the
thread byte rules of `Full/Ops` (`FTTotalTriple.storeBytes_bytesAt`, `ptrProject_of`) at byte
`k`, with the extent framed; `FTTriple.load` and `store` are those of a typed value (`pts`,
size-free: no extent needed); `FTTriple.alloc` and `free'` are in `Full/Block`. A load of a
block's bytes in a thread is `fsym` with the sequential rule (`loadBlock`, or
`FTotalTriple.load_bytesAt` at byte `k`).
-/

namespace Zig
namespace Full

open FAssn

section Block

variable {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
  {al : Nat}

/-- **A store of raw bytes at the start of a block's bytes** held with the block's extent
(`storeUndef` of an escaping local): the bytes become `bs'`, followed by the rest. -/
@[fsym] theorem FTotalTriple.storeBytesBlock {bs' : Array Byte} (_hpb : p.block = some b)
    (hn : 0 < bs'.size) (hk : bs'.size ≤ bs.size) (ha : (A + p.off.toNat) % al = 0)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.storeBytes p al bs')
      (fun _ => up (bytesAt p A S K (writeBytes bs 0 bs')) ⋆ bext b S K) := by
  have t := (FTotalTriple.storeBytes_bytesAt (q := p) (k := 0) (bs := bs) (A := A) (S := S)
    (K := K) (al := al) hn (by omega) (by simpa using ha) hK).frame (R := bext b S K)
  simpa only [Int.natCast_zero, Ptr.add_zero] using t

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

/-- The first byte of a buffer of `u8`s is the encoding of its first item. -/
theorem u8s_extract {vs : Array (BitVec 8)} (hn : 0 < vs.size) :
    (vs.map Byte.int).extract 0 (Enc.size (BitVec 8)) = Enc.encode vs[0]! := by
  have he : Enc.encode vs[0]! = #[Byte.int vs[0]!] := by
    have hr : Array.range 1 = #[0] := by decide
    simp [Enc.encode, padTo, intBytes, intSize, intAlign, alignUp, hr]
    apply BitVec.eq_of_toNat_eq
    have := vs[0]!.isLt
    simp only [BitVec.toNat_ofNat]
    omega
  rw [show Enc.size (BitVec 8) = 1 from rfl, he]
  apply Array.ext
  · simp; omega
  · intro i _ h2
    simp at h2
    subst h2
    simp [hn]

/-- **A load of the first `u8` of a buffer of `u8`s** (the integer bytes that a `std.Random`
fill leaves, `randomFillPost`) at the start of a block's bytes. -/
@[fsym] theorem FTotalTriple.loadBlock_u8 {vs : Array (BitVec 8)} (hpb : p.block = some b)
    (hn : 0 < vs.size) (ha : (A + p.off.toNat) % al = 0) :
    FTotalTriple (up (bytesAt p A S K (vs.map Byte.int)) ⋆ bext b S K) (Zig.load (BitVec 8) al p)
      (fun x => ⟪x = vs[0]!⟫ ⋆ (up (bytesAt p A S K (vs.map Byte.int)) ⋆ bext b S K)) :=
  FTotalTriple.loadBlock hpb (by decide) (by simp [show Enc.size (BitVec 8) = 1 from rfl]; omega)
    (by rw [u8s_extract hn]; exact LawfulEnc.decode_encode _) ha

end Block

/-! ## In a thread -/

namespace FTTriple

variable {p q : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId} {k a : Nat}

/-- A store of the bytes `bs'` at byte `k` of a thread's block, whose full extent it owns. -/
theorem storeBytesAt (bs' : Array Byte) (_hpb : p.block = some b) (hq : q = p.add k)
    (hn : 0 < bs'.size) (hk : k + bs'.size ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0)
    (hK : K ≠ .constGlobal) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.storeBytes q a bs')
      (fun _ => up (bytesAt p A S K (writeBytes bs k bs')) ⋆ bext b S K) := by
  subst hq
  exact (FTTotalTriple.storeBytes_bytesAt hn hk ha hK).frame.toPartial

/-- A store of `w`, whose encoding has the size of `T`, at byte `k` of a thread's block, whose
full extent it owns: a type whose encoding is not `LawfulEnc` (a struct such as `Io.Group`). -/
theorem storeAt' {T : Type} [Enc T] (w : T) (hw : (Enc.encode w).size = Enc.size T)
    (hpb : p.block = some b) (hq : q = p.add k) (hn : 0 < Enc.size T)
    (hk : k + Enc.size T ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0) (hK : K ≠ .constGlobal) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.store a q w)
      (fun _ => up (bytesAt p A S K (writeBytes bs k (Enc.encode w))) ⋆ bext b S K) :=
  storeBytesAt (Enc.encode w) hpb hq (by omega) (by omega) ha hK

/-- A store of `w` at byte `k` of a thread's block, whose full extent it owns. -/
theorem storeAt {T : Type} [Enc T] [LawfulEnc T] (w : T) (hpb : p.block = some b)
    (hq : q = p.add k) (hn : 0 < Enc.size T) (hk : k + Enc.size T ≤ bs.size)
    (ha : (A + p.off.toNat + k) % a = 0) (hK : K ≠ .constGlobal) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.store a q w)
      (fun _ => up (bytesAt p A S K (writeBytes bs k (Enc.encode w))) ⋆ bext b S K) :=
  storeAt' w (LawfulEnc.size_encode w) hpb hq hn hk ha hK

/-- The pointer `k` bytes into a thread's block. -/
theorem ptrProjectAt (hpb : p.block = some b) (hk : k ≤ bs.size) (hpos : 0 < bs.size) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (ptrProject p (·.add k))
      (fun x => ⟪x = p.add k⟫ ⋆ (up (bytesAt p A S K bs) ⋆ bext b S K)) := by
  have hr : Reaches b (p.off.toNat + (bs.size - 1) + 1) (up (bytesAt p A S K bs) ⋆ bext b S K) :=
    (Reaches.owned fun _ hp =>
      (up_bytesAt_cell hp hpb (j := bs.size - 1) (by omega)).imp fun _ h => h.1).sepL
  refine (FTTotalTriple.lift fun h0 => FTTotalTriple.ptrProject_of (k := (k : Int)) hpb hr h0
    (by omega) (by omega) (by omega)).toPartial.pre fun r hp => sep_lift.mpr ⟨?_, hp⟩
  obtain ⟨-, -, -, -, ⟨⟨-, -, h0, -⟩, -⟩, -⟩ := hp
  exact h0

/-- A load of a typed value (`pts`) in a thread. -/
theorem load {T : Type} [Enc T] {v : T} (hn : 0 < Enc.size T) :
    FTTriple (up (pts q a v)) (Zig.load T a q) (fun x => ⟪x = v⟫ ⋆ up (pts q a v)) :=
  (FTTotalTriple.ofSeq (FTotalTriple.load hn) (ThreadLocal.load OwnsPtr.pts)).toPartial

/-- A store of a typed value (`pts`) in a thread. -/
theorem store {T : Type} [Enc T] [LawfulEnc T] {v : T} (hn : 0 < Enc.size T) (w : T) :
    FTTriple (up (pts q a v)) (Zig.store a q w) (fun _ => up (pts q a w)) :=
  (FTTotalTriple.ofSeq (FTotalTriple.store hn w)
    (ThreadLocal.store (by rw [LawfulEnc.size_encode w]; exact OwnsPtr.pts))).toPartial

end FTTriple

end Full
end Zig
