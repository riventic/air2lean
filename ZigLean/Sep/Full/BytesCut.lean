import ZigLean.Sep.Full.ThreadFacts

/-!
# A run of bytes cut at a list of offsets

`bytesAt_split` (`ZigLean/Sep/Assert.lean`) cuts a run of bytes once. A proof that gives the
fields of an object to different owners (a lock's words to its protocol, the rest to the program)
cuts the object's bytes at every field's offset. This file does that once, for every pointer,
block and list of offsets.

- `up_bytesAt_cut`: the bytes `a .. c` of `bs` at `p + a` are the bytes `a .. b` and `b .. c`.
- `bytesCut p A S K bs a l c`: the bytes `a .. c` of `bs` at `p`, in the pieces that end at the
  offsets `l`; `Cuts a l c`: the offsets are in order between `a` and `c`.
- `up_bytesAt_cuts`, `up_bytesAt_cuts0`: a run of bytes is its pieces (from `a`; the whole of `bs`
  at `p`).
-/

namespace Zig
namespace Full

open FAssn

variable {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}

/-- The bytes `a .. c` of `bs` at `p + a` are the bytes `a .. b` and `b .. c`. -/
theorem up_bytesAt_cut {a b c : Nat} {r : Res}
    (h : up (bytesAt (p.add (a : Int)) A S K (bs.extract a c)) r) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c ≤ bs.size) :
    (up (bytesAt (p.add (a : Int)) A S K (bs.extract a b)) ⋆
      up (bytesAt (p.add (b : Int)) A S K (bs.extract b c))) r := by
  have hsz : (bs.extract a c).size = c - a := by simp; omega
  have := up_sep ⟨bytesAt_split h.1 (k := b - a) (by omega), h.2⟩
  have e1 : (bs.extract a c).extract 0 (b - a) = bs.extract a b := by
    rw [Array.extract_extract]; congr 1 <;> omega
  have e2 : (bs.extract a c).extract (b - a) (bs.extract a c).size = bs.extract b c := by
    rw [Array.extract_extract, hsz]; congr 1 <;> omega
  have e3 : (p.add (a : Int)).add ((b - a : Nat) : Int) = p.add (b : Int) := by
    rw [Ptr.add_add]; congr 1; omega
  rwa [e1, e2, e3] at this

/-- The bytes `a .. c` of `bs` at `p`, in the pieces that end at the offsets `l` (module doc). -/
def bytesCut (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) : Nat → List Nat → Nat → FAssn
  | a, [], c => up (bytesAt (p.add (a : Int)) A S K (bs.extract a c))
  | a, b :: l, c => up (bytesAt (p.add (a : Int)) A S K (bs.extract a b)) ⋆ bytesCut p A S K bs b l c

/-- The offsets `l` are in order between `a` and `c`. -/
def Cuts : Nat → List Nat → Nat → Prop
  | a, [], c => a ≤ c
  | a, b :: l, c => a ≤ b ∧ Cuts b l c

theorem Cuts.le : ∀ {l : List Nat} {a c : Nat}, Cuts a l c → a ≤ c
  | [], _, _, h => h
  | _ :: _, _, _, h => Nat.le_trans h.1 h.2.le

/-- **A run of bytes is its pieces**: the bytes `a .. c` of `bs` at `p + a`, cut at the offsets
`l`. -/
theorem up_bytesAt_cuts : ∀ (l : List Nat) {a c : Nat} {r : Res}, Cuts a l c → c ≤ bs.size →
    up (bytesAt (p.add (a : Int)) A S K (bs.extract a c)) r → bytesCut p A S K bs a l c r
  | [], _, _, _, _, _, h => h
  | _ :: l, _, _, _, hl, hc, h =>
    sep_mono_right (fun _ h' => up_bytesAt_cuts l hl.2 hc h') (up_bytesAt_cut h hl.1 hl.2.le hc)

/-- `up_bytesAt_cuts` for the whole of `bs` at `p`. -/
theorem up_bytesAt_cuts0 {l : List Nat} {r : Res} (h : up (bytesAt p A S K bs) r)
    (hl : Cuts 0 l bs.size) : bytesCut p A S K bs 0 l bs.size r := by
  refine up_bytesAt_cuts l hl (Nat.le_refl _) ?_
  have e : p.add ((0 : Nat) : Int) = p := by cases p; simp [Ptr.add]
  rw [e, Array.extract_size]; exact h

end Full
end Zig
