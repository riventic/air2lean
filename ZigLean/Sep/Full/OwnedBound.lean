import ZigLean.Sep.Full.Reclaim

/-!
# Owned bytes fit in the address space

A resource that holds in a full-state memory (`Holds`, `Mem.FSeq`) owns live bytes of live blocks
(`Holds.block`); two live blocks share no byte address (`Mem.LiveDisjoint`) and every live block
ends below `2 ^ 63` (`Mem.LiveBounded`). So the bytes it owns have pairwise different addresses
below `2 ^ 63`, and **at most `2 ^ 63` bytes are owned** (`Holds.owned_length_le`).

A client sums sizes of separately owned objects with an overflow-checked addition (the arena's
`countListCapacity` over its nodes): the objects' bytes, as a list of owned bytes (`OwnsList`,
composed over `⋆`), are at most `2 ^ 63`, so the checked `+` of 64-bit words does not overflow. No
premise: the bound follows from the memory invariant.
-/

namespace Zig.Full

open FAssn Zig.Region

/-- The address of byte `l.2` of block `l.1` in `m` (`0` for a block that does not exist). -/
def locAddr (m : Mem) (l : Loc) : Nat := ((m.blocks[l.1]?).map (·.addr)).getD 0 + l.2

/-- **Owned bytes have different addresses below `2 ^ 63`.** -/
theorem Holds.locAddr_lt {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq) {l : Loc}
    (hl : r.heap l ≠ none) : locAddr m l < 2 ^ 63 := by
  obtain ⟨b, x⟩ := l
  obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp hl
  obtain ⟨blk, hb, hlv, hx, -, -, -⟩ := hh.block hfc
  have := hs.2.2.2 b blk hb hlv
  simp only [locAddr, hb, Option.map_some, Option.getD_some]
  omega

theorem Holds.locAddr_inj {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq) {l l' : Loc}
    (hl : r.heap l ≠ none) (hl' : r.heap l' ≠ none) (he : locAddr m l = locAddr m l') : l = l' := by
  obtain ⟨b, x⟩ := l
  obtain ⟨b', x'⟩ := l'
  obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp hl
  obtain ⟨fc', hfc'⟩ := Option.ne_none_iff_exists'.mp hl'
  obtain ⟨blk, hb, hlv, hx, hlo, -, -⟩ := hh.block hfc
  obtain ⟨blk', hb', hlv', hx', hlo', -, -⟩ := hh.block hfc'
  simp only [locAddr, hb, hb', Option.map_some, Option.getD_some] at he
  by_cases hbb : b = b'
  · subst hbb
    rw [hb] at hb'; cases hb'
    have : x = x' := by omega
    rw [this]
  · exact absurd he (hs.2.2.1.addr_ne hbb hb hb' hlv hlv' hx hx' hlo hlo')

/-- **At most `2 ^ 63` bytes are owned**: a list of different locations that a resource owns is
no longer than `2 ^ 63`. -/
theorem Holds.owned_length_le {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq)
    {L : List Loc} (hnd : L.Nodup) (hown : ∀ l ∈ L, r.heap l ≠ none) : L.length ≤ 2 ^ 63 := by
  have hmap : (L.map (locAddr m)).Nodup := List.pairwise_map.mpr <| hnd.imp_of_mem
    fun hl hl' hne he => hne (hh.locAddr_inj hs (hown _ hl) (hown _ hl') he)
  have hsub : L.map (locAddr m) ⊆ List.range (2 ^ 63) := fun a ha => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    exact List.mem_range.mpr (hh.locAddr_lt hs (hown l hl))
  simpa using hmap.length_le_of_subset hsub

/-- The bytes `[lo, lo + n)` of block `b`. -/
def locRange (b lo n : Nat) : List Loc := (List.range n).map fun i => (b, lo + i)

theorem locRange_nodup (b lo n : Nat) : (locRange b lo n).Nodup :=
  List.pairwise_map.mpr <| List.nodup_range.imp fun hne he => hne (by simpa using he)

theorem mem_locRange {b lo n : Nat} {l : Loc} : l ∈ locRange b lo n ↔ l.1 = b ∧ lo ≤ l.2 ∧ l.2 < lo + n := by
  obtain ⟨b', x⟩ := l
  simp only [locRange, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩; exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨rfl, h1, h2⟩; exact ⟨x - lo, by omega, rfl, by omega⟩

/-! ## Lists of owned bytes

`OwnsList L P`: every resource of `P` owns each byte of `L`, which has no duplicates. Separated
parts own the concatenation (their heaps are disjoint), so an object made of several atoms owns
its whole range, and a list of objects their ranges one after the other. -/

/-- `P` owns every byte of the list `L` without duplicates. -/
def OwnsList (L : List Loc) (P : FAssn) : Prop := ∀ r, P r → L.Nodup ∧ ∀ l ∈ L, r.heap l ≠ none

theorem OwnsList.nil {P : FAssn} : OwnsList [] P := fun _ _ => ⟨List.nodup_nil, fun _ h => nomatch h⟩

/-- **Separated parts own the concatenation.** -/
theorem OwnsList.sep {L₁ L₂ : List Loc} {P Q : FAssn} (h₁ : OwnsList L₁ P) (h₂ : OwnsList L₂ Q) :
    OwnsList (L₁ ++ L₂) (P ⋆ Q) := by
  rintro r ⟨r₁, r₂, hd, rfl, hp, hq⟩
  obtain ⟨n₁, o₁⟩ := h₁ r₁ hp
  obtain ⟨n₂, o₂⟩ := h₂ r₂ hq
  refine ⟨List.nodup_append.mpr ⟨n₁, n₂, fun a ha b hb hab => ?_⟩, fun l hl => ?_⟩
  · subst hab
    rcases hd a with e | e
    · exact o₁ a ha e
    · exact o₂ a hb e
  · show (r₁.heap l).or (r₂.heap l) ≠ none
    rcases List.mem_append.mp hl with hl | hl
    · cases e : r₁.heap l with
      | none => exact absurd e (o₁ l hl)
      | some _ => simp
    · cases e : r₁.heap l with
      | none => simpa using o₂ l hl
      | some _ => simp

theorem OwnsList.of_imp {L : List Loc} {P Q : FAssn} (h : OwnsList L P) (hi : ∀ r, Q r → P r) :
    OwnsList L Q := fun r hq => h r (hi r hq)

theorem OwnsList.of_eq {L L' : List Loc} {P : FAssn} (h : OwnsList L P) (e : L = L') : OwnsList L' P :=
  e ▸ h

/-- Owned bytes (`bytesAt` of the erased heap) own their range. -/
theorem ownsList_bytes {p : Ptr} {b : BlockId} {A S : Nat} {K : BlockKind} {bs : Array Byte} {r : Res}
    (hb : p.block = some b) (h : bytesAt p A S K bs r.heap.erase) :
    (locRange b p.off.toNat bs.size).Nodup ∧ ∀ l ∈ locRange b p.off.toNat bs.size, r.heap l ≠ none := by
  refine ⟨locRange_nodup _ _ _, fun l hl => ?_⟩
  obtain ⟨b', hb', -, hl'⟩ := h
  rw [hb] at hb'; cases hb'
  obtain ⟨e1, a1, b1⟩ := mem_locRange.mp hl
  have := hl' l
  rw [if_pos ⟨e1, a1, b1⟩] at this
  intro e
  simp [FHeap.erase, e] at this

theorem OwnsList.region {p : Ptr} {b : BlockId} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    (hb : p.block = some b) : OwnsList (locRange b p.off.toNat bs.size) (up (regionIn p A S K a bs)) :=
  fun _ h => ownsList_bytes hb h.1.2.2

/-- **At most `2 ^ 63` bytes are owned** (`Holds.owned_length_le`), for a list of owned bytes. -/
theorem OwnsList.length_le {L : List Loc} {P : FAssn} (h : OwnsList L P) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : P r) (hs : m.FSeq) : L.length ≤ 2 ^ 63 :=
  hh.owned_length_le hs (h r hp).1 (h r hp).2

end Zig.Full
