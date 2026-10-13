import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AutoRules
import ZigLean.Sep.Full.Strength
import ZigLean.Sep.AllocSpec.Ops

/-!
# Regions in the full-state logic (library `Full/Region`)

A region `up (regionIn p A S K a bs)` owns the bytes `bs` at `p` (`ZigLean/Sep/AllocSpec/Region.lean`):
the memory an allocator grants (`FAllocInv.granted`), a stack local, a buffer. This module has
what generated code that works on regions needs beyond the step rules of `AutoRules`:

* **Memory facts** (`MemFacts P φ`): a fact of every memory that holds `P` (not only of the
  resource, as `AtomFacts`; `@[fsym_facts]`, `fsym` adds them for a pair of atoms when it needs
  more facts). `MemFacts.regions_apart`: two separately owned nonempty regions lie
  at disjoint address ranges: in one block by separation, in two blocks because live blocks lie
  apart (`Holds.apart`). This is the `@memcpy` aliasing check of the generated `dupe` and
  `realloc` wrappers (`ptrLe(src + n, dst) or ptrLe(dst + n, src)`); no premise about the
  placement is needed.
* **Pointer order** (`@[fsym]`): `ptrLe`/`ptrLt` of two pointers into blocks with known addresses
  (`AddrOf` providers): the addresses compared (`docs/architecture-audit/memory-model.md`, MM-4).
* **Bounds checks** (`@[fsym]`): the model's item checks `checkIndex`, `checkSentinelIndex` in
  bounds.
* **Byte operations on regions** (`@[fsym]`): `@memset(_, undefined)` of a whole region
  (`memsetUndef`), the store of an item (`regionStore`, and `regionStoreAdd` through a pointer
  that `ptrProject` formed with `Ptr.add`), the load of an item that a store wrote
  (`regionLoadWritten`, `regionLoadWrittenAdd`), and `@memcpy` between two separate regions (`memcpyRegions`; the model's
  overlap check passes by separation). They are the native rules of owned bytes (`Ops.lean`)
  with the region's alignment and kind (`FTotalTriple.region_of`).
-/

namespace Zig
namespace Full

open FAssn

/-! ## Memory facts (`MemFacts`, `MemFacts.pre`: `ZigLean/Sep/Full/AutoRules.lean`) -/

section Apart

variable {p q : Ptr} {A S A' S' a a' : Nat} {K K' : BlockKind} {bs cs : Array Byte}

/-- Byte `i` of a region is a cell of the resource, at the region's address label. -/
theorem region_cell {b : BlockId} {r : Res} (hb : p.block = some b) {i : Nat} (hi : i < bs.size)
    (hr : up (regionIn p A S K a bs) r) : ∃ fc, r.heap (b, p.off.toNat + i) = some fc ∧ fc.cell.addr = A := by
  obtain ⟨⟨-, -, b', hb', -, hl⟩, -⟩ := hr
  rw [hb] at hb'; cases hb'
  have := hl (b, p.off.toNat + i)
  simp only [FHeap.erase] at this
  rw [if_pos (by simp only [true_and]; omega)] at this
  cases e : r.heap (b, p.off.toNat + i) with
  | none => rw [e] at this; cases this
  | some fc =>
    rw [e] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨fc, rfl, by rw [this]⟩

/-- **Two separately owned regions lie at disjoint address ranges** (one of them may be empty).
In one block their bytes are disjoint cells; in two blocks the blocks lie apart (`Holds.apart`). -/
theorem MemFacts.regions_apart :
    MemFacts (up (regionIn p A S K a bs) ⋆ up (regionIn q A' S' K' a' cs))
      (bs.size = 0 ∨ cs.size = 0 ∨ (A : Int) + p.off + bs.size ≤ (A' : Int) + q.off ∨
        (A' : Int) + q.off + cs.size ≤ (A : Int) + p.off) := by
  intro m r rF hh hp hs
  rcases Nat.eq_zero_or_pos bs.size with h0 | hn
  · exact Or.inl h0
  rcases Nat.eq_zero_or_pos cs.size with h0 | hn'
  · exact Or.inr (Or.inl h0)
  right; right
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hp
  obtain ⟨b, hb, hp0, -⟩ := h1.1.2.2
  obtain ⟨b', hb', hq0, -⟩ := h2.1.2.2
  -- a cell of a part is a cell of the whole
  have inL : ∀ l fc, r₁.heap l = some fc → (r₁.heap ∪ r₂.heap) l = some fc := fun l fc e => by
    simp [e]
  have inR : ∀ l fc, r₂.heap l = some fc → (r₁.heap ∪ r₂.heap) l = some fc := fun l fc e => by
    rcases hd l with e' | e'
    · simp [e', e]
    · rw [e'] at e; cases e
  have ep : (p.off.toNat : Int) = p.off := Int.toNat_of_nonneg hp0
  have eq : (q.off.toNat : Int) = q.off := Int.toNat_of_nonneg hq0
  by_cases hbb : b = b'
  · subst hbb
    -- one block: the same address, and disjoint offsets
    obtain ⟨f1, e1, a1⟩ := region_cell hb (i := 0) hn h1
    obtain ⟨f2, e2, a2⟩ := region_cell hb' (i := 0) hn' h2
    obtain ⟨blk, hblk, -, -, -, ha1, -⟩ := hh.block (inL _ _ e1)
    obtain ⟨blk', hblk', -, -, -, ha2, -⟩ := hh.block (inR _ _ e2)
    rw [hblk] at hblk'; cases hblk'
    have hA : A = A' := by rw [← a1, ← a2, ha1, ha2]
    subst hA
    have hdis : p.off.toNat + bs.size ≤ q.off.toNat ∨ q.off.toNat + cs.size ≤ p.off.toNat := by
      refine Classical.byContradiction fun hc => ?_
      obtain ⟨x, hx1, hx2⟩ : ∃ x, (p.off.toNat ≤ x ∧ x < p.off.toNat + bs.size) ∧
          (q.off.toNat ≤ x ∧ x < q.off.toNat + cs.size) :=
        ⟨Nat.max p.off.toNat q.off.toNat, by simp only [Nat.max_def]; split <;> omega,
          by simp only [Nat.max_def]; split <;> omega⟩
      obtain ⟨g1, f1', -⟩ := region_cell hb (i := x - p.off.toNat) (by omega) h1
      obtain ⟨g2, f2', -⟩ := region_cell hb' (i := x - q.off.toNat) (by omega) h2
      rw [show p.off.toNat + (x - p.off.toNat) = x by omega] at f1'
      rw [show q.off.toNat + (x - q.off.toNat) = x by omega] at f2'
      rcases hd (b, x) with e | e
      · rw [e] at f1'; cases f1'
      · rw [e] at f2'; cases f2'
    omega
  · -- two blocks: the last byte of each lies before the first byte of the other
    obtain ⟨f1, e1, a1⟩ := region_cell hb (i := bs.size - 1) (by omega) h1
    obtain ⟨f2, e2, a2⟩ := region_cell hb' (i := cs.size - 1) (by omega) h2
    obtain ⟨g1, e1', -⟩ := region_cell hb (i := 0) hn h1
    obtain ⟨g2, e2', -⟩ := region_cell hb' (i := 0) hn' h2
    have := hh.apart hs hbb (inL _ _ e1) (inL _ _ e1') (inR _ _ e2) (inR _ _ e2')
    rw [a1, a2] at this
    omega

attribute [fsym_facts] MemFacts.regions_apart

end Apart

/-! ## Pointer order -/

/- The thread rules are the proofs (they read no byte); the sequential rules are read from them
(`FTTotalTriple.toFTotalTriple`). -/

namespace FTTotalTriple

variable {P : FAssn} {p q : Ptr} {b b' : BlockId} {A A' : Nat}

/-- **Pointer `<=`** of two pointers into blocks at known addresses: the addresses compared. -/
theorem ptrLe_of (hpb : p.block = some b) (hqb : q.block = some b') (h : AddrOf b A P)
    (h' : AddrOf b' A' P) :
    FTTotalTriple P (Zig.ptrLe p q) (fun r => ⟪r = decide ((A : Int) + p.off ≤ (A' : Int) + q.off)⟫ ⋆ P) := by
  unfold Zig.ptrLe
  refine bind (ptrAddr_of hpb h) fun x => lift fun hx => ?_
  refine bind (ptrAddr_of hqb h') fun y => lift fun hy => ?_
  subst hx hy
  exact conseq (ret (Q := fun r => ⟪r = decide ((A : Int) + p.off ≤ (A' : Int) + q.off)⟫ ⋆ P) _)
    (fun _ hh => sep_lift.mpr ⟨rfl, hh⟩) (fun _ _ h => h)

/-- **Pointer `<`** of two pointers into blocks at known addresses: the addresses compared. -/
theorem ptrLt_of (hpb : p.block = some b) (hqb : q.block = some b') (h : AddrOf b A P)
    (h' : AddrOf b' A' P) :
    FTTotalTriple P (Zig.ptrLt p q) (fun r => ⟪r = decide ((A : Int) + p.off < (A' : Int) + q.off)⟫ ⋆ P) := by
  unfold Zig.ptrLt
  refine bind (ptrAddr_of hpb h) fun x => lift fun hx => ?_
  refine bind (ptrAddr_of hqb h') fun y => lift fun hy => ?_
  subst hx hy
  exact conseq (ret (Q := fun r => ⟪r = decide ((A : Int) + p.off < (A' : Int) + q.off)⟫ ⋆ P) _)
    (fun _ hh => sep_lift.mpr ⟨rfl, hh⟩) (fun _ _ h => h)

/-- The model's bounds check of an item `s[i]` in bounds: no effect. -/
theorem checkIndex_of {w : Nat} {len i : BitVec w} (h : i.toNat < len.toNat) :
    FTTotalTriple P (checkIndex len i) (fun _ => P) := by
  unfold checkIndex; rw [if_pos h]; exact ret (Q := fun _ => P) ()

/-- The bounds check of an item of an operand with a sentinel (`i ≤ len`): no effect. -/
theorem checkSentinelIndex_of {w : Nat} {len i : BitVec w} (h : i.toNat ≤ len.toNat) :
    FTTotalTriple P (checkSentinelIndex len i) (fun _ => P) := by
  unfold checkSentinelIndex; rw [if_pos h]; exact ret (Q := fun _ => P) ()

end FTTotalTriple

namespace FTotalTriple

variable {P : FAssn} {p q : Ptr} {b b' : BlockId} {A A' : Nat}

/-- **Pointer `<=`** of two pointers into blocks at known addresses: the addresses compared. -/
theorem ptrLe_of (hpb : p.block = some b) (hqb : q.block = some b') (h : AddrOf b A P)
    (h' : AddrOf b' A' P) :
    FTotalTriple P (Zig.ptrLe p q) (fun r => ⟪r = decide ((A : Int) + p.off ≤ (A' : Int) + q.off)⟫ ⋆ P) :=
  (FTTotalTriple.ptrLe_of hpb hqb h h').toFTotalTriple

/-- **Pointer `<`** of two pointers into blocks at known addresses: the addresses compared. -/
theorem ptrLt_of (hpb : p.block = some b) (hqb : q.block = some b') (h : AddrOf b A P)
    (h' : AddrOf b' A' P) :
    FTotalTriple P (Zig.ptrLt p q) (fun r => ⟪r = decide ((A : Int) + p.off < (A' : Int) + q.off)⟫ ⋆ P) :=
  (FTTotalTriple.ptrLt_of hpb hqb h h').toFTotalTriple

end FTotalTriple

attribute [fsym] FTotalTriple.ptrLe_of FTotalTriple.ptrLt_of

/-! ## Bounds checks of item accesses -/

namespace FTotalTriple

variable {P : FAssn} {w : Nat} {len i : BitVec w}

/-- The model's bounds check of an item `s[i]` in bounds: no effect. -/
@[fsym] theorem checkIndex_of (h : i.toNat < len.toNat) : FTotalTriple P (checkIndex len i) (fun _ => P) :=
  (FTTotalTriple.checkIndex_of h).toFTotalTriple

/-- The bounds check of an item of an operand with a sentinel (`i ≤ len`): no effect. -/
@[fsym] theorem checkSentinelIndex_of (h : i.toNat ≤ len.toNat) :
    FTotalTriple P (checkSentinelIndex len i) (fun _ => P) :=
  (FTTotalTriple.checkSentinelIndex_of h).toFTotalTriple

end FTotalTriple

/-! ## Byte operations on regions

The native rules of owned bytes (`Ops.lean`: `load_bytesAt`, `store_bytesAt`, `memset_bytesAt`,
`memmove_bytesAt`) with the region's alignment and kind. -/

namespace FTotalTriple

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}

/-- **A rule on a region from the rule on its owned bytes** (`up_view`): the region's alignment
and kind are facts of its labels, which the bytes keep. -/
theorem region_of {α : Type} {c : MemM α} {φ : α → Prop} {Q : α → Array Byte}
    (ht : (A + p.off.toNat) % a = 0 → K ≠ .constGlobal →
      FTotalTriple (up (bytesAt p A S K bs)) c (fun v => ⟪φ v⟫ ⋆ up (bytesAt p A S K (Q v)))) :
    FTotalTriple (up (regionIn p A S K a bs)) c (fun v => ⟪φ v⟫ ⋆ up (regionIn p A S K a (Q v))) :=
  up_view fun _ ⟨hA, hK, hb⟩ => ⟨_, _, ht hA hK, hb, fun _ _ hb' => ⟨hA, hK, hb'⟩⟩

/-- `region_of` for a step without a returned fact. -/
theorem region_of' {α : Type} {c : MemM α} {Q : α → Array Byte}
    (ht : (A + p.off.toNat) % a = 0 → K ≠ .constGlobal →
      FTotalTriple (up (bytesAt p A S K bs)) c (fun v => up (bytesAt p A S K (Q v)))) :
    FTotalTriple (up (regionIn p A S K a bs)) c (fun v => up (regionIn p A S K a (Q v))) :=
  up_view' fun _ ⟨hA, hK, hb⟩ => ⟨_, _, ht hA hK, hb, fun _ _ hb' => ⟨hA, hK, hb'⟩⟩

/-- **`@memset(region, undefined)`** of all `n` bytes of a region: the region's bytes become
undefined (the `@memset` of `allocBytesWithAlignment` and of `free`). -/
@[fsym] theorem memsetUndef {n : BitVec 64} (hn : n.toNat = bs.size) :
    FTotalTriple (up (regionIn p A S K a bs)) (Zig.memset (α := BitVec 8) 1 p n none)
      (fun _ => up (regionIn p A S K a (Array.replicate n.toNat .undef))) := by
  have e : memsetBytes n.toNat (none : Option (BitVec 8)) = Array.replicate n.toNat .undef :=
    Region.flatten_replicate_single _ _
  have hs : (Array.replicate n.toNat Byte.undef).size = bs.size := by simp [hn]
  refine region_of' fun _ hK => ?_
  have t := memset_bytesAt (q := p) (k := 0) (al := 1) (A := A) (S := S) (bs := bs)
    (n := n) (v := (none : Option (BitVec 8))) (by rw [e]; simp [Region.enc_size_byte])
    (by rw [Region.enc_size_byte]; omega) (Nat.mod_one _) hK
  simpa only [Int.natCast_zero, Ptr.add_zero, e, writeBytes_all hs] using t

/-- **Store of an item** `v` at item `i` of a region (aligned to `al`): its bytes are `v`'s. -/
@[fsym] theorem regionStore {T : Type} [Enc T] [LawfulEnc T] {i : BitVec 64} {al : Nat} (v : T)
    (hpos : 0 < Enc.size T) (ho : Enc.size T * i.toNat + Enc.size T ≤ bs.size) (hal : al ∣ a)
    (halo : al ∣ Enc.size T * i.toNat) :
    FTotalTriple (up (regionIn p A S K a bs)) (Zig.store al (p.elem (Enc.size T) i) v)
      (fun _ => up (regionIn p A S K a (writeBytes bs (Enc.size T * i.toNat) (Enc.encode v)))) := by
  rw [Ptr.elem_eq]
  exact region_of' fun hA hK => store_bytesAt v (by rw [LawfulEnc.size_encode]; exact hpos)
    (by rw [LawfulEnc.size_encode]; exact ho) (mod_add_dvd hA hal halo) hK

/-- **Load of an item that a store wrote** (at item `i`, byte `o`): its value. -/
@[fsym] theorem regionLoadWritten {T : Type} [Enc T] [LawfulEnc T] {i : BitVec 64} {al o : Nat} {v : T}
    (hpos : 0 < Enc.size T) (ho : o + Enc.size T ≤ bs.size) (hoi : Enc.size T * i.toNat = o)
    (hal : al ∣ a) (halo : al ∣ o) :
    FTotalTriple (up (regionIn p A S K a (writeBytes bs o (Enc.encode v))))
      (Zig.load T al (p.elem (Enc.size T) i))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K a (writeBytes bs o (Enc.encode v)))) := by
  have hw := LawfulEnc.size_encode v
  have hs : (writeBytes bs o (Enc.encode v)).size = bs.size := writeBytes_size _ _ _ (by omega)
  rw [Ptr.elem_eq, hoi]
  refine region_of fun hA _ => load_bytesAt hpos (by omega) (mod_add_dvd hA hal halo) ?_
  have e := extract_writeBytes bs o (Enc.encode v) (by omega)
  rw [hw] at e
  rw [e]; exact LawfulEnc.decode_encode v

/-- **Store of an item** `v` at byte offset `k` of a region (a pointer formed by `ptrProject`
with `Ptr.add`). -/
@[fsym] theorem regionStoreAdd {T : Type} [Enc T] [LawfulEnc T] {k : Int} {al : Nat} (v : T)
    (hpos : 0 < Enc.size T) (h0 : 0 ≤ k) (ho : k.toNat + Enc.size T ≤ bs.size) (hal : al ∣ a)
    (halo : al ∣ k.toNat) :
    FTotalTriple (up (regionIn p A S K a bs)) (Zig.store al (p.add k) v)
      (fun _ => up (regionIn p A S K a (writeBytes bs k.toNat (Enc.encode v)))) := by
  have e : p.add k = p.add ((k.toNat : Nat) : Int) := by rw [Int.toNat_of_nonneg h0]
  rw [e]
  exact region_of' fun hA hK => store_bytesAt v (by rw [LawfulEnc.size_encode]; exact hpos)
    (by rw [LawfulEnc.size_encode]; exact ho) (mod_add_dvd hA hal halo) hK

/-- **Load of an item that a store wrote**, through a pointer formed with `Ptr.add`. -/
@[fsym] theorem regionLoadWrittenAdd {T : Type} [Enc T] [LawfulEnc T] {k : Int} {al o : Nat} {v : T}
    (hpos : 0 < Enc.size T) (ho : o + Enc.size T ≤ bs.size) (hko : k = (o : Int))
    (hal : al ∣ a) (halo : al ∣ o) :
    FTotalTriple (up (regionIn p A S K a (writeBytes bs o (Enc.encode v))))
      (Zig.load T al (p.add k))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K a (writeBytes bs o (Enc.encode v)))) := by
  have hw := LawfulEnc.size_encode v
  have hs : (writeBytes bs o (Enc.encode v)).size = bs.size := writeBytes_size _ _ _ (by omega)
  subst hko
  refine region_of fun hA _ => load_bytesAt hpos (by omega) (mod_add_dvd hA hal halo) ?_
  have e := extract_writeBytes bs o (Enc.encode v) (by omega)
  rw [hw] at e
  rw [e]; exact LawfulEnc.decode_encode v

/-- **Store of an item** `v` at the start of a region (the pointer itself: the first field).
Not `@[fsym]`: as a default rule it carves a region at a store through a formed pointer instead
of `regionStoreAdd`'s in-place update (`tests/roadmap/sep-auto/Region.lean`). -/
theorem regionStore0 {T : Type} [Enc T] [LawfulEnc T] {al : Nat} (v : T)
    (hpos : 0 < Enc.size T) (ho : Enc.size T ≤ bs.size) (hal : al ∣ a) :
    FTotalTriple (up (regionIn p A S K a bs)) (Zig.store al p v)
      (fun _ => up (regionIn p A S K a (writeBytes bs 0 (Enc.encode v)))) := by
  have t := regionStoreAdd (p := p) (A := A) (S := S) (K := K) (a := a) (bs := bs) (k := 0)
    (al := al) v hpos (Int.le_refl 0) (by simpa using ho) hal (Nat.dvd_zero al)
  simpa only [Ptr.add_zero, Int.toNat_zero] using t

/-- **Load of an item that a store wrote** at the start of a region (with `regionStore0`). -/
theorem regionLoadWritten0 {T : Type} [Enc T] [LawfulEnc T] {al : Nat} {v : T}
    (hpos : 0 < Enc.size T) (ho : Enc.size T ≤ bs.size) (hal : al ∣ a) :
    FTotalTriple (up (regionIn p A S K a (writeBytes bs 0 (Enc.encode v)))) (Zig.load T al p)
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K a (writeBytes bs 0 (Enc.encode v)))) := by
  have t := regionLoadWrittenAdd (p := p) (A := A) (S := S) (K := K) (a := a) (bs := bs) (k := 0)
    (o := 0) (al := al) (v := v) hpos (by simpa using ho) (by simp) hal (Nat.dvd_zero al)
  simpa only [Ptr.add_zero] using t

/-- Two separate nonempty regions do not overlap as the model's `@memcpy` check sees them. -/
theorem _root_.Zig.Region.not_overlaps {d s : Ptr} {A' S' : Nat} {K' : BlockKind} {a' : Nat}
    {bd bsrc : Array Byte} {n : Nat} {h : Heap} (hnd : n ≤ bd.size) (hns : n ≤ bsrc.size)
    (hp : (regionIn d A S K a bd ∗ regionIn s A' S' K' a' bsrc) h) : d.overlaps s n = false := by
  obtain ⟨h₁, h₂, hd, rfl, ⟨-, -, b, hb, h0, hl⟩, ⟨-, -, b', hb', h0', hl'⟩⟩ := hp
  unfold Ptr.overlaps
  rw [Bool.eq_false_iff]
  simp only [ne_eq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hb, hb', Option.some.injEq]
  rintro ⟨⟨⟨hn, rfl⟩, h1⟩, h2⟩
  obtain ⟨x, hx1, hx2⟩ : ∃ x, (d.off.toNat ≤ x ∧ x < d.off.toNat + n) ∧
      (s.off.toNat ≤ x ∧ x < s.off.toNat + n) :=
    ⟨Nat.max d.off.toNat s.off.toNat, by simp only [Nat.max_def]; split <;> omega,
      by simp only [Nat.max_def]; split <;> omega⟩
  have e1 := hl (b, x)
  have e2 := hl' (b, x)
  rw [if_pos ⟨rfl, hx1.1, by omega⟩] at e1
  rw [if_pos ⟨rfl, hx2.1, by omega⟩] at e2
  rcases hd (b, x) with e | e
  · rw [e] at e1; cases e1
  · rw [e] at e2; cases e2

/-- **`@memcpy`** of `n` items of `sz` bytes from the region `s` to the start of the separate
region `d`: the model's checks pass (equal counts; no overlap, by separation). -/
@[fsym] theorem memcpyRegions {d s : Ptr} {A' S' : Nat} {K' : BlockKind} {a' sz da sa : Nat}
    {bd bsrc : Array Byte} {n m : BitVec 64} (hm : n.toNat = m.toNat) (hnd : n.toNat * sz ≤ bd.size)
    (hns : n.toNat * sz ≤ bsrc.size) (hda : da ∣ a) (hsa : sa ∣ a') :
    FTotalTriple (up (regionIn d A S K a bd) ⋆ up (regionIn s A' S' K' a' bsrc))
      (Zig.memcpy sz da sa d s n m)
      (fun _ => up (regionIn d A S K a (writeBytes bd 0 (bsrc.extract 0 (n.toNat * sz)))) ⋆
        up (regionIn s A' S' K' a' bsrc)) := by
  have e : n = m := BitVec.eq_of_toNat_eq hm
  subst e
  refine of_cases fun r hp => ?_
  have hov := Region.not_overlaps hnd hns (sep_up hp).1
  have ec : Zig.memcpy sz da sa d s n n = Zig.memmove sz da sa d s n := by
    unfold Zig.memcpy; simp [hov]
  obtain ⟨r₁, r₂, hd, rfl, ⟨⟨hA, hK, hb₁⟩, hk₁, hg₁⟩, ⟨⟨hA', hK', hb₂⟩, hk₂, hg₂⟩⟩ := hp
  have t := memmove_bytesAt (d := d) (s := s) (k := 0) (j := 0) (A := A) (S := S) (K := K)
    (A' := A') (S' := S') (K' := K') (bd := bd) (bsrc := bsrc) (sz := sz) (da := da) (sa := sa)
    (n := n) (by omega) (by omega) (mod_add_dvd hA hda (Nat.dvd_zero _))
    (mod_add_dvd hA' hsa (Nat.dvd_zero _)) hK
  simp only [Int.natCast_zero, Ptr.add_zero, Nat.zero_add] at t
  refine ⟨_, _, ec ▸ t, ⟨r₁, r₂, hd, rfl, ⟨hb₁, hk₁, hg₁⟩, ⟨hb₂, hk₂, hg₂⟩⟩, fun _ _ h => ?_⟩
  obtain ⟨q₁, q₂, hdq, rfl, ⟨hq₁, hk₁', hg₁'⟩, ⟨hq₂, hk₂', hg₂'⟩⟩ := h
  exact ⟨q₁, q₂, hdq, rfl, ⟨⟨hA, hK, hq₁⟩, hk₁', hg₁'⟩, ⟨⟨hA', hK', hq₂⟩, hk₂', hg₂'⟩⟩

/-- `@memcpy` of a whole region onto a separate one of the same size: a copy of its bytes. -/
@[fsym] theorem memcpyRegionsAll {d s : Ptr} {A' S' : Nat} {K' : BlockKind} {a' sz da sa : Nat}
    {bd bsrc : Array Byte} {n m : BitVec 64} (hm : n.toNat = m.toNat) (hnd : n.toNat * sz = bd.size)
    (hns : n.toNat * sz = bsrc.size) (hda : da ∣ a) (hsa : sa ∣ a') :
    FTotalTriple (up (regionIn d A S K a bd) ⋆ up (regionIn s A' S' K' a' bsrc))
      (Zig.memcpy sz da sa d s n m)
      (fun _ => up (regionIn d A S K a bsrc) ⋆ up (regionIn s A' S' K' a' bsrc)) := by
  have e : writeBytes bd 0 (bsrc.extract 0 (n.toNat * sz)) = bsrc := by
    rw [Array.extract_eq_self_of_le (by omega), writeBytes_all (by omega)]
  have t := memcpyRegions (d := d) (s := s) (A := A) (S := S) (K := K) (a := a) (A' := A')
    (S' := S') (K' := K') (a' := a') (sz := sz) (da := da) (sa := sa) (bd := bd) (bsrc := bsrc)
    (n := n) (m := m) hm (by omega) (by omega) hda hsa
  rw [e] at t; exact t

end FTotalTriple

/-! ## Thread rules

The byte operations above in a thread (`docs/sep-threads.md` S2; the pointer order and bounds
checks are thread rules already): each is its sequential rule with the locality of its
access (`FTTotalTriple.ofSeq`, the region's owned bytes `OwnsPtr.regionIn_add`). -/

namespace OwnsPtr

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}

/-- The bytes `[k, k + n)` of a region. -/
theorem regionIn_add {k n : Nat} (hk : k + n ≤ bs.size) :
    OwnsPtr (up (regionIn p A S K a bs)) (p.add k) n := by
  rintro b hb r ⟨⟨-, -, hbt⟩, hk', hg⟩
  exact bytesAt_add hk b hb r ⟨hbt, hk', hg⟩

/-- The first `n` bytes of a region. -/
theorem regionIn_start {n : Nat} (hn : n ≤ bs.size) : OwnsPtr (up (regionIn p A S K a bs)) p n := by
  have t := regionIn_add (p := p) (A := A) (S := S) (K := K) (a := a) (bs := bs) (k := 0) (n := n)
    (by omega)
  simpa only [Int.natCast_zero, Ptr.add_zero] using t

end OwnsPtr

namespace FTTotalTriple

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}

theorem memsetUndef {n : BitVec 64} (hn : n.toNat = bs.size) :
    FTTotalTriple (up (regionIn p A S K a bs)) (Zig.memset (α := BitVec 8) 1 p n none)
      (fun _ => up (regionIn p A S K a (Array.replicate n.toNat .undef))) :=
  ofSeq (FTotalTriple.memsetUndef hn) (ThreadLocal.memset (fun _ h => by cases h)
    (OwnsPtr.regionIn_start (by rw [Region.enc_size_byte]; omega)))

theorem regionStore {T : Type} [Enc T] [LawfulEnc T] {i : BitVec 64} {al : Nat} (v : T)
    (hpos : 0 < Enc.size T) (ho : Enc.size T * i.toNat + Enc.size T ≤ bs.size) (hal : al ∣ a)
    (halo : al ∣ Enc.size T * i.toNat) :
    FTTotalTriple (up (regionIn p A S K a bs)) (Zig.store al (p.elem (Enc.size T) i) v)
      (fun _ => up (regionIn p A S K a (writeBytes bs (Enc.size T * i.toNat) (Enc.encode v)))) :=
  ofSeq (FTotalTriple.regionStore v hpos ho hal halo)
    (ThreadLocal.store (by rw [LawfulEnc.size_encode]; exact hpos)
      (by rw [LawfulEnc.size_encode, Ptr.elem_eq]; exact OwnsPtr.regionIn_add ho))

theorem regionLoadWritten {T : Type} [Enc T] [LawfulEnc T] {i : BitVec 64} {al o : Nat} {v : T}
    (hpos : 0 < Enc.size T) (ho : o + Enc.size T ≤ bs.size) (hoi : Enc.size T * i.toNat = o)
    (hal : al ∣ a) (halo : al ∣ o) :
    FTTotalTriple (up (regionIn p A S K a (writeBytes bs o (Enc.encode v))))
      (Zig.load T al (p.elem (Enc.size T) i))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K a (writeBytes bs o (Enc.encode v)))) := by
  have hs : (writeBytes bs o (Enc.encode v)).size = bs.size :=
    writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode]; omega)
  refine ofSeq (FTotalTriple.regionLoadWritten hpos ho hoi hal halo) (ThreadLocal.load hpos ?_)
  rw [Ptr.elem_eq, hoi]; exact OwnsPtr.regionIn_add (by omega)

theorem regionStoreAdd {T : Type} [Enc T] [LawfulEnc T] {k : Int} {al : Nat} (v : T)
    (hpos : 0 < Enc.size T) (h0 : 0 ≤ k) (ho : k.toNat + Enc.size T ≤ bs.size) (hal : al ∣ a)
    (halo : al ∣ k.toNat) :
    FTTotalTriple (up (regionIn p A S K a bs)) (Zig.store al (p.add k) v)
      (fun _ => up (regionIn p A S K a (writeBytes bs k.toNat (Enc.encode v)))) := by
  have e : p.add k = p.add ((k.toNat : Nat) : Int) := by rw [Int.toNat_of_nonneg h0]
  refine ofSeq (FTotalTriple.regionStoreAdd v hpos h0 ho hal halo)
    (ThreadLocal.store (by rw [LawfulEnc.size_encode]; exact hpos) ?_)
  rw [LawfulEnc.size_encode, e]; exact OwnsPtr.regionIn_add ho

theorem regionLoadWrittenAdd {T : Type} [Enc T] [LawfulEnc T] {k : Int} {al o : Nat} {v : T}
    (hpos : 0 < Enc.size T) (ho : o + Enc.size T ≤ bs.size) (hko : k = (o : Int))
    (hal : al ∣ a) (halo : al ∣ o) :
    FTTotalTriple (up (regionIn p A S K a (writeBytes bs o (Enc.encode v))))
      (Zig.load T al (p.add k))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K a (writeBytes bs o (Enc.encode v)))) := by
  have hs : (writeBytes bs o (Enc.encode v)).size = bs.size :=
    writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode]; omega)
  refine ofSeq (FTotalTriple.regionLoadWrittenAdd hpos ho hko hal halo) (ThreadLocal.load hpos ?_)
  subst hko; exact OwnsPtr.regionIn_add (by omega)

theorem memcpyRegions {d s : Ptr} {A' S' : Nat} {K' : BlockKind} {a' sz da sa : Nat}
    {bd bsrc : Array Byte} {n m : BitVec 64} (hm : n.toNat = m.toNat) (hnd : n.toNat * sz ≤ bd.size)
    (hns : n.toNat * sz ≤ bsrc.size) (hda : da ∣ a) (hsa : sa ∣ a') :
    FTTotalTriple (up (regionIn d A S K a bd) ⋆ up (regionIn s A' S' K' a' bsrc))
      (Zig.memcpy sz da sa d s n m)
      (fun _ => up (regionIn d A S K a (writeBytes bd 0 (bsrc.extract 0 (n.toNat * sz)))) ⋆
        up (regionIn s A' S' K' a' bsrc)) :=
  ofSeq (FTotalTriple.memcpyRegions hm hnd hns hda hsa)
    (ThreadLocal.memcpy (OwnsPtr.regionIn_start hnd).sepL (OwnsPtr.regionIn_start hns).sepR)

theorem memcpyRegionsAll {d s : Ptr} {A' S' : Nat} {K' : BlockKind} {a' sz da sa : Nat}
    {bd bsrc : Array Byte} {n m : BitVec 64} (hm : n.toNat = m.toNat) (hnd : n.toNat * sz = bd.size)
    (hns : n.toNat * sz = bsrc.size) (hda : da ∣ a) (hsa : sa ∣ a') :
    FTTotalTriple (up (regionIn d A S K a bd) ⋆ up (regionIn s A' S' K' a' bsrc))
      (Zig.memcpy sz da sa d s n m)
      (fun _ => up (regionIn d A S K a bsrc) ⋆ up (regionIn s A' S' K' a' bsrc)) :=
  ofSeq (FTotalTriple.memcpyRegionsAll hm hnd hns hda hsa)
    (ThreadLocal.memcpy (OwnsPtr.regionIn_start (by omega)).sepL
      (OwnsPtr.regionIn_start (by omega)).sepR)

end FTTotalTriple

end Full
end Zig
