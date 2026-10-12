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
  resource, as `AtomFacts`). `MemFacts.regions_apart`: two separately owned nonempty regions lie
  at disjoint address ranges: in one block by separation, in two blocks because live blocks lie
  apart (`Holds.apart`). This is the `@memcpy` aliasing check of the generated `dupe` and
  `realloc` wrappers (`ptrLe(src + n, dst) or ptrLe(dst + n, src)`); no premise about the
  placement is needed.
* **Pointer order** (`@[fsym]`): `ptrLe`/`ptrLt` of two pointers into blocks with known addresses
  (`AddrOf` providers): the addresses compared (`docs/architecture-audit/memory-model.md`, MM-4).
* **Byte operations on regions** (`@[fsym]`): `@memset(_, undefined)` of a whole region
  (`memsetUndef`), the store of an item (`regionStore`), the load of an item that a store wrote
  (`regionLoadWritten`), and `@memcpy` between two separate regions (`memcpyRegions`; the model's
  overlap check passes by separation). They lift the region library's total triples
  (`FTotalTriple.ofRegion`); the size label and the kind of a region's cells are labels
  (`EUpd.relabel`).
-/

namespace Zig
namespace Full

open FAssn

/-! ## Memory facts -/

/-- Every memory that holds `P` (sequentially) has the fact `φ`. -/
def MemFacts (P : FAssn) (φ : Prop) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FSeq → φ

theorem MemFacts.sepL {X R : FAssn} {φ : Prop} (h : MemFacts X φ) : MemFacts (X ⋆ R) φ :=
  fun m _ _ hh hp hs => by
    obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hp
    exact h m r₁ _ (Holds.split hd hh) h1 hs

/-- A memory fact of the precondition, in the context (any logic). -/
theorem MemFacts.pre (L : FLogic) {β : Type} {P : FAssn} {c : MemM β} {Q : β → FAssn} {φ : Prop}
    (hX : MemFacts P φ) (t : φ → L.T P c Q) : L.T P c Q := by
  have h0 : FTotalTriple P (pure () : MemM Unit) (fun _ => ⟪φ⟫ ⋆ P) :=
    FTotalTriple.of_run fun m r rF hh hp hs =>
      ⟨(), m, r, rfl, hh, sep_lift.mpr ⟨hX m r rF hh hp hs, hp⟩, hs⟩
  exact L.congr (fun _ _ => by simp) (L.bind (L.ofTotal h0) fun _ => L.lift t)

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
  · -- two blocks: the last byte of each lies before the other block
    obtain ⟨f1, e1, a1⟩ := region_cell hb (i := bs.size - 1) (by omega) h1
    obtain ⟨f2, e2, a2⟩ := region_cell hb' (i := cs.size - 1) (by omega) h2
    have := hh.apart hs hbb (inL _ _ e1) (inR _ _ e2)
    rw [a1, a2] at this
    omega

end Apart

/-! ## Pointer order -/

namespace FTotalTriple

variable {P : FAssn} {p q : Ptr} {b b' : BlockId} {A A' : Nat}

/-- **Pointer `<=`** of two pointers into blocks at known addresses: the addresses compared. -/
theorem ptrLe_of (hpb : p.block = some b) (hqb : q.block = some b') (h : AddrOf b A P)
    (h' : AddrOf b' A' P) :
    FTotalTriple P (Zig.ptrLe p q) (fun r => ⟪r = decide ((A : Int) + p.off ≤ (A' : Int) + q.off)⟫ ⋆ P) := by
  unfold Zig.ptrLe
  refine bind (ptrAddr_of hpb h) fun x => lift fun hx => ?_
  refine bind (ptrAddr_of hqb h') fun y => lift fun hy => ?_
  subst hx hy
  exact conseq (ret (Q := fun r => ⟪r = decide ((A : Int) + p.off ≤ (A' : Int) + q.off)⟫ ⋆ P) _)
    (fun _ hh => sep_lift.mpr ⟨rfl, hh⟩) (fun _ _ h => h)

/-- **Pointer `<`** of two pointers into blocks at known addresses: the addresses compared. -/
theorem ptrLt_of (hpb : p.block = some b) (hqb : q.block = some b') (h : AddrOf b A P)
    (h' : AddrOf b' A' P) :
    FTotalTriple P (Zig.ptrLt p q) (fun r => ⟪r = decide ((A : Int) + p.off < (A' : Int) + q.off)⟫ ⋆ P) := by
  unfold Zig.ptrLt
  refine bind (ptrAddr_of hpb h) fun x => lift fun hx => ?_
  refine bind (ptrAddr_of hqb h') fun y => lift fun hy => ?_
  subst hx hy
  exact conseq (ret (Q := fun r => ⟪r = decide ((A : Int) + p.off < (A' : Int) + q.off)⟫ ⋆ P) _)
    (fun _ hh => sep_lift.mpr ⟨rfl, hh⟩) (fun _ _ h => h)

end FTotalTriple

attribute [fsym] FTotalTriple.ptrLe_of FTotalTriple.ptrLt_of

/-! ## Lifting the region library -/

/-- A region whose cells carry some size label and some kind of `K`'s normal form: a size-free
form of `regionIn` (`SizeFree`), for lifting the region library's total triples. -/
def regionAny (p : Ptr) (A S : Nat) (K : BlockKind) (a : Nat) (bs : Array Byte) : Assn :=
  fun h => ∃ A' S' K', (A' = A ∧ K'.norm = K.norm ∧ (A' + p.off.toNat) % a = 0 ∧ K' ≠ .constGlobal) ∧
    bytesAt p A' S' K' bs h

theorem regionAny_sizeFree {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} :
    SizeFree (fun _ => none) (regionAny p A S K a bs) :=
  SizeFree.bytesAt_ex fun _ _ K₀ _ K' ⟨h1, h2, h3, h4⟩ hk =>
    ⟨h1, hk.trans h2, h3, fun e => h4 (by
      have hn : K₀.norm = .constGlobal := by rw [← hk, e]; rfl
      clear h1 h2 h3 h4 hk e; revert hn; cases K₀ <;> simp [BlockKind.norm])⟩

theorem regionAny_of {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} {h : Heap}
    (hr : regionIn p A S K a bs h) : regionAny p A S K a bs h :=
  ⟨A, S, K, ⟨rfl, rfl, hr.1, hr.2.1⟩, hr.2.2⟩

/-- A `regionAny` is the region with its own labels, relabeled (`EUpd.relabel`). -/
theorem EUpd.regionAny {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte} :
    EUpd (up (regionAny p A S K a bs)) (up (regionIn p A S K a bs)) := by
  intro m r rF hh hp hs
  obtain ⟨⟨A', S', K', ⟨rfl, hk, hal, hK⟩, hb⟩, hk2, hg⟩ := hp
  exact EUpd.relabel (S := S') (S' := S) hk.symm m r rF hh ⟨⟨hal, hK, hb⟩, hk2, hg⟩ hs

/-- **Lift a total triple of the region library** about one region, for every size label and
kind of the region's normal form, to the full-state logic. -/
theorem FTotalTriple.ofRegion {α : Type} {c : MemM α} {p : Ptr} {A S : Nat} {K : BlockKind}
    {a : Nat} {bs : Array Byte} {φ : α → Prop} {Q : α → Array Byte}
    (ht : ∀ S' K', K'.norm = K.norm → K' ≠ .constGlobal →
      TotalTriple (regionIn p A S' K' a bs) c (fun v => ⌜φ v⌝ ∗ regionIn p A S' K' a (Q v)))
    (hc : Tame c) (hk : Keeps (fun _ => False) c) :
    FTotalTriple (up (regionIn p A S K a bs)) c (fun v => ⟪φ v⟫ ⋆ up (regionIn p A S K a (Q v))) := by
  have ht' : TotalTriple (regionAny p A S K a bs) c
      (fun v => ⌜φ v⌝ ∗ regionAny p A S K a (Q v)) := by
    intro m hP hF hd hm hp hst
    obtain ⟨A', S', K', ⟨rfl, hk, hal, hK⟩, hb⟩ := hp
    obtain ⟨v, m', hQ, hr, hd', hm', hq, hs'⟩ := ht S' K' hk hK m hP hF hd hm ⟨hal, hK, hb⟩ hst
    obtain ⟨hφ, hq⟩ := Zig.sep_lift.mp hq
    exact ⟨v, m', hQ, hr, hd', hm', Zig.sep_lift.mpr ⟨hφ, ⟨A', S', K', ⟨rfl, hk, hq.1, hq.2.1⟩, hq.2.2⟩⟩, hs'⟩
  have hl := FTotalTriple.ofTotal_up ht' hc regionAny_sizeFree hk
  refine FTotalTriple.eupd_post (hl.pre fun r hr => up_imp (fun _ h => regionAny_of h) hr) fun _ => ?_
  intro m r rF hh hp hs
  obtain ⟨hφ, hp⟩ := up_lift.mp hp
  obtain ⟨r', hh', hq⟩ := EUpd.regionAny m r rF hh hp hs
  exact ⟨r', hh', sep_lift.mpr ⟨hφ, hq⟩⟩

/-! ## Byte operations on regions -/

/-- `@memset` keeps every block (it stores into one live block). -/
theorem Keeps.memset {D : BlockId → Prop} {β : Type} [Enc β] (a : Nat) (p : Ptr) (n : BitVec 64)
    (v : Option β) : Keeps D (Zig.memset a p n v) := by
  unfold Zig.memset
  split
  · exact Keeps.pure' _
  · refine Keeps.bind (Keeps.of_keepsExt fun _ _ _ h => ?_) fun _ =>
      Keeps.bind (Keeps.of_keepsExt fun _ _ _ h => ?_) fun _ => Keeps.storeBytes _ _ _ _
    · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.get_ok h; exact KeepsExt.refl _
    · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.lift_ok h; exact KeepsExt.refl _

/-- `@memcpy` keeps every block (it stores into one live block). -/
theorem Keeps.memcpy {D : BlockId → Prop} (size da sa : Nat) (d s : Ptr) (n m : BitVec 64) :
    Keeps D (Zig.memcpy size da sa d s n m) := by
  unfold Zig.memcpy Zig.memmove
  split
  · exact Keeps.of_keepsExt fun _ _ _ h => by cases h
  · split
    · exact Keeps.pure' _
    · refine Keeps.bind (Keeps.of_keepsExt fun _ _ _ h => ?_) fun _ =>
        Keeps.bind (Keeps.of_keepsExt fun _ _ _ h => ?_) fun _ =>
          Keeps.bind (Keeps.loadBytes _ _ _ _) fun _ => Keeps.storeBytes _ _ _ _
      · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.get_ok h; exact KeepsExt.refl _
      · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.lift_ok h; exact KeepsExt.refl _

namespace FTotalTriple

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}

/-- **`@memset(region, undefined)`** of all `n` bytes of a region: the region's bytes become
undefined (the `@memset` of `allocBytesWithAlignment` and of `free`). -/
@[fsym] theorem memsetUndef {n : BitVec 64} (hn : n.toNat = bs.size) :
    FTotalTriple (up (regionIn p A S K a bs)) (Zig.memset (α := BitVec 8) 1 p n none)
      (fun _ => up (regionIn p A S K a (Array.replicate n.toNat .undef))) :=
  (ofRegion (φ := fun _ => True) (fun _ _ _ _ => TotalTriple.conseq (Region.memsetUndefIn hn)
      (fun _ x => x) fun _ _ x => Zig.sep_lift.mpr ⟨trivial, x⟩)
    (Tame.memset 1 p n none) (Keeps.memset 1 p n none)).post fun _ _ h => (sep_lift.mp h).2

/-- **Store of an item** `v` at item `i` of a region (aligned to `al`): its bytes are `v`'s. -/
@[fsym] theorem regionStore {T : Type} [Enc T] [LawfulEnc T] {i : BitVec 64} {al : Nat} (v : T)
    (hpos : 0 < Enc.size T) (ho : Enc.size T * i.toNat + Enc.size T ≤ bs.size) (hal : al ∣ a)
    (halo : al ∣ Enc.size T * i.toNat) :
    FTotalTriple (up (regionIn p A S K a bs)) (Zig.store al (p.elem (Enc.size T) i) v)
      (fun _ => up (regionIn p A S K a (writeBytes bs (Enc.size T * i.toNat) (Enc.encode v)))) := by
  rw [Ptr.elem_eq]
  exact (ofRegion (φ := fun _ => True) (fun _ _ _ _ => TotalTriple.conseq
      (Region.storeItemIn v hpos ho hal halo) (fun _ x => x) fun _ _ x => Zig.sep_lift.mpr ⟨trivial, x⟩)
    (Tame.store _ _ _) (Keeps.store _ _ _)).post fun _ _ h => (sep_lift.mp h).2

/-- The load of an item at byte `o` of a region whose bytes there decode to `v`. -/
theorem _root_.Zig.Region.loadItemIn {T : Type} [Enc T] {o al : Nat} {v : T} (hpos : 0 < Enc.size T)
    (ho : o + Enc.size T ≤ bs.size) (hal : al ∣ a) (halo : al ∣ o)
    (hv : Enc.decode (bs.extract o (o + Enc.size T)) = (pure v : Result T)) :
    TotalTriple (regionIn p A S K a bs) (Zig.load T al (p.add o))
      (fun r => ⌜r = v⌝ ∗ regionIn p A S K a bs) := by
  intro m hP hF hd hm hp hst
  obtain ⟨hA, hK, hb⟩ := hp
  have ha : (A + p.off.toNat + o) % al = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans hal (Nat.dvd_of_mod_eq_zero hA)) halo)
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ := bytesAt_access (q := p.add o) (k := o) (n := Enc.size T)
    (a := al) hb hm rfl hpos ho ha
  have hv' : Enc.decode (blk.bytes.extract (p.off.toNat + o) (p.off.toNat + o + Enc.size T)) =
      (pure v : Result T) := by rw [hx]; exact hv
  refine ⟨v, _, hP, load_run hacc hv' (noRace_of_singleThread hst.single _ _ _ _), hd, ?_,
    Zig.sep_lift.mpr ⟨rfl, ⟨hA, hK, hb⟩⟩, hst.recordAt _ _ _ _⟩
  funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

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
  refine ofRegion (fun _ _ _ _ => Region.loadItemIn hpos (by omega) hal halo ?_)
    (Tame.load _ _ _) (Keeps.load _ _ _)
  have e := extract_writeBytes bs o (Enc.encode v) (by omega)
  rw [hw] at e
  rw [e]; exact LawfulEnc.decode_encode v

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
  -- the legacy triple, for every labels of the two regions
  have ht : TotalTriple (regionAny d A S K a bd ∗ regionAny s A' S' K' a' bsrc) (Zig.memcpy sz da sa d s n n)
      (fun _ => regionAny d A S K a (writeBytes bd 0 (bsrc.extract 0 (n.toNat * sz))) ∗
        regionAny s A' S' K' a' bsrc) := by
    intro mm hP hF hd hmm hp hst
    obtain ⟨h₁, h₂, hd₁₂, rfl, ⟨A₁, S₁, K₁, ⟨rfl, hk₁, hal₁, hK₁⟩, hb₁⟩,
      ⟨A₂, S₂, K₂, ⟨rfl, hk₂, hal₂, hK₂⟩, hb₂⟩⟩ := hp
    have hreg : (regionIn d A₁ S₁ K₁ a bd ∗ regionIn s A₂ S₂ K₂ a' bsrc) (h₁ ∪ h₂) :=
      ⟨h₁, h₂, hd₁₂, rfl, ⟨hal₁, hK₁, hb₁⟩, ⟨hal₂, hK₂, hb₂⟩⟩
    have ht0 := TotalTriple.memcpy_of (P := regionIn d A₁ S₁ K₁ a bd ∗ regionIn s A₂ S₂ K₂ a' bsrc)
      (fun _ _ _ _ hp => Region.not_overlaps hnd hns hp)
      (Region.memcpyIn (A := A₁) (S := S₁) (K := K₁) hnd hns hda hsa)
    obtain ⟨v, m', hQ, hr, hd', hm', hq, hs'⟩ := ht0 mm _ hF hd hmm hreg hst
    obtain ⟨q₁, q₂, hdq, rfl, hq₁, hq₂⟩ := hq
    exact ⟨v, m', q₁ ∪ q₂, hr, hd', hm', ⟨q₁, q₂, hdq, rfl,
      ⟨A₁, S₁, K₁, ⟨rfl, hk₁, hq₁.1, hq₁.2.1⟩, hq₁.2.2⟩, ⟨A₂, S₂, K₂, ⟨rfl, hk₂, hq₂.1, hq₂.2.1⟩, hq₂.2.2⟩⟩, hs'⟩
  have hl := FTotalTriple.ofTotal_up ht (Tame.memcpy _ _ _ _ _ _ _)
    (SizeFree.sep regionAny_sizeFree regionAny_sizeFree) (Keeps.memcpy _ _ _ _ _ _ _)
  refine FTotalTriple.eupd_post (hl.pre fun r hr => ?_) fun _ => ?_
  · exact up_imp (fun _ h => Zig.sep_mono (fun _ x => regionAny_of x) (fun _ x => regionAny_of x) h)
      (sep_up hr)
  · exact EUpd.trans (EUpd.of_imp fun _ h => up_sep h)
      (EUpd.trans (EUpd.frame EUpd.regionAny) (EUpd.frameL EUpd.regionAny))

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

end Full
end Zig
