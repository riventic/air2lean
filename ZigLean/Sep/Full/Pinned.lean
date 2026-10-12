import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Extent
import ZigLean.Sep.Full.AutoAttr

/-!
# Pinned blocks: legacy steps on blocks whose full extent is held

(`docs/sep-full-state.md` §Block extents.) A legacy assertion whose bytes all lie in one block
`b` whose full extent `bext b S K` is held next to it is *pinned*: its cells' sizes are the
block's. Such an assertion lifts to the full-state logic with the pinned bridge
(`FTotalTriple.ofTotal`, `E = {b ↦ (S, K)}`), and the program may change the block's extent
(`munmap`, `mremap`): the post gets the block's new full extent back from the cells it owns
(`upPost_bext`).

* `CTriple.step_bext`: one legacy step on a pinned assertion, with the extent read back from the
  post's cells. `FTotalTriple.pinned` is the same for a step that keeps the extent.
* **A block's bytes with its extent** (`@[fsym]`): `FTotalTriple.storeBlock` and
  `FTotalTriple.loadBlock`, a store or a load at the start of `bytesAt p A S K bs` held with
  `bext b S K`. These are the steps on an escaping local (`allocStack`: its bytes and its full
  extent), until `FTotalTriple.free` gives the block back.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Updates that forget -/

/-- Extent claims (anything that owns no bytes and no knowledge) can be dropped. -/
theorem EUpd.drop {P K : FAssn} (hK : ∀ r, K r → r.heap = FHeap.empty ∧ r.know = Know.none) :
    EUpd (P ⋆ K) P := by
  rintro m _ rF hh ⟨r₁, r₂, -, rfl, hp, hk⟩ -
  obtain ⟨e1, e2⟩ := hK _ hk
  obtain ⟨hd, hm, hkn, hkF, hg⟩ := hh
  simp only [e1, e2, FHeap.union_empty, Know.union_none] at hd hm hkn
  exact ⟨r₁, ⟨hd, hm, hkn, hkF, GOk.mono hg⟩, hp⟩

/-- A lifted post with its extents forgotten. -/
theorem EUpd.upPost_up {Q : Assn} {B : BlockId → Prop} {E : BlockId → Option (Nat × BlockKind)} :
    EUpd (upPost Q B E) (up Q) := fun m r rF hh h hs => by
  obtain ⟨E', ⟨hq, hk, hg⟩, -⟩ := h
  have := EUpd.drop (P := up Q) (K := fun r => r.heap = FHeap.empty ∧ r.know = Know.none)
    (fun _ h => h) m r rF hh ⟨⟨r.heap, Know.none, Ghost.unit⟩, ⟨FHeap.empty, Know.none, Ghost.exts E'⟩,
      FHeap.disjoint_empty _, by rw [res_eta r, hk, hg]; simp [Know.union_none], ⟨hq, rfl, rfl⟩, rfl, rfl⟩ hs
  exact this

theorem upPost.mono {Q Q' : Assn} {B : BlockId → Prop} {E : BlockId → Option (Nat × BlockKind)}
    {r : Res} (h : upPost Q B E r) (hq : Q' r.heap.erase) : upPost Q' B E r := by
  obtain ⟨E', ⟨-, hk, hg⟩, hc⟩ := h
  exact ⟨E', ⟨hq, hk, hg⟩, hc⟩

/-- The full extent of `b` only. -/
def ext1 (b : BlockId) (S : Nat) (K : BlockKind) : BlockId → Option (Nat × BlockKind) :=
  fun x => if x = b then some (S, K) else none

/-! ## Cells of legacy byte assertions -/

theorem bytesAt_of_cell {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {h : Heap}
    (hb : bytesAt p A S K bs h) {l : Loc} {c : Cell} (hl : h l = some c) :
    p.block = some l.1 ∧ c.size = S ∧ c.kind = K := by
  obtain ⟨b, hpb, -, hh⟩ := hb
  rw [hh l] at hl
  split at hl
  · rename_i hc; cases hl; exact ⟨by rw [hc.1]; exact hpb, rfl, rfl⟩
  · cases hl

/-- The first cell of a nonempty region, as a cell of the resource. -/
theorem regionIn_first {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte} {X : Assn} {r : Res}
    (hpos : 0 < bs.size) (h : (regionIn p A S K a bs ∗ X) r.heap.erase) :
    ∃ b, p.block = some b ∧ ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.size = S ∧ fc.cell.kind = K := by
  obtain ⟨h₁, h₂, -, he, ⟨-, -, b, hpb, -, hl⟩, -⟩ := h
  refine ⟨b, hpb, p.off.toNat, ?_⟩
  have e : r.heap.erase (b, p.off.toNat) = some ⟨bs[0]!, A, S, K⟩ := by
    rw [he, Heap.union_apply, hl]; simp [hpos]
  simp only [FHeap.erase, Option.map_eq_some_iff] at e
  obtain ⟨fc, hfc, hc⟩ := e
  exact ⟨fc, hfc, by rw [hc], by rw [hc]⟩

/-! ## A legacy step on a pinned assertion -/

theorem ext1_isSome {b x : BlockId} {S : Nat} {K : BlockKind} (h : x = b) : (ext1 b S K x).isSome := by
  subst h; simp [ext1]

/-- **A legacy step on an assertion pinned by `bext b S K`** (all of `X`'s cells lie in `b` and
record `(S, K)`), whose post keeps a cell of `b` recording `(S', K')`: the post gets `bext b S'
K'`. -/
theorem CTriple.step_bext {Tgt α β : Type} {H : FAssn} {X : Assn} {c : MemM α} {Y : α → Assn}
    {f : α → ConcM Tgt β} {R : β → FAssn} {b : BlockId} {S S' : Nat} {K K' : BlockKind}
    (ht : TotalTriple X c Y) (hc : Tame c)
    (hX : ∀ h, X h → ∀ l c, h l = some c → l.1 = b ∧ c.size = S ∧ c.kind = K)
    (hY : ∀ v h, Y v h → ∃ x c, h (b, x) = some c ∧ c.size = S' ∧ c.kind = K')
    (hf : ∀ v, CTriple (H ⋆ (up (Y v) ⋆ bext b S' K')) (f v) R) :
    CTriple (H ⋆ (up X ⋆ bext b S K)) (ConcM.liftMem c >>= f) R := by
  refine CTriple.pre (CTriple.step (E := ext1 b S K) (B := fun x => x = b) ht hc
    (fun h hx l c hl => (hX h hx l c hl).1)
    (fun h hx l c S₀ K₀ hl he => by
      obtain ⟨e1, e2, e3⟩ := hX h hx l c hl
      simp only [ext1, e1, if_pos, Option.some.injEq, Prod.mk.injEq] at he
      exact ⟨e2.trans he.1, e3.trans he.2⟩)
    (SizeFree.of_pinned fun h hx l c hl => ext1_isSome (hX h hx l c hl).1)
    (.inl fun _ h => ext1_isSome h) fun v => ?_) fun _ h => sep_mono_right (fun _ y => up_sep_bext y) h
  refine CTriple.eupd (EUpd.frameL (P := upPost (Y v) _ _) fun m r rF hh hp hs => ?_) (hf v)
  obtain ⟨x, cl, hcl, hs', hk'⟩ := hY v _ (by obtain ⟨E', ⟨hq, -⟩, -⟩ := hp; exact hq)
  simp only [FHeap.erase, Option.map_eq_some_iff] at hcl
  obtain ⟨fc, hfc, rfl⟩ := hcl
  exact EUpd.drop (fun _ h => h) m r rF hh
    (upPost_bext hp ⟨x, fc, hfc, hs', hk', fun h => ext1_isSome h⟩) hs

/-- **A legacy step on an assertion pinned by `bext b S K`** that keeps the extent: all of `X`'s
cells lie in `b` and record `(S, K)`, and so does a cell of the post. -/
theorem FTotalTriple.pinned {α : Type} {X : Assn} {c : MemM α} {Y : α → Assn} {b : BlockId}
    {S : Nat} {K : BlockKind} (ht : TotalTriple X c Y) (hc : Tame c)
    (hX : ∀ h, X h → ∀ l c, h l = some c → l.1 = b ∧ c.size = S ∧ c.kind = K)
    (hY : ∀ v h, Y v h → ∃ x c, h (b, x) = some c ∧ c.size = S ∧ c.kind = K) :
    FTotalTriple (up X ⋆ bext b S K) c (fun v => up (Y v) ⋆ bext b S K) := by
  refine ((FTotalTriple.ofTotal (E := ext1 b S K) (B := fun x => x = b) ht hc
    (fun h hx l c hl => (hX h hx l c hl).1)
    (fun h hx l c S₀ K₀ hl he => by
      obtain ⟨e1, e2, e3⟩ := hX h hx l c hl
      simp only [ext1, e1, if_pos, Option.some.injEq, Prod.mk.injEq] at he
      exact ⟨e2.trans he.1, e3.trans he.2⟩)
    (SizeFree.of_pinned fun h hx l c hl => ext1_isSome (hX h hx l c hl).1)
    (.inl fun _ h => ext1_isSome h)).pre fun _ h => up_sep_bext h).eupd_post fun v => ?_
  intro m r rF hh hp hs
  obtain ⟨x, cl, hcl, hs', hk'⟩ := hY v _ (by obtain ⟨E', ⟨hq, -⟩, -⟩ := hp; exact hq)
  simp only [FHeap.erase, Option.map_eq_some_iff] at hcl
  obtain ⟨fc, hfc, rfl⟩ := hcl
  exact EUpd.drop (fun _ h => h) m r rF hh
    (upPost_bext hp ⟨x, fc, hfc, hs', hk', fun h => ext1_isSome h⟩) hs

section Block

variable {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
  {al : Nat}

/-- The cells of `bytesAt p …` lie in `p`'s block and record its labels. -/
theorem bytesAt_cells (hpb : p.block = some b) :
    ∀ h, bytesAt p A S K bs h → ∀ l c, h l = some c → l.1 = b ∧ c.size = S ∧ c.kind = K :=
  fun _ hb _ _ hl => by
    obtain ⟨e, hs, hk⟩ := bytesAt_of_cell hb hl
    exact ⟨Option.some.inj (e.symm.trans hpb), hs, hk⟩

/-- A nonempty `bytesAt p …` has a cell of `p`'s block with its labels. -/
theorem bytesAt_cell_of (hpb : p.block = some b) (hpos : 0 < bs.size) {h : Heap}
    (hb : bytesAt p A S K bs h) : ∃ x c, h (b, x) = some c ∧ c.size = S ∧ c.kind = K := by
  obtain ⟨b', hpb', -, hh⟩ := hb
  rw [hpb] at hpb'; cases hpb'
  refine ⟨p.off.toNat, ⟨bs[0]!, A, S, K⟩, ?_, rfl, rfl⟩
  rw [hh]; simp [hpos]

/-- **A store at the start of a block's bytes** held with the block's extent (an escaping local,
`allocStack`): the bytes become the value's, followed by the rest. -/
@[fsym] theorem FTotalTriple.storeBlock (w : T) (hpb : p.block = some b)
    (hn : 0 < (Enc.encode w).size) (hk : (Enc.encode w).size ≤ bs.size)
    (ha : (A + p.off.toNat) % al = 0) (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.store al p w)
      (fun _ => up (bytesAt p A S K (writeBytes bs 0 (Enc.encode w))) ⋆ bext b S K) := by
  refine FTotalTriple.pinned (fun m hP hF hd hm hp hst => ?_) (Tame.store al p w)
    (bytesAt_cells hpb) fun _ _ h => bytesAt_cell_of hpb
      (by rw [writeBytes_size _ _ _ (by omega)]; omega) h
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ :=
    bytesAt_store (q := p) (k := 0) (a := al) (bs' := Enc.encode w) hp hm hd
      (by cases p; simp [Ptr.add]) hn (by omega) (by simpa using ha) hst hK
  exact ⟨(), m', h', hrun, hd', hm', hb', hst'⟩

/-- **A load at the start of a block's bytes** held with the block's extent, whose first bytes
decode to `v`. -/
@[fsym] theorem FTotalTriple.loadBlock {v : T} (hpb : p.block = some b) (hn : 0 < Enc.size T)
    (hk : Enc.size T ≤ bs.size) (hv : Enc.decode (bs.extract 0 (Enc.size T)) = pure v)
    (ha : (A + p.off.toNat) % al = 0) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.load T al p)
      (fun x => ⟪x = v⟫ ⋆ (up (bytesAt p A S K bs) ⋆ bext b S K)) := by
  refine (FTotalTriple.pinned (Y := fun x => ⌜x = v⌝ ∗ bytesAt p A S K bs)
    (fun m hP hF hd hm hp hst => ?_) (Tame.load T al p) (bytesAt_cells hpb)
    fun _ _ h => bytesAt_cell_of hpb (by omega) (Zig.sep_lift.mp h).2).post fun x r h => ?_
  · obtain ⟨_, blk, hacc, -, -, -, hx⟩ := bytesAt_access (q := p) (k := 0) (n := Enc.size T)
      (a := al) hp hm (by cases p; simp [Ptr.add]) hn (by omega) (by simpa using ha)
    refine ⟨v, _, hP, load_run hacc (by rw [hx]; simpa using hv)
      (noRace_of_singleThread hst.single _ _ _ _), hd, ?_, Zig.sep_lift.mpr ⟨rfl, hp⟩,
      hst.recordAt _ _ _ _⟩
    funext l; rw [Mem.heap_recordAt]; exact congrFun hm l
  · obtain ⟨r₁, r₂, hd, e, h1, h2⟩ := h
    obtain ⟨hx, h1⟩ := up_lift.mp h1
    exact sep_lift.mpr ⟨hx, r₁, r₂, hd, e, h1, h2⟩

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
