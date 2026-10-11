import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Extent

/-!
# Pinned blocks: legacy steps and allocators that own a block's full extent

(`docs/sep-full-state.md` §Block extents.) A legacy assertion whose bytes all lie in one block
`b` whose full extent `bext b S K` is held next to it is *pinned*: its cells' sizes are the
block's. Such an assertion lifts to the full-state logic with the pinned bridge
(`FTotalTriple.ofTotal`, `E = {b ↦ (S, K)}`), and the program may change the block's extent
(`munmap`, `mremap`): the post gets the block's new full extent back from the cells it owns
(`upPost_bext`).

* `CTriple.step_bext`: one legacy step on a pinned assertion, with the extent read back from the
  post's cells.
* **Pinned allocators** (`pinnedInv`): an allocator whose grant is the start of a block that the
  grant's legacy token (`Pinned`) pins (the page allocator: a grant is a whole mapping; the token
  owns the rest of its last page). Its full-state token holds the block's authority with the
  fraction `q'` that it did not lend to the grant's share (`q' + q = 1`). `free`, `resize` and
  `remap` collect the whole extent (`EUpd.unlend`), run the legacy triple through the pinned
  bridge, and lend half of the new extent to the new grant (`pinned_lend`). So a legacy
  `AllocSpec`-style proof of such an allocator gives its `FAllocSpec` fields (`pinned_free`,
  `pinned_resize`, `pinned_remap`); `alloc` builds its grants with `pinned_lend`.
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

/-! ## Pinned allocators -/

/-- **A legacy allocator invariant whose grants pin their block**: no allocator state, the
token's cells lie in the grant's block and record the extent `(S, K)`, and the block reaches the
grant's end. -/
structure Pinned (L : AllocInv) : Prop where
  own : L.own = Assn.emp
  cells : ∀ p n k A S K h, L.tok p n k A S K h → ∀ l c, h l = some c →
    p.block = some l.1 ∧ c.size = S ∧ c.kind = K
  bound : ∀ p n k A S K h, L.tok p n k A S K h → p.off.toNat + n ≤ S

/-- The full-state invariant of a pinned allocator with state `own`: the token is the legacy one
and the authority over the grant's block, with the fraction `q'` that the grant's share `q` leaves
(`q' + q = 1`). -/
def pinnedInv (L : AllocInv) (own : FAssn) : FAllocInv where
  own := own
  tok p n k A S K q := FAssn.ex fun b => FAssn.ex fun q' =>
    ⟪p.block = some b ∧ q'.add q = Frac.one⟫ ⋆ (up (L.tok p n k A S K) ⋆ bauth b S K q')
  fits := L.fits

section Pinned

variable {L : AllocInv} (hL : Pinned L) {own : FAssn}
include hL

/-- The legacy grant at fixed `A S K`: its cells lie in `p`'s block and record `(S, K)`. -/
theorem Pinned.grant_cells {p : Ptr} {A S k : Nat} {K : BlockKind} {bs : Array Byte} {h : Heap}
    (hg : (regionIn p A S K (2 ^ k) bs ∗ L.tok p bs.size k A S K) h) {l : Loc} {c : Cell}
    (hl : h l = some c) : p.block = some l.1 ∧ c.size = S ∧ c.kind = K := by
  obtain ⟨h₁, h₂, -, rfl, ⟨-, -, hb⟩, ht⟩ := hg
  simp only [Heap.union_apply] at hl
  cases e : h₁ l with
  | some c₁ => rw [e] at hl; cases hl; exact bytesAt_of_cell hb e
  | none => rw [e] at hl; exact hL.cells _ _ _ _ _ _ _ ht l c hl

/-- **Lend half of a pinned block's extent to a grant.** -/
theorem pinned_lend {p : Ptr} {b : BlockId} {A S k : Nat} {K : BlockKind} {bs : Array Byte}
    (hb : p.block = some b) :
    EUpd (up (regionIn p A S K (2 ^ k) bs ∗ L.tok p bs.size k A S K) ⋆ bext b S K)
      ((pinnedInv L own).granted p k bs) := by
  intro m r rF hh h hs
  have hk : p.off.toNat + bs.size ≤ S := by
    obtain ⟨r₁, r₂, _, _, hu, _⟩ := h
    have hu1 : (regionIn p A S K (2 ^ k) bs ∗ L.tok p bs.size k A S K) r₁.heap.erase := hu.1
    obtain ⟨h₁, h₂, _, _, _, ht⟩ := hu1
    exact hL.bound _ _ _ _ _ _ _ ht
  have hq := Frac.half_add_half Frac.one
  refine (EUpd.trans (P' := (up (regionIn p A S K (2 ^ k) bs) ⋆ up (L.tok p bs.size k A S K)) ⋆
      bauth b S K (Frac.one.half.add Frac.one.half)) (EUpd.of_imp fun r h => by
        rw [hq]; exact sep_mono_left (fun _ x => up_sep x) h)
    (EUpd.trans (EUpd.frameL (EUpd.lend (b := b) (K := K) hk (Frac.half_pos (by decide))))
      (EUpd.of_imp fun r h => ?_))) m r rF hh h hs
  refine ⟨A, S, K, Frac.one.half, ?_⟩
  have h' : (up (regionIn p A S K (2 ^ k) bs) ⋆ ((up (L.tok p bs.size k A S K) ⋆
      bauth b S K Frac.one.half) ⋆ bshare b Frac.one.half (p.off.toNat + bs.size))) r :=
    of_eq (by ac_rfl) h
  exact sep_mono_right (fun _ y => sep_mono (fun _ x => ⟨b, Frac.one.half, sep_lift.mpr ⟨⟨hb, hq⟩, x⟩⟩)
    (fun _ x => ⟨b, sep_lift.mpr ⟨hb, x⟩⟩) y) h'

omit hL in
/-- A grant of a pinned allocator, opened: the legacy grant at its `A S K` with its block's
whole extent (the token's authority and the grant's share, `EUpd.unlend`). -/
theorem pinned_open {α : Type} {p : Ptr} {k : Nat} {bs : Array Byte} {c : MemM α} {Q : α → FAssn}
    (h : ∀ b A S K, p.block = some b →
      FTotalTriple (upE (regionIn p A S K (2 ^ k) bs ∗ L.tok p bs.size k A S K) (ext1 b S K)) c Q) :
    FTotalTriple ((pinnedInv L own).granted p k bs) c Q := by
  refine FTotalTriple.ex fun A => FTotalTriple.ex fun S => FTotalTriple.ex fun K =>
    FTotalTriple.ex fun q => ?_
  refine FTotalTriple.pre (P := FAssn.ex fun b => FAssn.ex fun q' =>
      ⟪p.block = some b ∧ q'.add q = Frac.one⟫ ⋆ ((up (regionIn p A S K (2 ^ k) bs) ⋆
        up (L.tok p bs.size k A S K)) ⋆ (bauth b S K q' ⋆ bshare b q (p.off.toNat + bs.size))))
    (FTotalTriple.ex fun b => FTotalTriple.ex fun q' => FTotalTriple.lift fun ⟨hb, hq⟩ => ?_) ?_
  · refine FTotalTriple.eupd (EUpd.trans (EUpd.frameL EUpd.unlend) (EUpd.of_imp fun r h => ?_))
      (h b A S K hb)
    rw [hq] at h
    exact up_sep_bext (sep_mono_left (fun _ x => sep_up x) h)
  · rintro r ⟨r₁, r₂₃, hd, rfl, hR, r₂, r₃, hd', rfl, ⟨b, q', ht⟩, ⟨b', hs⟩⟩
    obtain ⟨⟨hb, hq⟩, ht⟩ := sep_lift.mp ht
    obtain ⟨hb', hs⟩ := sep_lift.mp hs
    rw [hb] at hb'; cases hb'
    obtain ⟨r₄, r₅, hd'', rfl, hT, hA⟩ := ht
    have h' : (up (regionIn p A S K (2 ^ k) bs) ⋆ ((up (L.tok p bs.size k A S K) ⋆ bauth b S K q') ⋆
        bshare b q (p.off.toNat + bs.size))) _ :=
      ⟨r₁, _, hd, rfl, hR, _, r₃, hd', rfl, ⟨r₄, r₅, hd'', rfl, hT, hA⟩, hs⟩
    exact ⟨b, q', sep_lift.mpr ⟨⟨hb, hq⟩, of_eq (by ac_rfl) h'⟩⟩

/-- The legacy triple of an entry of a pinned allocator, lifted with the grant's block pinned. -/
theorem pinned_lift {α : Type} {p : Ptr} {k : Nat} {bs : Array Byte} {c : MemM α} {Q : α → Assn}
    {b : BlockId} {A S : Nat} {K : BlockKind} (ht : TotalTriple (granted L p k bs) c Q) (hc : Tame c)
    (hb : p.block = some b) :
    FTotalTriple (upE (regionIn p A S K (2 ^ k) bs ∗ L.tok p bs.size k A S K) (ext1 b S K)) c
      (fun v => upPost (Q v) (fun x => x = b) (ext1 b S K)) := by
  have hcell : ∀ h, (regionIn p A S K (2 ^ k) bs ∗ L.tok p bs.size k A S K) h → ∀ l c, h l = some c →
      l.1 = b ∧ c.size = S ∧ c.kind = K := fun h hg l c hl => by
    obtain ⟨e1, e2, e3⟩ := hL.grant_cells hg hl
    rw [hb] at e1; exact ⟨(Option.some.inj e1).symm, e2, e3⟩
  refine FTotalTriple.ofTotal (ht.conseq (fun h hg => ⟨A, S, K, hg⟩) fun _ _ x => x) hc
    (fun h hg l c hl => (hcell h hg l c hl).1) (fun h hg l c S₀ K₀ hl he => ?_)
    (SizeFree.of_pinned fun h hg l c hl => ext1_isSome (hcell h hg l c hl).1)
    (.inl fun _ h => ext1_isSome h)
  obtain ⟨e1, e2, e3⟩ := hcell h hg l c hl
  simp only [ext1, e1, if_pos, Option.some.injEq, Prod.mk.injEq] at he
  exact ⟨e2.trans he.1, e3.trans he.2⟩

/-- **A legacy grant comes back as a full-state one**: the lifted post's cells give the block's
new extent (`upPost_bext`, for a block that was pinned or is new), and half of it is lent to the
grant. -/
theorem pinned_granted {q : Ptr} {k : Nat} {bs : Array Byte} {B : BlockId → Prop}
    {E : BlockId → Option (Nat × BlockKind)} (hpos : 0 < bs.size) (hBE : ∀ x, B x → (E x).isSome) :
    EUpd (upPost (granted L q k bs) B E) ((pinnedInv L own).granted q k bs) := by
  intro m r rF hh h hs
  obtain ⟨A, S, K, hg⟩ : ∃ A S K, (regionIn q A S K (2 ^ k) bs ∗ L.tok q bs.size k A S K) r.heap.erase := by
    obtain ⟨E', ⟨hq, -⟩, -⟩ := h; exact hq
  obtain ⟨b, hb, x, fc, hfc, hS, hK⟩ := regionIn_first hpos hg
  exact (EUpd.drop (fun _ h => h)).trans (pinned_lend hL hb) m r rF hh
    (upPost_bext (h.mono hg) ⟨x, fc, hfc, hS, hK, hBE b⟩) hs

/-- The same under the legacy allocator state and a fact on the new contents. -/
theorem pinned_granted_ex {q : Ptr} {k : Nat} {φ : Array Byte → Prop} {B : BlockId → Prop}
    {E : BlockId → Option (Nat × BlockKind)} (hφ : ∀ bs, φ bs → 0 < bs.size)
    (hBE : ∀ x, B x → (E x).isSome) :
    EUpd (upPost (L.own ∗ Assn.ex fun bs => ⌜φ bs⌝ ∗ granted L q k bs) B E)
      (FAssn.ex fun bs => ⟪φ bs⟫ ⋆ (pinnedInv L own).granted q k bs) := by
  intro m r rF hh h hs
  obtain ⟨bs, hφs, hg⟩ : ∃ bs, φ bs ∧ granted L q k bs r.heap.erase := by
    obtain ⟨E', ⟨hq, -⟩, -⟩ := h
    rw [hL.own] at hq
    obtain ⟨bs, hb⟩ := Zig.sep_emp.mp (Zig.sep_comm hq)
    exact ⟨bs, Zig.sep_lift.mp hb⟩
  obtain ⟨r', hh', hr'⟩ := pinned_granted hL (hφ bs hφs) hBE m r rF hh (h.mono hg) hs
  exact ⟨r', hh', bs, sep_lift.mpr ⟨hφs, hr'⟩⟩

theorem pinned_granted_own {q : Ptr} {k : Nat} {bs : Array Byte} {B : BlockId → Prop}
    {E : BlockId → Option (Nat × BlockKind)} (hpos : 0 < bs.size) (hBE : ∀ x, B x → (E x).isSome) :
    EUpd (upPost (L.own ∗ granted L q k bs) B E) ((pinnedInv L own).granted q k bs) := by
  intro m r rF hh h hs
  have hg : granted L q k bs r.heap.erase := by
    obtain ⟨E', ⟨hq, -⟩, -⟩ := h
    rw [hL.own] at hq
    exact Zig.sep_emp.mp (Zig.sep_comm hq)
  exact pinned_granted hL hpos hBE m r rF hh (h.mono hg) hs

/-- **An entry of a pinned allocator** from its legacy total triple: the post's legacy grants
come back as full-state ones (`hQ`, by `pinned_granted`). -/
theorem pinned_entry {α : Type} {p : Ptr} {k : Nat} {bs : Array Byte} {c : MemM α} {Q : α → Assn}
    {Q' : α → FAssn} (ht : TotalTriple (granted L p k bs) c Q) (hc : Tame c)
    (hQ : ∀ b S K v, EUpd (upPost (Q v) (fun x => x = b) (ext1 b S K)) (Q' v)) :
    FTotalTriple (own ⋆ (pinnedInv L own).granted p k bs) c (fun v => own ⋆ Q' v) :=
  FLogic.total.frameL (R := own) (pinned_open fun b A S K hb =>
    (pinned_lift hL ht hc hb).eupd_post (hQ b S K))

/-- **`free`** of a pinned allocator. -/
theorem pinned_free {α : Type} {p : Ptr} {k : Nat} {bs : Array Byte} {c : MemM α}
    (ht : TotalTriple (granted L p k bs) c (fun _ => Assn.emp)) (hc : Tame c) :
    FTotalTriple (own ⋆ (pinnedInv L own).granted p k bs) c (fun _ => own) :=
  (pinned_entry hL ht hc fun _ _ _ _ => EUpd.upPost_up.trans (EUpd.of_imp fun _ h => up_emp.mp h)).post
    fun _ _ h => sep_emp.mp h

/-- **`resize`** of a pinned allocator. -/
theorem pinned_resize {p : Ptr} {k : Nat} {bs : Array Byte} {n : Nat} {c : MemM Bool}
    (hpos : 0 < bs.size) (hn : 0 < n) (ht : TotalTriple (granted L p k bs) c (resizePost L p k bs n))
    (hc : Tame c) :
    FTotalTriple (own ⋆ (pinnedInv L own).granted p k bs) c ((pinnedInv L own).resizePost p k bs n) :=
  (pinned_entry hL ht hc (Q' := fun v => if v then FAssn.ex fun bs' =>
      ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆ (pinnedInv L own).granted p k bs'
    else (pinnedInv L own).granted p k bs) fun b S K v => by
      cases v
      · exact pinned_granted_own hL hpos fun _ h => ext1_isSome h
      · exact pinned_granted_ex hL (fun _ h => h.1 ▸ hn) fun _ h => ext1_isSome h).post
    fun v _ h => by cases v <;> exact h

/-- **`remap`** of a pinned allocator. -/
theorem pinned_remap {p : Ptr} {k : Nat} {bs : Array Byte} {n : Nat} {c : MemM (Option Ptr)}
    (hpos : 0 < bs.size) (hn : 0 < n) (ht : TotalTriple (granted L p k bs) c (remapPost L p k bs n))
    (hc : Tame c) :
    FTotalTriple (own ⋆ (pinnedInv L own).granted p k bs) c ((pinnedInv L own).remapPost p k bs n) :=
  (pinned_entry hL ht hc (Q' := fun v => match v with
    | none => (pinnedInv L own).granted p k bs
    | some q => FAssn.ex fun bs' =>
      ⟪bs'.size = n ∧ keepsPrefix bs bs'⟫ ⋆ (pinnedInv L own).granted q k bs') fun b S K v => by
      cases v
      · exact pinned_granted_own hL hpos fun _ h => ext1_isSome h
      · exact pinned_granted_ex hL (fun _ h => h.1 ▸ hn) fun _ h => ext1_isSome h).post
    fun v _ h => by cases v <;> exact h

end Pinned

end Full
end Zig
