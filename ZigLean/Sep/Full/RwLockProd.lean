import ZigLean.Sep.Full.RwLockImpl
import ZigLean.Sep.Full.LockProd

/-!
# The reader/writer lock's two-lock product

(ledger #two-lock-product, item (5).) `FRw.Fits` (`ZigLean/Sep/Full/RwLockImpl.lean`) states the
protocol with the reader/writer lock as two lock views of one invariant: the outer mutex `M` with
the rwlock as its primitive (`M.Fits W.prim P UM _`) and the semaphore next to its mutex `L`
(`S.Fits P US _`). `M` and `L` are one pair over the ghost value (`FRw.pair`), so both views are
the two-lock product of `ZigLean/Sep/Full/LockProd.lean`: `M`'s rest is `L`'s side next to a
common rest (`UM = FLock.Pair.U L U₀`), and `L`'s rest is `M`'s side next to it
(`US = FLock.Pair.U M U₀`), with the client's base `U₀` at the common rest. This module builds
the views from `U₀` and the client's obligations stated at `U₀`.

- **The rwlock's invariant at the common rest.** The client's `U₀` keeps `W.Inv` at the common
  rest; `FRw.Inv.frame` gives it at `M`'s rest (`L`'s side next to the common rest), the
  primitive's `Sub` of `M`'s view.
- **The rwlock's own steps keep the product** (`FRw.U_step`, `M.Fits.kstep` at `Step`): `L` is
  kept over the atomic op at the state word (`FLock.Pair.Keeps.wordStep`): the op changes no
  place or held resource of `L`, and `L`'s resource (the count and the pool) only through
  `RwPosted`, which the op keeps (`Step`'s iff, `cnt_posted`/`cnt_idle`,
  `pool_posted`/`pool_idle`); `t`'s new part stays apart from what it holds of `L`, which lies in
  `M`'s rest (`M`'s invariant after the step). The invariants' own splits of the rest identify
  `Step`'s free resources with the common rest's (`Split.unique`): `L`'s side lies in the rest of
  the rest, which the op keeps, so the common rest after the step is the word's new cells, the
  new free resource and the same rest of the rest, and the rwlock's invariant holds there
  (`Inv.unframe`). The client keeps `U₀` given these facts (`W.Moves` at the common rest).
- **The outer mutex's view** (`FRw.fitsM`): `FLock.Pair.fits` at `K := W.prim` with `ok` the
  client's `okM` at `L`'s `away`. The product gives the queue premise (`away`), `M`'s `noGather`
  (`M.R = emp`), `ok_calm` (the calm places are out of the semaphore's code), `sub` and `kstep`;
  the client gives its own `U₀`'s obligations.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

namespace FRw

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C} {W : FRw γ X Y M L C S}

/-! ## The rwlock's own steps keep the product -/

/-- **A step of the rwlock's own code keeps the two-lock product's rest** at the outer mutex
(`M.Fits.kstep` at `Step`, module doc): `L` stays kept at the same free and holders' resources,
and the common rest after the step is `rX₀'`, the word's new cells beside the new free resource
and the same rest of the rest (`Moves` at the common rest), where the rwlock's invariant holds.
The client keeps its base `U₀` (`hcl`), which keeps the rwlock's invariant (`hsub`). -/
theorem U_step {U₀ : (ThreadId → γ) → Res → Mem → Prop} {t : ThreadId} {G G' : ThreadId → γ}
    {rX rX' : Res} {m m' : Mem} (hs : W.Step t G rX m G' rX' m')
    (hU : FLock.Pair.U L U₀ G rX m) (hsub : ∀ G rX m, U₀ G rX m → W.Inv G rX m)
    (hcl : ∀ sB rL rH rX₀ rX₀' rY rY', rX = rsum sB rX₀ → rX' = rsum sB rX₀' →
      Res.Sim sB (FLock.side L m rL rH) → L.Keeps G m rL rH rX₀ →
      L.Keeps G' m' rL rH rX₀' → U₀ G rX₀ m → W.Inv G' rX₀' m' →
      rX₀ = rsum (W.st.cellsR m) rY → rX₀' = rsum (W.st.cellsR m') rY' →
      W.Moves G m rY G' m' rY' → U₀ G' rX₀' m') :
    FLock.Pair.U L U₀ G' rX' m' := by
  obtain ⟨hM, -, hM', hWI', -, ⟨hr, hfs⟩, hoth, hx, -, -, hlph, hlheld, -, -, hpost, rF, rF',
    rO, he, he', hsp, hsp'⟩ := hs
  obtain ⟨sB, rL, rH, rX₀, rfl, hsB, hk, hu⟩ := hU
  have hf := hk.facts
  have hbL : L.BlkOk m := hf.w.blk
  have hI₀ := hsub _ _ _ hu
  obtain ⟨rF₀, rO₀, rfl, hsp₀, -⟩ := hI₀.split
  -- the pieces of the common rest, apart from `L`'s side as the rest stores it (`sB`)
  have hsX := hsB.disj hk.side_disj
  have hsX1 := FHeap.disjoint_union_right.mp hsX
  have hsX2 := FHeap.disjoint_union_right.mp hsX1.2
  -- `L`'s side owns no byte of the state word: the word's cells are in the common rest, and `M`'s
  -- rest holds them as cells, so no share of them
  have hcell : ∀ l, W.st.In l →
      (rsum (W.st.cellsR m) (rsum rF₀ rO₀)).heap l ≠ none := fun l hl e =>
    cellsAt_some hl (hI₀.ok.cellIn hl) (rsum_heap_none.mp e).1
  have hsW : ∀ l, W.st.In l → sB.heap l = none := fun l hl =>
    (hsX l).resolve_right (hcell l hl)
  have hsO : ∀ l, W.st.In l → (FLock.side L m rL rH).owned l = none := by
    intro l hl
    obtain ⟨rLM, hoM, -⟩ := hM.rest
    have hne : (rsum (M.wordR m) (rsum rLM (rsum sB
        (rsum (W.st.cellsR m) (rsum rF₀ rO₀))))).heap l ≠ none := fun e =>
      hcell l hl (rsum_heap_none.mp (rsum_heap_none.mp (rsum_heap_none.mp e).2).2).2
    have hns : ¬ (sB.gh.share l).Pos := fun hp' =>
      hoM.rest_noShare hne (by
        show (((M.wordR m).gh.add (rLM.gh.add (sB.gh.add
          (rsum (W.st.cellsR m) (rsum rF₀ rO₀)).gh))).share l).Pos
        simp only [Ghost.add_share]
        exact SCell.pos_add_iff.mpr (.inr (SCell.pos_add_iff.mpr (.inr
          (SCell.pos_add_iff.mpr (.inl hp'))))))
    exact hsB.owned_none.mp (Classical.byContradiction fun hn =>
      (Res.owned_ne.mp hn).elim (fun h => h (hsW l hl)) hns)
  -- `Step`'s split is the common rest's, with `L`'s side in the rest of the rest
  have hrot : rsum sB (rsum (W.st.cellsR m) (rsum rF₀ rO₀)) =
      rsum (W.st.cellsR m) (rsum rF₀ (rsum sB rO₀)) :=
    rsum_rot hsX1.1 hsX2.1
  obtain ⟨rfl, rfl⟩ := hsp.unique_cells (hsp₀.frame hsW hsX2.1.symm) (he.symm.trans hrot)
  -- the common rest after the step
  have hFs : FHeap.Disjoint rF'.heap sB.heap := (FHeap.disjoint_union_right.mp hsp'.2.1).1
  have hsC' : FHeap.Disjoint sB.heap (W.st.cellsR m').heap := disj_cellsAt hsW
  have hrot' : rsum (W.st.cellsR m') (rsum rF' (rsum sB rO₀)) =
      rsum sB (rsum (W.st.cellsR m') (rsum rF' rO₀)) :=
    (rsum_rot hsC' hFs.symm).symm
  have hsp₀' : W.Split G' m' rF' rO₀ := hsp'.unframe
  have hI₀' : W.Inv G' (rsum (W.st.cellsR m') (rsum rF' rO₀)) m' :=
    hWI'.unframe hsp₀' (hWI'.owns_split he' hsp')
  -- `L` is kept over the op at the word
  have hG : ∀ u, L.ph (G' u) = L.ph (G u) ∧ L.held (G' u) = L.held (G u) := fun u => by
    by_cases e : u = t
    · subst e; exact ⟨hlph, hlheld⟩
    · rw [hoth u e]; exact ⟨rfl, rfl⟩
  have hLR := lR_eq (W := W) hpost hx
  have hthr : m'.threads = m.threads := hr.threads
  have hpd : ∀ u, FHeap.Disjoint (L.part (G' u)).heap (L.held (G' u)).heap := fun u => by
    by_cases e : u = t
    case neg => rw [hoth u e]; exact hf.pdisj u
    rw [e, hlheld]
    by_cases hg : L.ph (G t) = .gone
    · rw [hf.idle t (by rw [hg]; rfl)]; exact fun _ => .inr rfl
    obtain ⟨hut, hju⟩ := hf.w.live t hg
    obtain ⟨rj, hrj, hsj⟩ := sepN_mem hk.held hut
    simp only [partOf, FLock.heldOf, hju, Bool.false_eq_true, ↓reduceIte] at hrj; subst hrj
    intro l
    by_cases hn : (L.held (G t)).heap l = none
    · exact .inr hn
    refine .inl ?_
    obtain ⟨rLM', hoM', -⟩ := hM'.rest
    have hO : (rsum (M.wordR m') (rsum rLM' rX')).heap l ≠ none := fun e => by
      rw [he', hrot'] at e
      refine hsj l hn ?_
      have hsn := (rsum_heap_none.mp (rsum_heap_none.mp (rsum_heap_none.mp e).2).2).1
      exact (rsum_heap_none.mp (rsum_heap_none.mp (hsB.none.mp hsn)).2).2
    have h0 := hoM'.part_off (u := t) (by rw [hthr]; exact hut) hO
    have hj' : joinedB m' t = false := by rw [LockWord.joinedB_congr hthr]; exact hju
    simp only [FLock.own, hj', Bool.false_eq_true, ↓reduceIte] at h0
    rw [← W.pair.part]
    exact (rsum_heap_none.mp h0).1
  have hsC'' := hsB.symm.disj hsC'
  have hFs' := hsB.symm.disj hFs.symm
  have hxd : FHeap.Disjoint (rsum rL rH).heap (rsum (W.st.cellsR m') (rsum rF' rO₀)).heap :=
    FHeap.disjoint_union_right.mpr ⟨(FHeap.disjoint_union_left.mp hsC'').2,
      FHeap.disjoint_union_right.mpr ⟨(FHeap.disjoint_union_left.mp hFs').2,
        (FHeap.disjoint_union_right.mp (FHeap.disjoint_union_right.mp hk.xdisj).2).2⟩⟩
  have hxo : L.Off (rsum (W.st.cellsR m') (rsum rF' rO₀)).heap.erase :=
    LockWord.off_erase.mpr fun l hl => by
      have hsl : sB.heap l ≠ none := fun e =>
        LockWord.wordR_some hbL hl (rsum_heap_none.mp (hsB.none.mp e)).1
      refine rsum_heap_none.mpr ⟨cellsAt_none fun hw => hsl (hsW l hw),
        rsum_heap_none.mpr ⟨(hFs l).resolve_right hsl, ?_⟩⟩
      exact (rsum_heap_none.mp (rsum_heap_none.mp (LockWord.off_erase.mp hk.xoff l hl)).2).2
  obtain ⟨hside, hk'⟩ := FLock.Pair.Keeps.wordStep hk hr hfs hsO hG
    (fun r h => by rw [hLR]; exact h) hpd hxd hxo
  have hrX' : rX' = rsum sB (rsum (W.st.cellsR m') (rsum rF' rO₀)) := by rw [he', hrot']
  exact ⟨sB, rL, rH, _, hrX', by rw [hside]; exact hsB, hk',
    hcl sB rL rH _ _ _ _ rfl hrX' hsB hk hk' hu hI₀' rfl rfl
      ⟨hpost, _, rF', rO₀, rfl, rfl, hsp₀, hsp₀'⟩⟩

/-! ## The outer mutex's view -/

variable {Tgt : Type} {P : Proto Tgt γ} {U₀ : (ThreadId → γ) → Res → Mem → Prop} {okM : γ → Prop}

/-- **The outer mutex's view of the two-lock product** (module doc; `FRw.Fits.m`):
`FLock.Pair.fits` at the rwlock's primitive, where the outer mutex's code runs at `L`'s `away`.
The client gives its base `U₀`'s obligations at the common rest (`stable`, `atStop`, `tick`,
`kstep` with `U_step`'s facts, `holdLive`), that `U₀` keeps the rwlock's invariant (`hsub`), the
laws of the rwlock's and the semaphore's places next to `M` (`lph` … `set_part`) and of `okM`. -/
theorem fitsM
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L U₀ G rX m)
    (fin : ∀ g, P.fin g → M.ph g = .gone) (joins : ∀ g, P.joins g → M.ph g = .out)
    (kfin : ∀ g, P.fin g → W.ph g = .out ∧ S.place.ph g = (.out, .out))
    (kjoins : ∀ g, P.joins g → W.ph g = .out ∧ S.place.ph g = (.out, .out))
    (okM_set : ∀ g a, okM (W.set g a) ↔ okM g) (okM_m : ∀ g p h, okM (M.set g p h) ↔ okM g)
    (okM_part : ∀ g r, okM (M.setPart g r) ↔ okM g)
    (stable : ∀ G rL rH rX m m' t p h, okM (G t) → L.ph (G t) = .away → M.ph (G t) ≠ .gone →
      M.ph (G t) ≠ .away → M.ph (G t) ≠ .holdsAway →
      M.Inv G (rsum (FLock.side L m rL rH) rX) m → L.Keeps G m rL rH rX → U₀ G rX m →
      M.Step t m m' → (M.ph (G t) = .holds → p ≠ .holds → M.Before m' (m.clocks[t]!)) →
      M.Transfer G (rsum (FLock.side L m rL rH) rX) m m' t p h →
      U₀ (upd G t (M.set (G t) p h)) rX m')
    (atStop : ∀ G rX m t, t < m.threads.size → U₀ G rX m → U₀ G rX { m with current := t })
    (tick : ∀ t G rX m r, U₀ G rX m → U₀ (upd G t (M.setPart (G t) r)) rX m.ticked)
    (hsub : ∀ G rX m, U₀ G rX m → W.Inv G rX m) (apart : W.st.ApartL M.toLockWord)
    (lph : ∀ g p, M.ph (W.place.set g p) = M.ph g)
    (lpart : ∀ g p, M.part (W.place.set g p) = M.part g)
    (lheld : ∀ g p, M.held (W.place.set g p) = M.held g)
    (ph_l : ∀ g q h, W.place.ph (M.set g q h) = W.place.ph g)
    (set_l : ∀ g p q h, W.place.set (M.set g q h) p = M.set (W.place.set g p) q h)
    (ph_part : ∀ g r, W.place.ph (M.setPart g r) = W.place.ph g)
    (set_part : ∀ g p r, W.place.set (M.setPart g r) p = M.setPart (W.place.set g p) r)
    (kstep : ∀ t G G' rX rX' m m' sB rL rH rX₀ rX₀' rY rY', W.Step t G rX m G' rX' m' →
      rX = rsum sB rX₀ → rX' = rsum sB rX₀' → Res.Sim sB (FLock.side L m rL rH) →
      L.Keeps G m rL rH rX₀ → L.Keeps G' m' rL rH rX₀' → U₀ G rX₀ m → W.Inv G' rX₀' m' →
      rX₀ = rsum (W.st.cellsR m) rY → rX₀' = rsum (W.st.cellsR m') rY' →
      W.Moves G m rY G' m' rY' → U₀ G' rX₀' m')
    (holdLive : ∀ G rX m v, M.Inv G rX m → FLock.Pair.U L U₀ G rX m → M.ph (G v) = .holdsAway →
      P.Live v G m) :
    M.Fits W.prim P (FLock.Pair.U L U₀) (fun g => okM g ∧ L.ph g = .away) :=
  W.pair.fits inv fin joins
    (fun g p h => by rw [okM_m, W.pair.ph_ab])
    (fun g r => by rw [okM_part, W.pair.setPart, L.ph_setPart])
    (fun _ _ _ _ _ hok _ _ _ _ => .inl hok.2)
    (fun G rL rH rX m m' t p h hok hg ha hh hi hk hu hs hb htr =>
      stable G rL rH rX m m' t p h hok.1 hok.2 hg ha hh hi hk hu hs hb htr)
    atStop tick
    (fun _ _ _ _ _ _ rL h l => .inr (by rw [W.mR] at h; exact FAssn.Unshared.emp _ h l))
    (fun g h => Prod.ext (kfin g h).1 (kfin g h).2)
    (fun g h => Prod.ext (kjoins g h).1 (kjoins g h).2)
    (fun G _ _ _ rX m hsB hk hu => (hsub G rX m hu).frame (hsB.disj hk.side_disj))
    apart lph lpart lheld
    (fun G t p r h => by rw [W.mR] at h ⊢; exact h)
    ph_l set_l ph_part set_part (fun i => nomatch i) (fun i => nomatch i)
    (fun g p q hp hq => by
      show (okM (W.set (S.place.set g p.2) p.1) ∧ L.ph (W.set (S.place.set g p.2) p.1) = .away) ↔
        (okM (W.set (S.place.set g q.2) q.1) ∧ L.ph (W.set (S.place.set g q.2) q.1) = .away)
      rw [hp.2, hq.2, okM_set, okM_set, W.lph, W.lph])
    (fun t G rX m G' rX' m' hs hU => U_step hs hU hsub fun sB rL rH rX₀ rX₀' rY rY' =>
      kstep t G G' rX rX' m m' sB rL rH rX₀ rX₀' rY rY' hs)
    holdLive

end FRw

end Full
end Zig
