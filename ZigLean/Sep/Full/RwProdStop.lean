import ZigLean.Sep.Full.RwLockGhost
import ZigLean.Sep.Full.LockProdStop

/-!
# The end of a program with a reader/writer lock

(ledger #two-lock-product, item (5).) The dual of `RwProd.start`
(`ZigLean/Sep/Full/RwProdStart.lean`): a program whose invariant is the two-lock product at the
reader/writer lock's base ends with one thread that takes the lock's bytes back out of the rest
before it frees the object that holds the lock. This file proves that step once for every
program: the two-lock pair's end (`FLock.Pair.stop`) and the base's end (`FRw.Base.stop`).

- `Word.Ok.hits_le`, `Word.Ok.ownsCells`: the clock of a thread of the word's live set that is
  above every thread's owns the word's cells. `Word.Ok.backRel_le`: the release clock of the
  word's newest message happened before every clock that covers the accesses to the word
  (`Mem.MsgCov`).
- `FRw.Owns.owns`: what the reader/writer lock owns through its word, such a thread owns.
- `cellsAt_split`: a resource that holds the memory's cells at `W` is those cells and a rest.
- `FRw.Base.stop`: the base's end, for every reader/writer lock and every program's facts `E`.
  Every thread is out of the rwlock's code, and thread `t` (not ended at the outer mutex) has a
  clock above every thread's. `t` takes the state word's cells, the protected resource (with `R`)
  and the condition's two words' cells. The rest of the rest `rZ` stays: it pins the lock's block
  and holds the program's read-shared bytes, and the program's facts hold at it.
- `RwProd.stop`: the end of a program with a reader/writer lock over the product ghost value.
  `t` takes the outer mutex's word, the semaphore's count (`0`) and its mutex's word, the state
  word, the protected resource and the condition's two words.

The rest `rZ` (the pin of the block, the read-shared bytes, what the rest held before the start)
stays the rest: the base orders the accesses to the read-shared region only (`ReadShared`), not
every access to a byte of `rZ`. The program takes a piece `rT` of it with `FOwned.takeOwned`
once it has `m.OwnsRes t rT`.
-/

namespace Zig

namespace Conc.Word

open Full

variable {n nb : Nat} {W : Word n nb} {A : ThreadId → Prop}

/-- **An access to the word happened before the last thread**: thread `t` of the live set has a
clock above every thread's. -/
theorem Ok.hits_le {m : Mem} {t : ThreadId} (hw : W.Ok m A) (ht : t < m.threads.size) (hA : A t)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true)
    {e : FootprintEntry} (he : e ∈ m.footprint) (hh : W.Hits e) :
    VClock.le e.clock (m.clocks[t]!) = true := by
  rcases hw.wfp e he hh with ⟨-, v, hv, hle⟩ | h
  · exact VClock.le_trans hle (hall v hv)
  · exact h t ht hA

/-- **The last thread owns the word's cells**: thread `t` of the live set has a clock above every
thread's, and above every access to a block that does not exist yet (`hfut`: it owns its part). -/
theorem Ok.ownsCells {m : Mem} {t : ThreadId} (hw : W.Ok m A) (ht : t < m.threads.size) (hA : A t)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true)
    (hfut : ∀ e ∈ m.footprint, m.blocks.size ≤ e.block →
      VClock.le e.clock (m.clocks[t]!) = true) :
    m.OwnsRes t (W.cellsR m) := by
  refine .of_owns ?_
  intro e he htc
  rcases htc with ⟨x, h1, h2, h3⟩ | hb
  · have hin : W.In (e.block, x) := Classical.byContradiction fun hn =>
      h3 (cellsAt_owned_none hn)
    obtain ⟨hb, hx1, hx2⟩ := hin
    exact hw.hits_le ht hA hall he ⟨hb, x, h1, h2, hx1, hx2⟩
  · exact hfut e he hb

/-- **The release clock of the word's newest message happened before a clock that covers the
word's accesses** (`Mem.MsgCov`). -/
theorem Ok.backRel_le {m : Mem} (hw : W.Ok m A) (hmc : m.MsgCov) {c : VClock}
    (hc : ∀ e ∈ m.footprint, W.Hits e → VClock.le e.clock c = true) :
    VClock.le ((W.hist m).back!).relClock c = true := by
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none =>
    rw [hist_none fun i l h => by have h' := h.1; rw [hf] at h'; cases h']
    exact VClock.le_default c
  | some i =>
    obtain ⟨l, hl⟩ : ∃ l, W.Loc m i l := ⟨_, loc_of_find hf⟩
    obtain ⟨hlen, h0, -⟩ := hw.loc i l hl
    obtain ⟨hlb, hlo⟩ := loc_at hl
    obtain ⟨hi, hget, -⟩ := loc_get hl
    have hsz := W.sz_pos
    have hmem : l ∈ m.atomics := hget ▸ Array.getElem_mem hi
    have hcov := ((hmc l hmem (by omega)).2 (l.msgs[l.msgs.size - 1]'(by omega))
      (Array.getElem_mem _)).2
    have hb : (W.hist m).back! = ent (l.msgs.size - 1) (l.msgs[l.msgs.size - 1]'(by omega)) := by
      show (W.hist m)[(W.hist m).size - 1]! = _
      rw [hist_size hl]; exact hist_get hl (by omega)
    rw [hb]
    exact hcov c (ALoc.over_iff.mpr fun e he ⟨h1, h2, h3, h4⟩ =>
      hc e he (hits_of (h1.trans hlb) h2 (by omega) (by omega)))

end Conc.Word

namespace Full

open FAssn Conc Proto

/-- **A resource that holds the memory's cells at `W` is those cells and a rest** without a byte
of `W`, with the resource's other bytes, knowledge and ghost state. -/
theorem cellsAt_split {W : Zig.Loc → Prop} [DecidablePred W] {m : Mem} {r : Res}
    (h : ∀ l, W l → r.heap l = (cellsAt W m).heap l) :
    ∃ rZ : Res, r = rsum (cellsAt W m) rZ ∧ (∀ l, W l → rZ.heap l = none) ∧
      (∀ l, ¬ W l → rZ.heap l = r.heap l) ∧ rZ.know = r.know ∧ rZ.gh = r.gh := by
  obtain ⟨rh, rk, rg⟩ := r
  refine ⟨⟨fun l => if W l then none else rh l, rk, rg⟩, ?_, fun l hl => if_pos hl,
    fun l hl => if_neg hl, rfl, rfl⟩
  have hh : rh = (cellsAt W m).heap ∪ (fun l => if W l then none else rh l) := funext fun l => by
    rw [FHeap.union_apply]
    by_cases hl : W l
    · rw [if_pos hl, Option.or_none]; exact h l hl
    · rw [if_neg hl, cellsAt_none hl, Option.none_or]
  show (⟨rh, rk, rg⟩ : Res) = ⟨(cellsAt W m).heap ∪ (fun l => if W l then none else rh l),
    Know.none.union rk, Ghost.unit.add rg⟩
  rw [Know.none_union, Ghost.unit_add, ← hh]

namespace FRw

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C} {W : FRw γ X Y M L C S}

/-- **What the reader/writer lock owns through its word, the last thread owns**: thread `t` (not
ended at the outer mutex) has a clock above every thread's. An access to the resource happened
before every thread that has not ended, before the release clock of the word's newest message
(`Word.Ok.backRel_le`), or before a reader. -/
theorem Owns.owns {G : ThreadId → γ} {m : Mem} {r : Res} {t : ThreadId} (h : W.Owns G m r)
    (hok : W.st.Ok m fun u => M.ph (G u) ≠ .gone) (hmc : m.MsgCov) (ht : t < m.threads.size)
    (hg : M.ph (G t) ≠ .gone)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true)
    (hex : ∀ u, (W.ph (G u)).isRd = true → u < m.threads.size) : m.OwnsRes t r := by
  have key : ∀ e ∈ m.footprint,
      (e.Touches r.excl ∨ e.Touches r.shared ∨ m.blocks.size ≤ e.block) →
      VClock.le e.clock (m.clocks[t]!) = true := fun e he htc => by
    rcases h e he htc with h1 | h2 | ⟨-, -, u, hu, hle⟩
    · exact h1 t ht hg
    · exact VClock.le_trans h2 (hok.backRel_le hmc fun e' he' hh =>
        hok.hits_le ht hg hall he' hh)
    · exact VClock.le_trans hle (hall u (hex u hu))
  exact ⟨fun e he htc => key e he (htc.elim .inl fun hb => .inr (.inr hb)),
    fun e he _ htc => key e he (htc.elim (fun h => .inr (.inl h)) fun hb => .inr (.inr hb))⟩

namespace Base

/-- **The base's end** (module doc; the dual of `Base.start`), for every reader/writer lock and
every program's facts `E`. The parts and the base's rest `rX` are `FOwned`; thread `t`'s part is
`a`, with `P`. Every thread is out of the rwlock's code, `t` has not ended at the outer mutex and
its clock is above every thread's. The state word is apart from the condition's words (`hst`),
no resource with `R` has a byte of them (`hRoff`), and the program's read-shared bytes are none
of the bytes the lock's code changes (`hIo`; both as `FRw.Base.fits` takes them).

Then `t` takes the state word's cells, the protected resource (with `R`) and the cells of the
condition's two words: its new part `r` is its old part and these, apart from each other. The
rest of the rest `rZ` stays the rest: it pins the lock's block, the program's facts hold at it,
and its bytes are live. -/
theorem stop {E : FClient X} {Sz : Nat} {K : BlockKind} {G : ThreadId → γ} {m : Mem}
    {rX a : Res} {own : ThreadId → Res} {t : ThreadId} {P : FAssn}
    (hu : W.Base E Sz K G rX m) (ho : FOwned own rX m) (ht : t < m.threads.size)
    (hat : own t = a) (hP : P a) (hout : ∀ u, W.ph (G u) = .out) (hg : M.ph (G t) ≠ .gone)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true)
    (hst : ∀ l, W.st.In l → ¬ (C.S.In l ∨ C.Ep.In l))
    (hRoff : ∀ xs r l, W.R xs r → (C.S.In l ∨ C.Ep.In l) → r.heap l = none)
    (hIo : ∀ r l, E.Io r → W.Lk l → r.heap l = none) :
    ∃ r rZ, (P ⋆ ((fun r => r = W.st.cellsR m) ⋆ (W.R (W.xs G) ⋆
        ((fun r => r = C.S.cellsR m) ⋆ fun r => r = C.Ep.cellsR m)))) r ∧
      FOwned (upd own t r) rZ m ∧ rZ.Pins W.st.b Sz K ∧ E.Holds (W.xs G) rZ m ∧
      ∀ l, rZ.owned l ≠ none → m.heap l ≠ none := by
  obtain ⟨rF, rO, rfl, hoff, hdFO, hfree, hown⟩ := hu.winv.rest
  obtain ⟨-, hfr, -⟩ := hfree
  have hR : W.R (W.xs G) rF := hfr (not_busy_out hout) (nrd_out hout)
  obtain ⟨⟨-, hws⟩, -⟩ := hu.sub
  have hmc : m.MsgCov := ho.conc.2.2
  have hfut : ∀ e ∈ m.footprint, m.blocks.size ≤ e.block →
      VClock.le e.clock (m.clocks[t]!) = true := fun e he hb => (ho.owns t ht).1 e he (.inr hb)
  have hplain : ∀ {r : Res}, r.gh = Ghost.unit → ∀ l, r.shared l = none :=
    fun h l => (Res.excl_eq_erase (by rw [h]; rfl)).2 l
  have hSE : ∀ l, C.S.In l → ¬ C.Ep.In l := fun l h h' => by
    have h1 : l.2 < C.S.o + 4 := h.2.2
    have h2 : C.Ep.o ≤ l.2 := h'.2.1
    have := C.ep_o
    omega
  -- the condition's words' cells in the rest of the rest
  have hcell : ∀ Wd : Word 32 4, Wd = C.S ∨ Wd = C.Ep → ∀ l, Wd.In l →
      rO.heap l = (m.heap l).map fun c => ⟨c, none⟩ := fun Wd hWd l hl => by
    obtain ⟨-, rY, e, hY⟩ := hws Wd hWd
    have hC : C.S.In l ∨ C.Ep.In l := by
      rcases hWd with rfl | rfl
      · exact .inl hl
      · exact .inr hl
    have h1 : ((W.st.cellsR m).heap ∪ (rF.heap ∪ rO.heap)) l =
        ((Wd.cellsR m).heap ∪ rY.heap) l := congrArg (fun r : Res => r.heap l) e
    simpa only [FHeap.union_apply, cellsAt_none (show ¬ W.st.In l from fun h => hst l h hC),
      hRoff _ _ l hR hC, hY l hl, cellsAt_of hl, Option.none_or, Option.or_none] using h1
  obtain ⟨rZ, eO, hZ, -, -, -⟩ := cellsAt_split (W := fun l => C.S.In l ∨ C.Ep.In l) (m := m)
    (r := rO) fun l h => by
      rw [cellsAt_of h]
      rcases h with h | h
      · exact hcell _ (.inl rfl) l h
      · exact hcell _ (.inr rfl) l h
  rw [cellsAt_or (P := C.S.In) (Q := C.Ep.In), rsum_assoc] at eO
  subst eO
  have hstOk := hu.winv.ok
  obtain ⟨hSok, -⟩ := hws C.S (.inl rfl)
  obtain ⟨hEok, -⟩ := hws C.Ep (.inr rfl)
  -- the pieces are apart
  have hd1 : FHeap.Disjoint (W.st.cellsR m).heap
      (rsum rF (rsum (C.S.cellsR m) (rsum (C.Ep.cellsR m) rZ))).heap := fun l => by
    by_cases hl : W.st.In l
    · exact .inr (rsum_heap_none.mpr ⟨Res.heap_of_owned (hoff l hl).1, (hoff l hl).2⟩)
    · exact .inl (cellsAt_none hl)
  have hd3 : FHeap.Disjoint (C.S.cellsR m).heap (rsum (C.Ep.cellsR m) rZ).heap := fun l => by
    by_cases hl : C.S.In l
    · exact .inr (rsum_heap_none.mpr ⟨cellsAt_none (hSE l hl), hZ l (.inl hl)⟩)
    · exact .inl (cellsAt_none hl)
  have hd4 : FHeap.Disjoint (C.Ep.cellsR m).heap rZ.heap := fun l => by
    by_cases hl : C.Ep.In l
    · exact .inr (hZ l (.inr hl))
    · exact .inl (cellsAt_none hl)
  -- `t` takes the state word, the resource and the condition's words
  obtain ⟨hs1, ho1⟩ := ho.takeOwned (Q := fun r => r = W.st.cellsR m) ht hat hd1
    (hstOk.ownsCells ht hg hall hfut) (fun l => .inr (hplain rfl l)) hP rfl
  obtain ⟨hs2, ho2⟩ := ho1.takeOwned (Q := W.R (W.xs G)) ht (upd_self _ _ _) hdFO
    (hown.owns hstOk hmc ht hg hall fun u hu' => hu.winv.ex u fun h => by
      rw [h] at hu'; cases hu')
    (fun l => .inr (hplain (W.R_plain _ _ hR).2 l)) hs1 hR
  rw [upd_upd] at ho2
  obtain ⟨hs3, ho3⟩ := ho2.takeOwned (Q := fun r => r = C.S.cellsR m) ht (upd_self _ _ _) hd3
    (hSok.ownsCells ht trivial hall hfut) (fun l => .inr (hplain rfl l)) hs2 rfl
  rw [upd_upd] at ho3
  obtain ⟨hs4, ho4⟩ := ho3.takeOwned (Q := fun r => r = C.Ep.cellsR m) ht (upd_self _ _ _) hd4
    (hEok.ownsCells ht trivial hall hfut) (fun l => .inr (hplain rfl l)) hs3 rfl
  rw [upd_upd] at ho4
  simp only [sep_assoc_eq] at hs4
  refine ⟨_, rZ, hs4, ho4, hu.pin.of_gh ?_, ⟨hu.cl.thr, hu.cl.sh, ?_⟩, fun l h => hu.live l ?_⟩
  · show rZ.gh = Ghost.unit.add (rF.gh.add (Ghost.unit.add (Ghost.unit.add rZ.gh)))
    rw [(W.R_plain _ _ hR).2]
    simp only [Ghost.unit_add]
  · obtain ⟨r, hr, hsub⟩ := hu.cl.io
    refine ⟨r, hr, fun l fc hfc => ?_⟩
    have hLk : ¬ W.Lk l := fun hk => by
      have h0 := hIo r l hr hk
      rw [hfc] at h0; cases h0
    have h' : ((W.st.cellsR m).heap ∪ (rF.heap ∪ ((C.S.cellsR m).heap ∪
        ((C.Ep.cellsR m).heap ∪ rZ.heap)))) l = some fc := hsub l fc hfc
    simpa only [FHeap.union_apply,
      cellsAt_none (show ¬ W.st.In l from fun h => hLk (Or.inl h)),
      cellsAt_none (show ¬ C.S.In l from fun h => hLk (Or.inr (Or.inl h))),
      cellsAt_none (show ¬ C.Ep.In l from fun h => hLk (Or.inr (Or.inr (Or.inl h)))),
      (show rF.heap l = none from Classical.byContradiction fun h =>
        hLk (Or.inr (Or.inr (Or.inr ⟨_, _, hR, h⟩)))),
      Option.none_or] using h'
  · exact (Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr (.inr
      ((Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr (.inr h)))))))

end Base

end FRw

namespace RwProd

variable {Xc : Type} {b o : Nat} {R : (ThreadId → Xc) → FAssn}
  {R_plain : ∀ xs r, R xs r → r.know = Know.none ∧ r.gh = Ghost.unit}
  {R_fixed : ∀ xs, (R xs).FixedDom} {E : FClient Xc} {Sz : Nat} {K : BlockKind}

/-- **The end of a program with a reader/writer lock** (module doc; the dual of `RwProd.start`).
The invariant holds, every thread is out of the rwlock's code, no thread holds the outer mutex or
the semaphore's mutex, and thread `t` (not ended at either mutex) has a clock above every
thread's: every other thread has ended and been joined. `R` has no byte of the condition's words
and the read-shared bytes are none of the bytes the lock's code changes (`hRoff`, `hIo`: what
`RwProd.fits` takes).

Then `t`'s new part `r` is its old part, the outer mutex's word's cells, the semaphore's count
(`0`), its mutex's word's cells, the state word's cells, the protected resource (with `R`) and
the cells of the condition's two words, apart from each other. The rest `rZ` pins the lock's
block, holds the program's read-shared bytes (the program's facts hold at it) and its bytes are
live; `t` takes a piece of it with `FOwned.takeOwned` once its clock owns the piece. -/
theorem stop {G : ThreadId → Gh Xc} {rXA : Res} {m : Mem} {t : ThreadId}
    (hi : (M b o).Inv G rXA m)
    (hU : FLock.Pair.U (L b o R) ((W b o R R_plain R_fixed).Base E Sz K) G rXA m)
    (hw : ∀ u, (G u).2.w = .out) (hFA : (M b o).Free G) (hFB : (L b o R).Free G)
    (hgA : (G t).1.phA ≠ .gone) (hgB : (G t).1.phB ≠ .gone)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true)
    (hRoff : ∀ xs r l, R xs r → ((C b o (Xc := Xc)).S.In l ∨ (C b o (Xc := Xc)).Ep.In l) →
      r.heap l = none)
    (hIo : ∀ r l, E.Io r → (W b o R R_plain R_fixed).Lk l → r.heap l = none) :
    ∃ r rZ, ((fun r => r = (M b o).own G m t) ⋆ ((fun r => r = (M b o).wordR m) ⋆
        (up (pts ((p b o).add 8) 8 (0 : BitVec 64)) ⋆ ((fun r => r = (L b o R).wordR m) ⋆
        ((fun r => r = (W b o R R_plain R_fixed).st.cellsR m) ⋆ (R (fun u => (G u).2.x) ⋆
        ((fun r => r = (C b o (Xc := Xc)).S.cellsR m) ⋆
          fun r => r = (C b o (Xc := Xc)).Ep.cellsR m))))))) r ∧
      FOwned (upd ((M b o).own G m) t r) rZ m ∧ rZ.Pins b Sz K ∧
      E.Holds (fun u => (G u).2.x) rZ m ∧ ∀ l, rZ.owned l ≠ none → m.heap l ≠ none := by
  obtain ⟨sB, rLB, rHB, rX, rfl, hs, hk, hb⟩ := hU
  obtain ⟨ht, -⟩ := hi.ht hgA
  -- the resource is not posted: the count is `0` and the pool is empty
  have hnp : ¬ RwPosted Prod.fst (fun u => sx (G u).2) := fun ⟨⟨u, hu⟩, _⟩ => by
    have h : (G u).2.w = .ww := hu
    rw [hw u] at h; cases h
  have hcnt : ∀ r, (L b o R).R G r → up (pts ((p b o).add 8) 8 (0 : BitVec 64)) r :=
    fun r h => by
      have h' : (up (pts ((p b o).add 8) 8 (pv fun u => sx (G u).2)) ⋆
          Pool R fun u => sx (G u).2) r := h
      rw [show pv (fun u => sx (G u).2) = 0 by unfold pv; exact if_neg hnp,
        show Pool R (fun u => sx (G u).2) = emp by unfold Pool; exact if_neg hnp] at h'
      exact sep_emp.mp h'
  have hplain : ∀ {r : Res}, r.gh = Ghost.unit → ∀ l, r.shared l = none :=
    fun h l => (Res.excl_eq_erase (by rw [h]; rfl)).2 l
  have hemp : ∀ r, (M b o).R G r → ∀ l, r.shared l = none := fun r h l => by
    have h' : emp r := h
    exact hplain h'.2.2 l
  -- the two locks
  obtain ⟨r0, hs0, ho0⟩ := FLock.Pair.stop hi hs hk hFA hFB hgA hgB hall
    (fun rL hR l => .inr (hemp rL hR l))
    (fun rB hR l => .inr (hplain (hcnt rB hR).2.2 l))
    (fun rA _ hA _ l => .inl (hemp rA hA l))
  have hs0' : ((fun r => r = (M b o).own G m t) ⋆ ((fun r => r = (M b o).wordR m) ⋆
      (up (pts ((p b o).add 8) 8 (0 : BitVec 64)) ⋆ fun r => r = (L b o R).wordR m))) r0 :=
    sep_mono_right (fun _ h => sep_mono_right (fun _ h2 => sep_mono_left
      (fun r hr => hcnt r hr) h2) (sep_emp.mp (sep_comm h))) hs0
  -- the base
  obtain ⟨r, rZ, hsr, hor, hpin, hcl, hlive⟩ := FRw.Base.stop hb ho0 ht (upd_self _ _ _) hs0' hw
    hgA hall
    (fun l h hC => by
      have h1 : l.2 < o + 8 := h.2.2
      rcases hC with h' | h'
      · have h2 : o + 20 ≤ l.2 := h'.2.1
        omega
      · have h2 : o + 24 ≤ l.2 := h'.2.1
        omega)
    hRoff hIo
  rw [upd_upd] at hor
  simp only [sep_assoc_eq] at hsr
  exact ⟨r, rZ, hsr, hor, hpin, hcl, hlive⟩

end RwProd

end Full
end Zig
