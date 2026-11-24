import ZigLean.Sep.Full.RwLockGhost
import ZigLean.Sep.Full.RwLockStart

/-!
# The start of a program with a reader/writer lock

(ledger #two-lock-product, item (5).) A program whose invariant is the two-lock product at the
reader/writer lock's base (`RwProd.fits`, `ZigLean/Sep/Full/RwLockGhost.lean`) starts with one
thread that owns the lock's bytes and gives them to the rest. This file proves the invariant
there once for every program: the two-lock pair's start (`FLock.Pair.start`) and the base at a
fresh lock (`FRw.Base.start`).

- `RwProd.start`: thread `t`, whose clock is above every thread's, has in its part the outer
  mutex's word, the semaphore's count (`0`) and its mutex's word, the state word and the
  condition's two words (`rYw`), the protected resource `rR` and the rest of the program's rest
  `rI` (a pin of the lock's block, the bytes every thread reads). The five words hold `0` (the
  epoch any value), no atomic location is in the lock's block, no thread waits at a futex, and
  every thread is out of every code (and alive) or ended. Then the invariant holds.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

namespace RwProd

variable {Xc : Type} {b o : Nat} {R : (ThreadId → Xc) → FAssn}
  {R_plain : ∀ xs r, R xs r → r.know = Know.none ∧ r.gh = Ghost.unit}
  {R_fixed : ∀ xs, (R xs).FixedDom} {E : FClient Xc} {Sz : Nat} {K : BlockKind}

private theorem heap_l {a c : Res} {l : Zig.Loc} (h : a.heap l ≠ none) :
    (rsum a c).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro h'; exact absurd h' h

private theorem heap_r {a c : Res} {l : Zig.Loc} (h : c.heap l ≠ none) :
    (rsum a c).heap l ≠ none := by
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro _; exact h

/-- **The start of a program with a reader/writer lock** (module doc). -/
theorem start {own : ThreadId → Res} {rO rWM rCnt rWL rYw rR rI : Res} {G : ThreadId → Gh Xc}
    {m : Mem} {t : ThreadId} {e0 : BitVec 32}
    (ho : FOwned own rO m) (hjt : joinedB m t = false) (ht : t < m.threads.size)
    (hown : ∀ u, u ≠ t → (M b o).own G m u = own u)
    (hsplit : own t = rsum (G t).1.part
      (rsum (rsum rnil rWM) (rsum (rsum rCnt rWL) (rsum rYw (rsum rR rI)))))
    (hdP : FHeap.Disjoint (G t).1.part.heap
      (rsum (rsum rnil rWM) (rsum (rsum rCnt rWL) (rsum rYw (rsum rR rI)))).heap)
    (hdAB : FHeap.Disjoint (rsum rnil rWM).heap
      (rsum (rsum rCnt rWL) (rsum rYw (rsum rR rI))).heap)
    (hdB : FHeap.Disjoint rCnt.heap rWL.heap)
    (hdBY : FHeap.Disjoint (rsum rCnt rWL).heap (rsum rYw (rsum rR rI)).heap)
    (hdY : FHeap.Disjoint rYw.heap (rsum rR rI).heap)
    (hdRI : FHeap.Disjoint rR.heap rI.heap)
    (hWM : ∀ l, rWM.heap l ≠ none ↔ (M b o (Xc := Xc)).In l) (hWMk : rWM.know = Know.none)
    (hWMg : rWM.gh = Ghost.unit)
    (hWL : ∀ l, rWL.heap l ≠ none ↔ (L b o R).In l) (hWLk : rWL.know = Know.none)
    (hWLg : rWL.gh = Ghost.unit)
    (hYw : ∀ l, rYw.heap l ≠ none ↔ ((W b o R R_plain R_fixed).st.In l ∨
      ((C b o (Xc := Xc)).S.In l ∨ (C b o (Xc := Xc)).Ep.In l)))
    (hYwk : rYw.know = Know.none) (hYwg : rYw.gh = Ghost.unit)
    (hCnt : up (pts ((p b o).add 8) 8 (0 : BitVec 64)) rCnt)
    (hR : R (fun u => (G u).2.x) rR) (hpin : rI.Pins b Sz K)
    (hG : ∀ u, (G u).2.w = .out ∧ (G u).2.c = .out ∧ (G u).2.sp = .out ∧
      (G u).1.heldA = rnil ∧ (G u).1.heldB = rnil)
    (hphA : ∀ u, ((G u).1.phA = .out ∧ u < m.threads.size ∧ joinedB m u = false) ∨
      (G u).1.phA = .gone)
    (hphB : ∀ u, ((G u).1.phB = .out ∧ u < m.threads.size ∧ joinedB m u = false) ∨
      (G u).1.phB = .gone)
    (hblk : ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ o + 40 ≤ blk.bytes.size ∧
      (blk.addr + o) % 8 = 0 ∧ blk.kind ≠ .constGlobal ∧ blk.kind.mappedLo ≤ o)
    (hat : ∀ l ∈ m.atomics, l.block ≠ b) (hq : m.waiters = #[])
    (hst : (W b o R R_plain R_fixed).st.Holds m (RwState.encode 0 0 false))
    (hS0 : (C b o (Xc := Xc)).S.Holds m 0) (hE0 : (C b o (Xc := Xc)).Ep.Holds m e0)
    (hM0 : (M b o (Xc := Xc)).U32 m 0) (hL0 : (L b o R).U32 m 0)
    (hall : AllLe m (m.clocks[t]!))
    (hthr : E.T (fun u => (G u).2.x) m.threads)
    (hio : ∃ r, E.Io r ∧ ∀ l fc, r.heap l = some fc → rI.heap l = some fc) :
    ∃ rX, (M b o).Inv G rX m ∧
      FLock.Pair.U (L b o R) ((W b o R R_plain R_fixed).Base E Sz K) G rX m := by
  obtain ⟨blk, hb, hlv, hsz, hal, hkd, hlo⟩ := hblk
  -- the two-lock pair
  have hnp : ¬ RwPosted Prod.fst (fun u => sx (G u).2) := fun ⟨⟨u, hu⟩, _⟩ => by
    have h : (G u).2.w = .ww := hu
    rw [(hG u).1] at h; cases h
  have hRB : (L b o R).R G rCnt := by
    show (up (pts ((p b o).add 8) 8 (pv fun u => sx (G u).2)) ⋆ Pool R fun u => sx (G u).2) rCnt
    rw [show pv (fun u => sx (G u).2) = 0 by unfold pv; exact if_neg hnp,
      show Pool R (fun u => sx (G u).2) = emp by unfold Pool; exact if_neg hnp]
    exact sep_emp.mpr hCnt
  obtain ⟨hi, hk⟩ := FLock.Pair.start (A := M b o) (B := L b o R) (G := G) (rLA := rnil)
    (rY := rsum rR rI) ho hjt ht hown hsplit hdP (fun _ => .inl rfl) hdAB hdB hdBY hdY hYw hYwk
    hYwg hWM hWMk hWMg hWL hWLk hWLg hphA hphB (fun u => (hG u).2.2.2.1) (fun u => (hG u).2.2.2.2)
    ⟨rfl, rfl, rfl⟩ hRB
    ⟨blk, hb, hlv, by show o + 32 + 4 ≤ _; omega, by show (blk.addr + (o + 32)) % 4 = 0; omega,
      hkd, by show _ ≤ o + 32; omega⟩ hM0
    ⟨blk, hb, hlv, by show o + 16 + 4 ≤ _; omega, by show (blk.addr + (o + 16)) % 4 = 0; omega,
      hkd, by show _ ≤ o + 16; omega⟩ hL0
    (fun l hl => ⟨hat l hl, hat l hl⟩) hq hall
  -- `t` owns the pieces of its part: an access to them happened before every thread
  have hown0 : ∀ e ∈ m.footprint, (e.Touches (own t).excl ∨ m.blocks.size ≤ e.block) →
      AllLe m e.clock := fun e he htc u hu =>
    VClock.le_trans ((ho.owns t ht).1 e he htc) (hall u hu)
  have hYwT : ∀ l, rYw.heap l ≠ none → (own t).heap l ≠ none := fun l h => by
    rw [hsplit]; exact heap_r (heap_r (heap_r (heap_l h)))
  have hRT : ∀ l, rR.heap l ≠ none → (own t).heap l ≠ none := fun l h => by
    rw [hsplit]; exact heap_r (heap_r (heap_r (heap_r (heap_l h))))
  have hIT : ∀ l, rI.heap l ≠ none → (own t).heap l ≠ none := fun l h => by
    rw [hsplit]; exact heap_r (heap_r (heap_r (heap_r (heap_r h))))
  have hOoff : ∀ {r : Res}, (∀ l, r.heap l ≠ none → (own t).heap l ≠ none) →
      FHeap.Disjoint r.heap rO.heap := fun h l => by
    cases e : rO.heap l with
    | none => exact .inr rfl
    | some _ => exact .inl (Classical.byContradiction fun hn =>
        h l hn (ho.part_off ht (by rw [e]; simp)))
  have hdY' := FHeap.disjoint_union_right.mp hdY
  -- the bytes of the lock's three words in the protocol's rest are apart from the rest of it
  have hWoff : ∀ l, rYw.heap l ≠ none → rR.heap l = none ∧ rI.heap l = none ∧ rO.heap l = none :=
    fun l h => ⟨(hdY'.1 l).resolve_left h, (hdY'.2 l).resolve_left h,
      (hOoff hYwT l).resolve_left h⟩
  have hcell : ∀ (Q : Zig.Loc → Prop) [DecidablePred Q] (r : Res),
      (∀ l, Q l → r.heap l = none) → FHeap.Disjoint (cellsAt Q m).heap r.heap := fun Q _ r h l => by
    by_cases hl : Q l
    · exact .inr (h l hl)
    · exact .inl (cellsAt_none hl)
  have hSin : ∀ l, (C b o (Xc := Xc)).S.In l → rYw.heap l ≠ none := fun l h =>
    (hYw l).mpr (.inr (.inl h))
  have hEin : ∀ l, (C b o (Xc := Xc)).Ep.In l → rYw.heap l ≠ none := fun l h =>
    (hYw l).mpr (.inr (.inr h))
  have hstin : ∀ l, (W b o R R_plain R_fixed).st.In l → rYw.heap l ≠ none := fun l h =>
    (hYw l).mpr (.inl h)
  have hSE : ∀ l, (C b o (Xc := Xc)).S.In l → ¬ (C b o (Xc := Xc)).Ep.In l := fun l h h' => by
    have h1 : l.2 < o + 20 + 4 := h.2.2
    have h2 : o + 24 ≤ l.2 := h'.2.1
    omega
  have hstS : ∀ l, (W b o R R_plain R_fixed).st.In l → ¬ (C b o (Xc := Xc)).S.In l :=
    fun l h h' => by
      have h1 : l.2 < o + 8 := h.2.2
      have h2 : o + 20 ≤ l.2 := h'.2.1
      omega
  have hstE : ∀ l, (W b o R R_plain R_fixed).st.In l → ¬ (C b o (Xc := Xc)).Ep.In l :=
    fun l h h' => by
      have h1 : l.2 < o + 8 := h.2.2
      have h2 : o + 24 ≤ l.2 := h'.2.1
      omega
  -- the protocol's rest as the base reads it
  have eX : rsum (cellsAt (fun l => (W b o R R_plain R_fixed).st.In l ∨
        ((C b o (Xc := Xc)).S.In l ∨ (C b o (Xc := Xc)).Ep.In l)) m) (rsum (rsum rR rI) rO) =
      rsum ((W b o R R_plain R_fixed).st.cellsR m) (rsum rR
        (rsum ((C b o (Xc := Xc)).S.cellsR m) (rsum ((C b o (Xc := Xc)).Ep.cellsR m)
          (rsum rI rO)))) := by
    rw [cellsAt_or (P := (W b o R R_plain R_fixed).st.In), cellsAt_or (P := (C b o (Xc := Xc)).S.In)]
    simp only [rsum_assoc]
    rw [rsum_left_comm (hcell _ rR fun l h => (hWoff l (hEin l h)).1),
      rsum_left_comm (hcell _ rR fun l h => (hWoff l (hSin l h)).1)]
  rw [eX] at hi hk
  -- the three words at the start
  have htouch : ∀ {n nb : Nat} (V : Word n nb), (∀ l, V.In l → rYw.heap l ≠ none) →
      ∀ e ∈ m.footprint, V.Hits e → AllLe m e.clock := fun V hV e he hh =>
    hown0 e he (.inl (Word.touches_of hh fun x h1 h2 =>
      Res.excl_of_heap (hYwT _ (hV (V.b, x) ⟨rfl, h1, h2⟩))))
  have hat' : ∀ {n nb : Nat} (V : Word n nb), V.b = b → ∀ l ∈ m.atomics, l.block = V.b →
      V.o + nb ≤ l.off ∨ (l.off < V.o ∧ l.off + l.len ≤ V.o) := fun V hV l hl hb' =>
    absurd (hb'.trans hV) (hat l hl)
  obtain ⟨hstOk, hst1, hstV, -⟩ := Word.Ok.init (W := (W b o R R_plain R_fixed).st)
    (A := fun u => (M b o).ph (G u) ≠ .gone)
    ⟨blk, hb, hlv, by show o + 8 ≤ _; omega, hal, hkd, hlo⟩
    (hat' _ rfl) hst fun e he hh => (htouch _ hstin e he hh).on _
  obtain ⟨hSOk, hS1, hSV, -⟩ := Word.Ok.init (W := (C b o (Xc := Xc)).S) (A := fun _ => True)
    ⟨blk, hb, hlv, by show o + 20 + 4 ≤ _; omega, by show (blk.addr + (o + 20)) % 4 = 0; omega,
      hkd, by show _ ≤ o + 20; omega⟩
    (hat' _ rfl) hS0 fun e he hh => (htouch _ hSin e he hh).on _
  obtain ⟨hEOk, hE1, hEV, hEc⟩ := Word.Ok.init (W := (C b o (Xc := Xc)).Ep) (A := fun _ => True)
    ⟨blk, hb, hlv, by show o + 24 + 4 ≤ _; omega, by show (blk.addr + (o + 24)) % 4 = 0; omega,
      hkd, by show _ ≤ o + 24; omega⟩
    (hat' _ rfl) hE0 fun e he hh => (htouch _ hEin e he hh).on _
  -- the rest of the rest
  have hRO : FHeap.Disjoint rR.heap rO.heap := hOoff hRT
  have hIO : FHeap.Disjoint rI.heap rO.heap := hOoff hIT
  have hlive := fun {l : Zig.Loc} => hi.rest_live (l := l)
  obtain ⟨r, hr, hsub⟩ := hio
  have hbase := FRw.Base.start (W := W b o R R_plain R_fixed) (E := E) (Sz := Sz) (K := K) (G := G)
    (rF := rR) (rO := rsum ((C b o (Xc := Xc)).S.cellsR m)
      (rsum ((C b o (Xc := Xc)).Ep.cellsR m) (rsum rI rO))) (e0 := e0)
    (fun u => (hG u).1) (fun u => (hG u).2.1) (fun u => (hG u).2.2.1)
    (fun u => (hphA u).imp (·.1) id) (fun u => (hphB u).imp (·.1) id)
    hstOk hst1 hstV hSOk hS1 hSV hEOk hE1 hEV (fun u _ => hEc _) hq hR
    (FRw.Owns.of_allLe fun e he htc => by
      rcases htc with ⟨x, h1, h2, h3⟩ | ⟨x, h1, h2, h3⟩ | hbe
      · exact hown0 e he (.inl ⟨x, h1, h2, by
          rw [hsplit]
          exact Res.excl_sep rfl rfl (.inr (Res.excl_sep rfl rfl (.inr (Res.excl_sep rfl rfl
            (.inr (Res.excl_sep rfl rfl (.inr (Res.excl_sep rfl rfl (.inl h3)))))))))⟩)
      · exact absurd (Res.shared_ne.mp h3).2.2 (by
          rw [(R_plain _ _ hR).2]; exact SCell.not_pos_iff.mpr SCell.empty_zero)
      · exact hown0 e he (.inr hbe))
    (fun l h => ⟨(hWoff l (hstin l h)).1, by
      show (((C b o (Xc := Xc)).S.cellsR m).heap ∪ (((C b o (Xc := Xc)).Ep.cellsR m).heap ∪
        (rI.heap ∪ rO.heap))) l = none
      rw [FHeap.union_apply, FHeap.union_apply, FHeap.union_apply, cellsAt_none (hstS l h),
        cellsAt_none (hstE l h), (hWoff l (hstin l h)).2.1, (hWoff l (hstin l h)).2.2]; rfl⟩)
    (FHeap.disjoint_union_right.mpr ⟨(hcell _ rR fun l h => (hWoff l (hSin l h)).1).symm,
      FHeap.disjoint_union_right.mpr ⟨(hcell _ rR fun l h => (hWoff l (hEin l h)).1).symm,
        FHeap.disjoint_union_right.mpr ⟨hdRI, hRO⟩⟩⟩)
    (fun V hV => by
      rcases hV with rfl | rfl
      · refine ⟨_, rfl, fun l h => ?_⟩
        show (((C b o (Xc := Xc)).Ep.cellsR m).heap ∪ (rI.heap ∪ rO.heap)) l = none
        rw [FHeap.union_apply, FHeap.union_apply, cellsAt_none (hSE l h),
          (hWoff l (hSin l h)).2.1, (hWoff l (hSin l h)).2.2]; rfl
      · refine ⟨rsum ((C b o (Xc := Xc)).S.cellsR m) (rsum rI rO),
          rsum_left_comm (hcell _ _ fun l h => cellsAt_none fun h' => hSE l h h'), fun l h => ?_⟩
        show (((C b o (Xc := Xc)).S.cellsR m).heap ∪ (rI.heap ∪ rO.heap)) l = none
        rw [FHeap.union_apply, FHeap.union_apply, cellsAt_none (fun h' => hSE l h' h),
          (hWoff l (hEin l h)).2.1, (hWoff l (hEin l h)).2.2]; rfl)
    (Res.Pins.right (Res.Pins.right (Res.Pins.left hpin)))
    hthr
    (fun e he hRg => .inr (by
      obtain ⟨x, h1, h2, h3⟩ := E.touch r e hr hRg
      obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp h3
      exact hown0 e he (.inl ⟨x, h1, h2, Res.excl_of_heap (hIT _ (by rw [hsub _ _ hfc]; nofun))⟩)))
    ⟨r, hr, fun l fc hfc => by
      have hI := hsub l fc hfc
      have hIn : rI.heap l ≠ none := by rw [hI]; nofun
      have hnS : ¬ (C b o (Xc := Xc)).S.In l := fun h => hIn (hWoff l (hSin l h)).2.1
      have hnE : ¬ (C b o (Xc := Xc)).Ep.In l := fun h => hIn (hWoff l (hEin l h)).2.1
      show (((C b o (Xc := Xc)).S.cellsR m).heap ∪ (((C b o (Xc := Xc)).Ep.cellsR m).heap ∪
        (rI.heap ∪ rO.heap))) l = some fc
      rw [FHeap.union_apply, FHeap.union_apply, FHeap.union_apply, cellsAt_none hnS,
        cellsAt_none hnE, hI]; rfl⟩
    (fun l h => hlive ((Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr
      (.inr ((Res.owned_sep rfl rfl).mpr (.inl h)))))))
    (fun l h => hlive ((Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr
      (.inr ((Res.owned_sep rfl rfl).mpr (.inr h)))))))
  exact ⟨_, hi, _, rCnt, rnil, _, rfl, Res.Sim.refl _, hk, hbase⟩

end RwProd

end Full
end Zig
