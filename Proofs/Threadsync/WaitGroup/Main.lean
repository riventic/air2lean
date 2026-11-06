import Proofs.Threadsync.WaitGroup.Start
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.WordNewest

/-!
# `main`'s steps in `waitGroup`'s protocol

Once for every version: `main`'s RMWs at the group's state (`startMany`'s `add(4)` and the wait's
`add(1)`, `U_mainRmw`) and its spawns. Its event wait is in `Wait`, its read of the whole `Tally`
in `Read` and its joins in `Join`.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Threadsync.WG

/-! ## A step at the group's state -/


/-- `main` never finishes. -/
theorem fd0 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m) : (G 0).2.ph.fd = false := by
  have h : (G 0).2.ph.isMain = true := hu.shape.2.1
  generalize (G 0).2.ph = p at h ⊢
  cases p <;> first | rfl | exact absurd h (by decide)

/-- A setter is a task. -/
theorem sx_ne0 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m) {u : ThreadId}
    (h : (G u).2.sx = true) : u ≠ 0 := by
  rcases (hu.sto u h).1 with rfl | rfl <;> decide

/-- The rest's other cells of the `Tally` below the mutex, next to the group's state's. -/
theorem rY_cell {G : ThreadId → Gh} {rY : Res} {m : Mem} (hu : U G (rsum (WG.cellsR m) rY) m)
    {l : Zig.Loc} (hb : BoxW l) (hw : ¬ WG.In l) : rY.heap l ≠ none := by
  obtain ⟨rB, -, -, hrX⟩ := hu.rest
  have := congrFun (congrArg Res.heap hrX) l
  simp only [FHeap.union_apply] at this
  rw [cellsAt_none hw, Option.none_or, cellsAt_of hb] at this
  rw [this]
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (box_live hu hb)
  simp [hc]

/-- **After a step whose rest has the group's state's new cells** (`hL`, the lock's invariant
after it), block 0 is the `Tally` and the other bytes of the two words and the padding stay. -/
theorem rest_cellsWG {G G' : ThreadId → Gh} {rY : Res} {m m' : Mem}
    (hu : U G (rsum (WG.cellsR m) rY) m) (hL : L.Inv G' (rsum (WG.cellsR m') rY) m') :
    BlkOk m' ∧ ∀ l, BoxW l → ¬ WG.In l → m'.heap l = m.heap l := by
  obtain ⟨rB, hB, hBoff, hrX⟩ := hu.rest
  have hg : rY.gh = rB.gh := by
    have := congrArg Res.gh hrX; simpa [cellsAt, Word.cellsR] using this
  have hbk' := blk_of hL hB hg
  refine ⟨hbk', ?_⟩
  rintro ⟨b, x⟩ ⟨h0, h1⟩ hw
  simp only at h0 h1; subst h0
  refine cell_eq hu.blk hbk' hL (by omega) ?_
  have := congrFun (congrArg Res.heap hrX) (0, x)
  simp only [FHeap.union_apply] at this ⊢
  rw [cellsAt_none hw, Option.none_or] at this ⊢
  rw [this, cellsAt_of (W := BoxW) ⟨rfl, h1⟩, hBoff _ ⟨rfl, h1⟩, Option.or_none]

/-- The counter does not read `main`'s place. -/
theorem R_upd0 {G : ThreadId → Gh} {g : Gh} {r : Res} (h : L.R G r) : L.R (upd G 0 g) r := by
  show up (pts (bPtr.add 20) 4 (BitVec.ofNat 32 ((upd G 0 g 1).2.cnt + (upd G 0 g 2).2.cnt))) r
  rw [upd_ne _ _ (by decide : (1 : ThreadId) ≠ 0), upd_ne _ _ (by decide : (2 : ThreadId) ≠ 0)]
  exact h

/-- **`main`'s RMW at the group's state** (not a release: `startMany`'s `add(4)`, the wait's
`add(1)`) keeps `U` with `main`'s next place `x₁`, given the fields that read it: the group's new
value, `last3` and `done`. The event's word and the other bytes stay (`rest_cellsWG`), the write
continues the release sequence (`gw`), and its access is `main`'s (`attr`). -/
theorem U_mainRmw {G : ThreadId → Gh} {rY : Res} {m m' : Mem} {x₁ : X} {ord : AtomicOrder}
    {new : BitVec 64} (hu : U G (rsum (WG.cellsR m) rY) m) (hY : ∀ l, WG.In l → rY.heap l = none)
    (hc : m.current = 0)
    (hhW : WG.hist m' = (WG.hist m).push (Word.rmwEnt m' 0 ord (newest WG m) new))
    (hrel : ord.isRel = false) (hH : WG.Holds m' (BitVec.ofNat 64 (wgv x₁ (G 1).2 (G 2).2)))
    (hw' : WG.Ok m' (fun u => WLive (G u)))
    (hA : ∀ hF : Heap, (∀ x, WG.o ≤ x → x < WG.o + 8 → hF (WG.b, x) = none) → FStepIn hF m m')
    (hL : L.Inv G (rsum (WG.cellsR m') rY) m')
    (he₀ : (G 0).2.e = .out) (he₁ : x₁.e = .out) (hsx₁ : x₁.sx = false) (hfd₁ : x₁.ph.fd = false)
    (hwx : (G 0).2.ph.wa = true → x₁.ph.wa = true)
    (hwxk : (G 0).2.wk = true → x₁.wk = true) (hwk₁ : x₁.wk = true → x₁.ph.wa = true)
    (hsh : Shape (fun u => (upd G 0 ((G 0).1, x₁) u).2) m)
    (hlast3 : x₁.wk = true → (G 1).2.ph.fd = true → (G 2).2.ph.fd = true →
      ∃ u, (G u).2.sx = true)
    (hdone : 6 ≤ x₁.ph.rank → (G 1).2.ph.fd = true ∧ (G 2).2.ph.fd = true ∧
      VClock.le (G 1).2.fc (m'.clocks[0]!) = true ∧ VClock.le (G 2).2.fc (m'.clocks[0]!) = true ∧
      (∀ j < (EV.hist m).size, IsSetW m j →
        VClock.le (EV.hist m)[j]!.clock (m'.clocks[0]!) = true) ∧
      ∀ u, (G u).2.sx = true → (G u).2.e.Setting ∨ (G u).2.ph = .fin) :
    U (upd G 0 ((G 0).1, x₁)) (rsum (WG.cellsR m') rY) m' := by
  have hX0 : (upd G 0 ((G 0).1, x₁) 0).2 = x₁ := by rw [upd_self]
  have hX : ∀ u, u ≠ 0 → upd G 0 ((G 0).1, x₁) u = G u := fun u h => upd_ne _ _ h
  have h10 : (1 : ThreadId) ≠ 0 := by decide
  have h20 : (2 : ThreadId) ≠ 0 := by decide
  obtain ⟨hbk', hcs⟩ := rest_cellsWG hu hL
  have hs : FStepIn rY.heap.erase m m' := hA _ fun x h1 h2 => by
    simp [FHeap.erase, hY (WG.b, x) ⟨rfl, h1, h2⟩]
  have hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    by_cases e : u = m.current
    · rw [e]; exact hs.mine
    · rw [hs.others u e]; exact VClock.le_refl _
  have hcovE : ∀ l, EV.In l → rY.heap.erase l ≠ none := fun l hl =>
    erase_ne (rY_cell hu (ev_box hl) fun hw => wg_ev hw hl)
  have hnE : ∀ l, EV.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm :=
    fun l hl => by rw [hcs l (ev_box hl) fun hw => wg_ev hw hl]
  have hwE := hu.ev.fstep hs hcovE hnE
  have hhE := Word.hist_fstep hu.ev hs hcovE hnE
  have hfr := hu.einv.fresh.fstep hs (fun x h1 h2 => hcovE _ ⟨rfl, h1, h2⟩)
    (fun i l hl => (hu.ev.loc i l hl).1)
  have hmain := fd0 hu
  have hkE : EV.key m' = EV.key m := hu.ev.key_of_addrs hs.addrs
  obtain ⟨blk₀, hb₀, -⟩ := hu.blk
  have hkL : L.key m' = L.key m := L.key_of_addrs hs.addrs hb₀
  have hI : E.Inv L (upd G 0 ((G 0).1, x₁)) m' :=
    hu.einv.frame (t := 0) (fun u hu => upd_ne _ _ hu)
      (by rw [upd_self]; exact he₁.trans he₀.symm) (by rw [upd_self]; rfl) hhE hs.waiters hclk
      (Nat.le_of_eq (by rw [hs.threads])) (fun h => by rw [upd_self]; exact hwxk h)
      (fun h => absurd hmain (by rw [h.2]; decide)) hfr hkE hkL
  have hnew : ∀ e ∈ m'.footprint, e.block = 0 → e.kind.isWrite = true →
      (∃ e₀ ∈ m.footprint, e.Narrows e₀) ∨
      (∃ u, u < 3 ∧ (G u).2.ph.fd = false ∧ VClock.le e.clock (m'.clocks[u]!) = true) :=
    fun e he _ _ => (hs.fpc e he).imp_right fun hle => ⟨0, by decide, hmain, by rw [← hc]; exact hle⟩
  have hattr := attr_step hu (G' := G) (fun _ => rfl) hclk hhE hnew
  have hbnd : ∀ u, (u = 1 ∨ u = 2) → bnd (upd G 0 ((G 0).1, x₁)) m' u = bnd G m' u := by
    rintro u (rfl | rfl) <;> unfold bnd <;> rw [hX _ (by decide)]
  refine ⟨Shape.congr hsh hs.threads (fun _ => rfl) (fun _ h => h), Rest.step (fun _ => wg_box)
    hu.rest rfl hY hcs, hbk', hw'.anti fun u h => ?_, hwE.anti fun u h => ?_, hI, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun w hw => by rw [hkL, hkE]; exact hu.q w (by rw [← hs.waiters]; exact hw)⟩
  · by_cases e : u = 0
    · subst e; exact hmain
    · rwa [hX u e] at h
  · by_cases e : u = 0
    · subst e; exact .inl hmain
    · rwa [hX u e] at h
  · -- gv
    show (newest WG m').Val _
    rw [hX0, hX 1 h10, hX 2 h20, ← hw'.holds_last]; exact hH
  · -- gw
    intro u h
    rw [newest_push hhW]
    simp only [Word.rmwEnt, hrel, Bool.false_eq_true, ↓reduceIte]
    by_cases e : u = 0
    · subst e; rw [hX0, hfd₁] at h; cases h
    · rw [hX u e] at h ⊢; exact hu.gw u h
  · -- sto
    intro u h
    have e : u ≠ 0 := by
      intro e; subst e; rw [hX0, hsx₁] at h; cases h
    rw [hX u e] at h ⊢
    obtain ⟨a, b, c, d, f⟩ := hu.sto u h
    refine ⟨a, by rw [hX0]; exact hwx b, by rw [hX 1 h10]; exact c, by rw [hX 2 h20]; exact d,
      fun hs ho => ?_⟩
    rw [hX 1 h10, hX 2 h20]
    obtain ⟨x, y⟩ := f hs ho
    exact ⟨VClock.le_trans x (hclk u), VClock.le_trans y (hclk u)⟩
  · -- last3
    intro h0 h1 h2
    rw [hX0] at h0; rw [hX 1 h10] at h1; rw [hX 2 h20] at h2
    obtain ⟨u, hu'⟩ := hlast3 h0 h1 h2
    exact ⟨u, by rw [hX u (sx_ne0 hu hu')]; exact hu'⟩
  · -- isw
    intro j hj hsj
    unfold IsSetW at hsj; rw [hhE] at hj hsj ⊢; rw [hX 1 h10, hX 2 h20]
    obtain ⟨⟨u, h1, h2⟩, h3, h4⟩ := hu.isw j hj hsj
    exact ⟨⟨u, by rw [hX u (sx_ne0 hu h1)]; exact h1, by rw [hX u (sx_ne0 hu h1)]; exact h2⟩, h3, h4⟩
  · -- one
    intro i hi j hj h1 h2; unfold IsSetW at h1 h2; rw [hhE] at hi hj h1 h2
    exact hu.one i hi j hj h1 h2
  · -- sfin
    intro u h1 h2
    have e : u ≠ 0 := by
      intro e; subst e; rw [hX0, hsx₁] at h1; cases h1
    rw [hX u e] at h1 h2
    exact E.IsSet_of_hist_eq hhE (hu.sfin u h1 h2)
  · -- lg
    intro u h
    by_cases e : u = 0
    · subst e; rw [hX0, hfd₁] at h; cases h
    · rw [hX u e] at h ⊢; exact hu.lg u h
  · -- out3
    intro u h3
    rw [hX u (by unfold ThreadId at *; omega)]; exact hu.out3 u h3
  · -- wa0
    intro u h
    by_cases e : u = 0
    · exact e
    · rw [hX u e] at h; exact hu.wa0 u h
  · -- wk0
    intro u h
    by_cases e : u = 0
    · subst e; rw [hX0] at h ⊢; exact ⟨rfl, hwk₁ h⟩
    · rw [hX u e] at h ⊢; exact hu.wk0 u h
  · -- sx1
    intro u v h1 h2
    have e1 : u ≠ 0 := by
      intro e; subst e; rw [hX0, hsx₁] at h1; cases h1
    have e2 : v ≠ 0 := by
      intro e; subst e; rw [hX0, hsx₁] at h2; cases h2
    rw [hX u e1] at h1; rw [hX v e2] at h2; exact hu.sx1 u v h1 h2
  · -- attr
    intro e he hb hk hl ho
    rcases hattr e he hb hk hl ho with h | ⟨u, hu12, h⟩ | h
    · exact .inl h
    · exact .inr (.inl ⟨u, hu12, by rw [hbnd u hu12]; exact h⟩)
    · exact .inr (.inr h)
  · -- done
    intro h
    rw [hX0] at h
    obtain ⟨a, b, c, d, f, k⟩ := hdone h
    refine ⟨by rw [hX 1 h10]; exact a, by rw [hX 2 h20]; exact b, by rw [hX 1 h10]; exact c,
      by rw [hX 2 h20]; exact d, fun j hj hsj => ?_, fun u hx => ?_⟩
    · unfold IsSetW at hsj; rw [hhE] at hj hsj ⊢; exact f j hj hsj
    · have e : u ≠ 0 := by
        intro e; subst e; rw [hX0, hsx₁] at hx; cases hx
      rw [hX u e] at hx ⊢; exact k u hx

/-- **`main`'s next place** `g` keeps the threads' shape: at the same stage of the spawns, and
joined (task 1) exactly at `j1`. -/
theorem shape_main {G : ThreadId → Gh} {m : Mem} {g : Gh} (h : Shape (fun u => (G u).2) m)
    (hm : g.2.ph.isMain = true) (h1 : (G 0).2.ph.rank ≤ 1 → g.2.ph.rank ≤ 1)
    (h2 : (G 0).2.ph = .sp1 → g.2.ph = .sp1)
    (h3 : 3 ≤ (G 0).2.ph.rank → 3 ≤ g.2.ph.rank ∧ ((G 0).2.ph = .j1 ↔ g.2.ph = .j1)) :
    Shape (fun u => (upd G 0 g u).2) m := by
  obtain ⟨h00, -, hn, hc⟩ := h
  have hX : ∀ u, u ≠ 0 → upd G 0 g u = G u := fun u h => upd_ne _ _ h
  refine ⟨h00, by dsimp only; rw [upd_self]; exact hm, fun u hu => ?_, ?_⟩
  · dsimp only; rw [hX u (by unfold ThreadId at *; omega)]; exact hn u hu
  dsimp only at hc ⊢
  simp only [upd_self, hX 1 (by decide), hX 2 (by decide)]
  rcases hc with ⟨a, b, c, d⟩ | ⟨a, b, c, d, f⟩ | ⟨a, b, c, d, f, k⟩
  · exact .inl ⟨a, h1 b, c, d⟩
  · exact .inr (.inl ⟨a, h2 b, c, d, f⟩)
  · obtain ⟨b', hj⟩ := h3 b
    refine .inr (.inr ⟨a, b', c, d, ?_, k⟩)
    rw [show decide (g.2.ph = .j1) = decide ((G 0).2.ph = .j1) from decide_eq_decide.mpr hj.symm]
    exact f

/-- **The protocol's invariant after `main`'s RMW at the group's state** (`U_mainRmw`, the lock's
invariant relabelled: the counter does not read `main`'s place). -/
theorem inv_mainRmw {G : ThreadId → Gh} {rY : Res} {m m' : Mem} {rM : Res} {x₀ x₁ : X}
    {ord : AtomicOrder} {new : BitVec 64} (hg : G 0 = gO rM x₀)
    (hu : U G (rsum (WG.cellsR m) rY) m) (hY : ∀ l, WG.In l → rY.heap l = none)
    (hc : m.current = 0)
    (hhW : WG.hist m' = (WG.hist m).push (Word.rmwEnt m' 0 ord (newest WG m) new))
    (hrel : ord.isRel = false) (hH : WG.Holds m' (BitVec.ofNat 64 (wgv x₁ (G 1).2 (G 2).2)))
    (hw' : WG.Ok m' (fun u => WLive (G u)))
    (hA : ∀ hF : Heap, (∀ x, WG.o ≤ x → x < WG.o + 8 → hF (WG.b, x) = none) → FStepIn hF m m')
    (hL : L.Inv G (rsum (WG.cellsR m') rY) m')
    (he₀ : x₀.e = .out) (he₁ : x₁.e = .out) (hsx₁ : x₁.sx = false) (hfd₁ : x₁.ph.fd = false)
    (hwx : x₀.ph.wa = true → x₁.ph.wa = true) (hwxk : x₀.wk = true → x₁.wk = true)
    (hwk₁ : x₁.wk = true → x₁.ph.wa = true) (hm : x₁.ph.isMain = true)
    (h1 : x₀.ph.rank ≤ 1 → x₁.ph.rank ≤ 1) (h2 : x₀.ph = .sp1 → x₁.ph = .sp1)
    (h3 : 3 ≤ x₀.ph.rank → 3 ≤ x₁.ph.rank ∧ (x₀.ph = .j1 ↔ x₁.ph = .j1))
    (hlast3 : x₁.wk = true → (G 1).2.ph.fd = true → (G 2).2.ph.fd = true →
      ∃ u, (G u).2.sx = true)
    (hdone : 6 ≤ x₁.ph.rank → (G 1).2.ph.fd = true ∧ (G 2).2.ph.fd = true ∧
      VClock.le (G 1).2.fc (m'.clocks[0]!) = true ∧ VClock.le (G 2).2.fc (m'.clocks[0]!) = true ∧
      (∀ j < (EV.hist m).size, IsSetW m j →
        VClock.le (EV.hist m)[j]!.clock (m'.clocks[0]!) = true) ∧
      ∀ u, (G u).2.sx = true → (G u).2.e.Setting ∨ (G u).2.ph = .fin) :
    proto.inv (upd G 0 (gO rM x₁)) m' := by
  have e : gO rM x₁ = ((G 0).1, x₁) := by rw [hg]; rfl
  have hx₀ : (G 0).2 = x₀ := by rw [hg]; rfl
  refine ⟨_, hL.relabel (t := 0) (by rw [hg]; rfl) (by rw [hg]; rfl) (by rw [hg]; rfl)
    fun _ hR => R_upd0 hR, ?_⟩
  rw [e]
  exact U_mainRmw hu hY hc hhW hrel hH hw' hA hL (by rw [hx₀]; exact he₀) he₁ hsx₁ hfd₁
    (by rw [hx₀]; exact hwx) (by rw [hx₀]; exact hwxk) hwk₁
    (shape_main hu.shape (by exact hm) (by rw [hx₀]; exact h1) (by rw [hx₀]; exact h2)
      (by rw [hx₀]; exact h3))
    hlast3 hdone

/-! ## `startMany` -/

/-- Before `main`'s spawns the tasks have no place. -/
theorem none12 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m)
    (h : (G 0).2.ph.rank ≤ 1) : (G 1).2 = {} ∧ (G 2).2 = {} := by
  obtain ⟨-, -, -, ⟨-, -, h1, h2⟩ | ⟨-, h0, -⟩ | ⟨-, h0, -⟩⟩ := hu.shape
  · exact ⟨h1, h2⟩
  · have h0' : (G 0).2.ph = .sp1 := h0; rw [h0'] at h; simp [Ph.rank] at h
  · have h0' : 3 ≤ (G 0).2.ph.rank := h0; omega

/-- **`startMany(2)`'s `add(4)`** at `pre`: the group's state was 0; `main` to `sm`. -/
theorem wp_smRmw {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat} {rM : Res}
    (hi : proto.inv (upd G 0 (gO rM { ph := .pre })) m)
    {Q : BitVec 64 × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = 0 →
      proto.inv (upd G₁ 0 (gO rM { ph := .sm })) m' → Q ((0 : BitVec 64), s) G₁ m' k) :
    proto.WP 0 ((atomicRmwC .add false .relaxed 8 bPtr (4 : BitVec 64) : CM Tgt σ (BitVec 64)).run s)
      Q G m n := by
  refine FLock.wp_wordRmw fitsE wg_inRest apG hi (hlv := rfl) ?_
  intro k hk G₁ rY m₁ m' old hg₁ hc₁ hU _ hY hv hH hh _ hw' _ _ _ hA _ _ hL
  have hx₀ : (G₁ 0).2 = { ph := .pre } := by rw [hg₁]; rfl
  obtain ⟨h1, h2⟩ := none12 hU (by rw [hx₀]; decide)
  have h0 : old = 0 := Word.Entry.val_inj hv (by
    have := hU.gv; rw [hx₀] at this; exact this)
  subst h0
  refine h k hk G₁ m' ((hA (fun _ => none) (fun _ _ _ => rfl)).current.trans hc₁) ?_
  refine inv_mainRmw hg₁ hU hY hc₁ hh rfl ?_ hw' hA hL rfl rfl rfl rfl (fun h => h) (fun h => h)
    (fun h => by cases h) rfl (fun _ => by decide) (fun h => by cases h) (fun h => by simp [Ph.rank] at h)
    (fun h => by cases h) (fun h => by simp [Ph.rank] at h)
  rw [h1, h2]; exact hH

/-- **`main`'s `startMany(2)`** at `pre`: to `sm`. -/
theorem wp_startMany {G : ThreadId → Gh} {m : Mem} {d : Nat} {rM : Res}
    (hi : proto.inv (upd G 0 (gO rM { ph := .pre })) m) :
    proto.WP 0 (Thread_WaitGroup_startMany bPtr 2) (fun _ G' m' d' => d' < d ∧ m'.current = 0 ∧
      proto.inv (upd G' 0 (gO rM { ph := .sm })) m') G m d := by
  unfold Thread_WaitGroup_startMany
  fsym [wp_smRmw, debug_assert]

/-! ## The spawns -/

/-- A fork by `t` moves no thread's clock back. -/
theorem clk_fork {cs : Array VClock} {t : ThreadId} (ht : t < cs.size) (u : ThreadId) :
    VClock.le (cs[u]!) (((cs.set! t (VClock.bump (cs[t]!) t)).push
      (VClock.bump (cs[t]!) t))[u]!) = true := by
  by_cases hu : u < cs.size
  · exact (Conc.fork_clocks ht).1 u hu
  · rw [getElem!_neg cs u hu]; exact VClock.le_default _

/-- A task's bound grows with its clock, at the same finish (and finish clock). -/
theorem bnd_le {G G' : ThreadId → Gh} {m m' : Mem} {u : ThreadId}
    (hfd : (G' u).2.ph.fd = (G u).2.ph.fd)
    (hfc : (G u).2.ph.fd = true → (G' u).2.fc = (G u).2.fc)
    (hclk : VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    VClock.le (bnd G m u) (bnd G' m' u) = true := by
  unfold bnd; rw [hfd]
  cases h : (G u).2.ph.fd
  · simpa using hclk
  · simp only [↓reduceIte]; rw [hfc h]; exact VClock.le_refl _

/-- A thread out of the event's code gets another ghost value out of it (`FEvent.Inv.toOut`). -/
theorem einv_out {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh} (hI : E.Inv L G m)
    (h₀ : (G t).2.e = .out) (h₁ : g.2.e = .out) (hwx : E.wx (G t) → E.wx g) :
    E.Inv L (upd G t g) m :=
  have hsd : E.ph g ≠ .sd := fun h => by
    rw [show E.ph g = g.2.e from rfl, h₁] at h; cases h
  hI.toOut (.inl h₀) (.inl h₁) (fun h => absurd h hsd) hwx (fun h => absurd h hsd)

/-- Before `main`'s `add(1)` no task is the setter, and the event has no `is_set` write. -/
theorem no_set {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m)
    (hwa : (G 0).2.ph.wa = false) :
    (∀ u, (G u).2.sx = false) ∧ ∀ j < (EV.hist m).size, ¬ IsSetW m j := by
  have hsx : ∀ u, (G u).2.sx = false := fun u => by
    cases h : (G u).2.sx
    · rfl
    · have := (hu.sto u h).2.1; rw [hwa] at this; cases this
  refine ⟨hsx, fun j hj hs => ?_⟩
  obtain ⟨⟨u, h, -⟩, -⟩ := hu.isw j hj hs
  rw [hsx u] at h; cases h

/-- **`main`'s spawn of task `k`** (from `main`'s place `(G 0).2`, before its `add(1)`, to `x₁`):
the new thread starts at `lk` with `main`'s clock, so the words stay `Ok` for the live sets with it
(`Word.Ok.fork_native`) and its bound is above every access `main` made; no setter yet. -/
theorem U_spawn {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {k : ThreadId} {rM rP : Res}
    {x₁ : X} (hu : U G rX m) (hk0 : k ≠ 0) (hk3 : k < 3) (hGk : (G k).2 = {})
    (hcs : m.clocks.size = m.threads.size) (he₀ : (G 0).2.e = .out)
    (hwa₀ : (G 0).2.ph.wa = false) (hpre : (G 0).2.ph ≠ .pre)
    (he₁ : x₁.e = .out) (hsx₁ : x₁.sx = false) (hwa₁ : x₁.ph.wa = false) (hfd₁ : x₁.ph.fd = false)
    (hr₁ : x₁.ph.rank < 4) (hpre₁ : x₁.ph ≠ .pre) (hwk₁ : x₁.wk = false)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (k, m')))
    (hsh : Shape (fun u => (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u).2)
      { m with threads := m.threads.push { spawner := 0, joined := false } }) :
    U (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁)) rX m' := by
  have hfork := hf
  change ((Thread.forkWith false).run { m with current := 0 }).run = some (.ok (k, m')) at hfork
  rw [Proto.forkWith_run] at hfork
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hfork
  obtain ⟨hk, rfl⟩ := hfork
  have ht0 : 0 < m.threads.size := by unfold ThreadId at *; omega
  have hclk := clk_fork (cs := m.clocks) (t := 0) (by rw [hcs]; exact ht0)
  have h0 : upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) 0 = gO rM x₁ := upd_self _ _ _
  have hk' : upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) k = gO rP { ph := .lk } := by
    rw [upd_ne _ _ hk0, upd_self]
  have hX : ∀ u, u ≠ 0 → u ≠ k → upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u = G u :=
    fun u h0 hk => by rw [upd_ne _ _ h0, upd_ne _ _ hk]
  have hmain := fd0 hu
  obtain ⟨hnsx, hnis⟩ := no_set hu hwa₀
  -- the places that the fields read: `fd`, `sx`, `wa` stay those of `G` but at 0 and `k`
  have hfd : ∀ u, (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u).2.ph.fd = (G u).2.ph.fd :=
    fun u => by
      by_cases e0 : u = 0
      · subst e0; rw [h0, hmain]; exact hfd₁
      by_cases ek : u = k
      · subst ek; rw [hk', hGk]; rfl
      rw [hX u e0 ek]
  have hsx' : ∀ u, (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u).2.sx = false := fun u => by
    by_cases e0 : u = 0
    · subst e0; rw [h0]; exact hsx₁
    by_cases ek : u = k
    · subst ek; rw [hk']; rfl
    rw [hX u e0 ek]; exact hnsx u
  have hfdT : ∀ u, (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u).2.ph.fd = true →
      upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u = G u ∧ u ≠ 0 := fun u h => by
    by_cases e0 : u = 0
    · subst e0; rw [h0] at h; exact absurd (h.symm.trans hfd₁) (by decide)
    by_cases ek : u = k
    · subst ek; rw [hk'] at h; cases h
    exact ⟨hX u e0 ek, e0⟩
  have hWl : ∀ u, WLive (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u) → WLive (G u) :=
    fun u h => by unfold WLive at h ⊢; rw [← hfd u]; exact h
  have hEl : ∀ u, ELive (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u) → ELive (G u) :=
    fun u h => by
      by_cases e0 : u = 0
      · subst e0; exact .inl hmain
      by_cases ek : u = k
      · subst ek; exact .inl (by show (G u).2.ph.fd = false; rw [hGk]; rfl)
      rwa [hX u e0 ek] at h
  obtain ⟨hwG, hhG⟩ := (hu.wg.anti hWl).fork_native (t := 0) ht0 hcs hf
    (fun _ => by show (upd (upd G k _) 0 (gO rM x₁) 0).2.ph.fd = false; rw [h0]; exact hfd₁)
  obtain ⟨hwE, hhE⟩ := (hu.ev.anti hEl).fork_native (t := 0) ht0 hcs hf
    (fun _ => .inl (by show (upd (upd G k _) 0 (gO rM x₁) 0).2.ph.fd = false; rw [h0]; exact hfd₁))
  have hJ := hu.einv.frame (G' := G) (t := 0) (fun _ _ => rfl) rfl rfl hhE rfl hclk
    (by simp) id id hu.einv.fresh rfl rfl
  have hJ' := einv_out (einv_out hJ (t := k) (g := gO rP { ph := .lk }) (by rw [hGk]) rfl
      (fun h => by
        have h' : (G k).2.wk = true := h
        rw [hGk] at h'; cases h'))
    (t := 0) (g := gO rM x₁) (by rw [upd_ne _ _ (Ne.symm hk0)]; exact he₀) he₁
    (fun h => by
      have h' : (upd G k (gO rP { ph := .lk }) 0).2.wk = true := h
      rw [upd_ne _ _ (Ne.symm hk0)] at h'
      have := (hu.wk0 0 h').2; rw [hwa₀] at this; cases this)
  refine ⟨Shape.congr hsh rfl (fun _ => rfl) (fun _ h => h), hu.rest.congr fun _ _ => rfl, hu.blk,
    hwG, hwE, hJ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hu.q⟩
  · -- gv: `main` past `pre` before its `add`, no task finished
    show (newest WG _).Val _
    unfold newest; rw [hhG]
    have e : wgv (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) 0).2
        (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) 1).2
        (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) 2).2 = wgv (G 0).2 (G 1).2 (G 2).2 := by
      unfold wgv X.fdn
      rw [h0, hfd 1, hfd 2]
      show (if x₁.ph = .pre then 0 else 4 + (if x₁.ph.wa then 1 else 0) - _) = _
      rw [if_neg hpre₁, if_neg hpre, hwa₁, hwa₀]
    rw [e]; exact hu.gv
  · intro u h; obtain ⟨e, -⟩ := hfdT u h; unfold newest; rw [hhG, e]; rw [e] at h; exact hu.gw u h
  · intro u h; rw [hsx' u] at h; cases h
  · intro h; rw [h0] at h; have h' : x₁.wk = true := h; rw [hwk₁] at h'; cases h'
  · intro j hj hs; unfold IsSetW at hs; rw [hhE] at hj hs; exact absurd hs (hnis j hj)
  · intro i hi j hj h1 h2; unfold IsSetW at h1 h2; rw [hhE] at hi hj h1 h2
    exact hu.one i hi j hj h1 h2
  · intro u h; rw [hsx' u] at h; cases h
  · intro u h; obtain ⟨e, -⟩ := hfdT u h; rw [e]; rw [e] at h; exact hu.lg u h
  · intro u h3
    rw [hX u (by unfold ThreadId at *; omega) (by unfold ThreadId at *; omega)]; exact hu.out3 u h3
  · intro u h
    by_cases e0 : u = 0
    · exact e0
    by_cases ek : u = k
    · subst ek; rw [hk'] at h; cases h
    rw [hX u e0 ek] at h; exact hu.wa0 u h
  · intro u h
    by_cases e0 : u = 0
    · subst e0
      rw [h0] at h
      have h' : x₁.wk = true := h
      rw [hwk₁] at h'; cases h'
    by_cases ek : u = k
    · subst ek; rw [hk'] at h; cases h
    rw [hX u e0 ek] at h ⊢; exact hu.wk0 u h
  · intro u v h; rw [hsx' u] at h; cases h
  · -- attr: the same accesses; the bounds grow
    intro e he hb hkw hl ho
    rcases hu.attr e he hb hkw hl ho with h | ⟨u, hu12, h⟩ | ⟨j, hj, hs, -⟩
    · exact .inl (VClock.le_trans h (hclk 0))
    · exact .inr (.inl ⟨u, hu12, VClock.le_trans h (bnd_le (hfd u)
        (fun h => by rw [(hfdT u (by rw [hfd u]; exact h)).1]) (hclk u))⟩)
    · exact absurd hs (hnis j hj)
  · intro h; rw [h0] at h; have h' : 6 ≤ x₁.ph.rank := h; omega

/-- **The threads after `main`'s spawn of task `k`**: one more, spawned by `main`, not joined. -/
theorem shape_spawn {G : ThreadId → Gh} {m : Mem} {k : ThreadId} {rM rP : Res} {x₁ : X}
    (h : Shape (fun u => (G u).2) m)
    (hk : (k = 1 ∧ (G 0).2.ph = .sm ∧ x₁.ph = .sp1) ∨ (k = 2 ∧ (G 0).2.ph = .sp1 ∧ x₁.ph = .run)) :
    m.threads.size = k ∧ (G k).2 = {} ∧
      Shape (fun u => (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u).2)
        { m with threads := m.threads.push { spawner := 0, joined := false } } := by
  obtain ⟨h00, -, hn, hc⟩ := h
  have hk0 : k ≠ 0 := by rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have e0 : (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) 0).2 = x₁ := by rw [upd_self]; rfl
  have ek : (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) k).2 = { ph := .lk } := by
    rw [upd_ne _ _ hk0, upd_self]; rfl
  have eu : ∀ u, u ≠ 0 → u ≠ k → upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) u = G u :=
    fun u h0 hk => by rw [upd_ne _ _ h0, upd_ne _ _ hk]
  have hpush : ∀ i, i < m.threads.size →
      (m.threads.push ({ spawner := 0, joined := false } : ThreadRec))[i]? = m.threads[i]? :=
    fun i hi => by simp only [Array.getElem?_push]; rw [ite_eq_right_iff.mpr (by omega)]
  have hnew : (m.threads.push ({ spawner := 0, joined := false } : ThreadRec))[m.threads.size]? =
      some { spawner := 0, joined := false } := by simp
  generalize upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) = G' at e0 ek eu ⊢
  rcases hk with ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1⟩
  · rcases hc with ⟨a, -, c, d⟩ | ⟨-, b, -⟩ | ⟨-, b, -⟩
    · refine ⟨a, c, ?_, ?_, fun u hu => ?_, .inr (.inl ⟨?_, ?_, ?_, ?_, ?_⟩)⟩
      · show (m.threads.push _)[0]? = _; rw [hpush 0 (by omega)]; exact h00
      · show (G' 0).2.ph.isMain = true; rw [e0, h1]; rfl
      · show (G' u).2 = _
        rw [eu u (by unfold ThreadId at *; omega) (by unfold ThreadId at *; omega)]; exact hn u hu
      · show (m.threads.push _).size = 2; rw [Array.size_push, a]
      · show (G' 0).2.ph = _; rw [e0, h1]
      · show (m.threads.push _)[1]? = _; rw [show 1 = m.threads.size by omega]; exact hnew
      · show (G' 1).2.ph.isTask = true; rw [ek]; rfl
      · show (G' 2).2 = _; rw [eu 2 (by decide) (by decide)]; exact d
    · have : (G 0).2.ph = .sp1 := b; rw [h0] at this; cases this
    · have : 3 ≤ (G 0).2.ph.rank := b; rw [h0] at this; simp [Ph.rank] at this
  · rcases hc with ⟨-, b, -⟩ | ⟨a, -, c, d, f⟩ | ⟨-, b, -⟩
    · have : (G 0).2.ph.rank ≤ 1 := b; rw [h0] at this; simp [Ph.rank] at this
    · refine ⟨a, f, ?_, ?_, fun u hu => ?_, .inr (.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)⟩
      · show (m.threads.push _)[0]? = _; rw [hpush 0 (by omega)]; exact h00
      · show (G' 0).2.ph.isMain = true; rw [e0, h1]; rfl
      · show (G' u).2 = _
        rw [eu u (by unfold ThreadId at *; omega) (by unfold ThreadId at *; omega)]; exact hn u hu
      · show (m.threads.push _).size = 3; rw [Array.size_push, a]
      · show 3 ≤ (G' 0).2.ph.rank; rw [e0, h1]; decide
      · show (G' 1).2.ph.isTask = true; rw [eu 1 (by decide) (by decide)]; exact d
      · show (G' 2).2.ph.isTask = true; rw [ek]; rfl
      · show (m.threads.push _)[1]? = some { spawner := 0, joined := decide ((G' 0).2.ph = Ph.j1) }
        rw [hpush 1 (by omega), c, e0, h1]; rfl
      · show (m.threads.push _)[2]? = _; rw [show 2 = m.threads.size by omega]; exact hnew
    · have : 3 ≤ (G 0).2.ph.rank := b; rw [h0] at this; simp [Ph.rank] at this

/-- The counter after a spawn: the new task has not stored it. -/
theorem R_spawn {G : ThreadId → Gh} {k : ThreadId} {g₀ g₁ : Gh} {r : Res} (hk0 : k ≠ 0)
    (hGk : (G k).2 = {}) (hg₀ : g₀.2.ph = .lk) (h : L.R G r) : L.R (upd (upd G k g₀) 0 g₁) r := by
  have hc : ∀ u, u ≠ 0 → (upd (upd G k g₀) 0 g₁ u).2.cnt = (G u).2.cnt := fun u hu => by
    rw [upd_ne _ _ hu]
    by_cases e : u = k
    · subst e; rw [upd_self, hGk]; unfold X.cnt; rw [hg₀]; rfl
    · rw [upd_ne _ _ e]
  show up (pts (bPtr.add 20) 4
    (BitVec.ofNat 32 ((upd (upd G k g₀) 0 g₁ 1).2.cnt + (upd (upd G k g₀) 0 g₁ 2).2.cnt))) r
  rw [hc 1 (by decide), hc 2 (by decide)]
  exact h

/-- **`main`'s spawn of task `k`** after its part has been split (`rP`, the copied plain mode, is
the task's): the lock forks (`FLock.Inv.fork`) and `U` holds (`U_spawn`). -/
theorem inv_spawnParts {G : ThreadId → Gh} {m m' : Mem} {c k : ThreadId} {rM rP : Res}
    {x₀ x₁ : X} (hP : plain rP) (hi : proto.inv G m) (hg : G 0 = gO (rsum rM rP) x₀)
    (hk : (k = 1 ∧ x₀.ph = .sm ∧ x₁.ph = .sp1) ∨ (k = 2 ∧ x₀.ph = .sp1 ∧ x₁.ph = .run))
    (he₀ : x₀.e = .out) (he₁ : x₁.e = .out) (hsx₁ : x₁.sx = false) (hwk₁ : x₁.wk = false)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = k ∧ proto.inv (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁)) m' := by
  obtain ⟨rX, hL, hu⟩ := hi
  have hx₀ : (G 0).2 = x₀ := by rw [hg]; rfl
  obtain ⟨hsz, hGk, hsh⟩ := shape_spawn (rM := rM) (rP := rP) (x₁ := x₁) hu.shape (by
    rw [hx₀]; exact hk)
  have hk0 : k ≠ 0 := by rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hcs : m.clocks.size = m.threads.size := hL.w.csize
  have hfork := hf
  change ((Thread.forkWith false).run { m with current := 0 }).run = some (.ok (c, m')) at hfork
  rw [Proto.forkWith_run] at hfork
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hfork
  have hc : c = k := by rw [← hfork.1]; exact hsz
  subst hc
  have hL' := hL.fork (t := 0) (g₁ := gO rM x₁) (g₀ := gO rP { ph := .lk })
    (by rw [hg]; rfl) hf (by rw [hg]; rfl)
    (by show FHeap.Disjoint rM.heap rP.heap; rw [(plain_ghost hP).1]; exact FHeap.disjoint_empty _)
    rfl rfl rfl rfl fun r hR => by
      rw [← hfork.1, hsz]; exact R_spawn hk0 hGk rfl hR
  rw [← hfork.1, hsz] at hL'
  have hph : x₁.ph.rank < 4 ∧ x₁.ph ≠ .pre ∧ x₁.ph.wa = false ∧ x₁.ph.fd = false ∧
      x₀.ph.wa = false ∧ x₀.ph ≠ .pre := by
    rcases hk with ⟨-, h0, h1⟩ | ⟨-, h0, h1⟩ <;> rw [h0, h1] <;> decide
  obtain ⟨hr₁, hp₁, hwa₁, hfd₁, hwa₀, hp₀⟩ := hph
  refine ⟨rfl, _, hL', U_spawn hu hk0 (by rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide) hGk hcs
    (by rw [hx₀]; exact he₀) (by rw [hx₀]; exact hwa₀) (by rw [hx₀]; exact hp₀) he₁ hsx₁ hwa₁ hfd₁
    hr₁ hp₁ hwk₁ (by rw [← hfork.1, hsz] at hf; exact hf) hsh⟩

/-- A change of `t`'s part at the same memory keeps `U` (`U_own_native` with no step). -/
theorem U_part {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {r : Res}
    (hu : U G rX m) (hc : m.current = t) (hng : (G t).1.ph ≠ .gone)
    (hi' : L.Inv (upd G t (L.setPart (G t) r)) rX m) :
    U (upd G t (L.setPart (G t) r)) rX m := by
  obtain ⟨rY, hrX, hY⟩ := Rest.split (fun _ => ev_box) hu.rest
  subst hrX
  exact U_own_native hu hY hng hc (FStepIn.refl _ _) (fun _ _ => rfl) rfl hi'

/-- **`main`'s spawn of task `k`**: `main` copies its duplicable plain mode `rM` for the task
(`EUpd.plain_split`), then forks (`inv_spawnParts`). -/
theorem inv_spawnK {G : ThreadId → Gh} {m m' : Mem} {c k : ThreadId} {rM : Res} {x₀ x₁ : X}
    (hp : rM.Plain) (hi : proto.inv G m) (hg : G 0 = gO rM x₀)
    (hk : (k = 1 ∧ x₀.ph = .sm ∧ x₁.ph = .sp1) ∨ (k = 2 ∧ x₀.ph = .sp1 ∧ x₁.ph = .run))
    (he₀ : x₀.e = .out) (he₁ : x₁.e = .out) (hsx₁ : x₁.sx = false) (hwk₁ : x₁.wk = false)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = k ∧ ∃ rP, plain rP ∧
      proto.inv (upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁)) m' := by
  obtain ⟨rX, hL, hU⟩ := hi
  have hL₀ : L.Inv (upd G 0 (G 0)) rX { m with current := 0 } := by
    rw [upd_same]
    exact hL.cur 0
  obtain ⟨r, ⟨r₁, rP, hd, rfl, hr₁, hpP⟩, hL'⟩ := hL₀.eupdPart proto rfl
    (by rw [hg]; exact fun h => nomatch h) (EUpd.plain_split (P := fun r => r = L.part (G 0))
      fun r hr => by rw [hr, hg]; exact hp)
  have hrM : rM = r₁ := by rw [hr₁, hg]; rfl
  subst hrM
  have hU₀ := atStop 0 hU
  have hU' := U_part hU₀ rfl (by rw [hg]; exact fun h => nomatch h)
    (by simpa only [upd_upd] using hL')
  have hG' : upd G 0 (L.setPart (G 0) (rsum rM rP)) 0 = gO (rsum rM rP) x₀ := by
    rw [upd_self, hg]; rfl
  obtain ⟨hc, hi'⟩ := inv_spawnParts hpP ⟨rX, by simpa only [upd_upd] using hL', hU'⟩ hG' hk he₀
    he₁ hsx₁ hwk₁ hf
  refine ⟨hc, rP, hpP, ?_⟩
  have hk0 : k ≠ 0 := by rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have he : upd (upd (upd G 0 (L.setPart (G 0) (rsum rM rP))) k (gO rP { ph := .lk }))
      0 (gO rM x₁) = upd (upd G k (gO rP { ph := .lk })) 0 (gO rM x₁) := by
    rw [upd_comm G _ _ (Ne.symm hk0), upd_upd]
  rwa [he] at hi'

/-- `main`'s first spawn, at `sm`: task 1; `main` to `sp1`. -/
theorem inv_spawn1 {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} {rM : Res} (hp : rM.Plain)
    (hi : proto.inv G m) (hg : G 0 = gO rM { ph := .sm })
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 1 ∧ ∃ rP, plain rP ∧
      proto.inv (upd (upd G 1 (gO rP { ph := .lk })) 0 (gO rM { ph := .sp1 })) m' :=
  inv_spawnK hp hi hg (.inl ⟨rfl, rfl, rfl⟩) rfl rfl rfl rfl hf

/-- `main`'s second spawn, at `sp1`: task 2; `main` to `run`. -/
theorem inv_spawn2 {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} {rM : Res} (hp : rM.Plain)
    (hi : proto.inv G m) (hg : G 0 = gO rM { ph := .sp1 })
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 2 ∧ ∃ rP, plain rP ∧
      proto.inv (upd (upd G 2 (gO rP { ph := .lk })) 0 (gO rM { ph := .run })) m' :=
  inv_spawnK hp hi hg (.inr ⟨rfl, rfl, rfl⟩) rfl rfl rfl rfl hf

end Threadsync.WG
