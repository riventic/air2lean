import Proofs.Threadsync.WaitGroup.Main
import Proofs.Threadsync.Event

/-!
# `main`'s wait in `waitGroup`'s protocol

`main`'s place changes at a step that keeps the memory model's data (`U_main`: a relabel, a
join), its `wait` on the group: the `add(1)` (`wp_waRmw`) and, if it read a pending task, the
event's wait (`wp_ewait`, a client of `EventImpl.wait_wp`), after which `main` is after both
finishes and the set (`inv_rd`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Threadsync.WG

/-! ## `main`'s place changes without a step of the words -/

/-- **`main`'s new place `x₁` across a step that keeps the memory model's data** (a relabel at the
same memory, a join): the cells, blocks, atomics and footprint stay, as many threads, the clocks
grow. `main`'s event place, its roles and the group's value stay; the caller gives the threads'
shape and `done` for `x₁`. -/
theorem U_main {G : ThreadId → Gh} {rX : Res} {m m' : Mem} {x₁ : X} (hu : U G rX m)
    (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics) (hf : m'.footprint = m.footprint)
    (hh : ∀ l, m'.heap l = m.heap l) (hts : m'.threads.size = m.threads.size)
    (hw : m'.waiters = m.waiters) (hn : m.nextMsg ≤ m'.nextMsg)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (he : x₁.e = (G 0).2.e) (hsx : x₁.sx = false) (hfd : x₁.ph.fd = false)
    (hwa : x₁.ph.wa = (G 0).2.ph.wa) (hwk : x₁.wk = (G 0).2.wk)
    (hgv : wgv x₁ (G 1).2 (G 2).2 = wgv (G 0).2 (G 1).2 (G 2).2)
    (hsh : Shape (fun u => (upd G 0 ((G 0).1, x₁) u).2) m')
    (hdone : 6 ≤ x₁.ph.rank → (G 1).2.ph.fd = true ∧ (G 2).2.ph.fd = true ∧
      VClock.le (G 1).2.fc (m'.clocks[0]!) = true ∧ VClock.le (G 2).2.fc (m'.clocks[0]!) = true ∧
      (∀ j < (EV.hist m).size, IsSetW m j →
        VClock.le (EV.hist m)[j]!.clock (m'.clocks[0]!) = true) ∧
      ∀ u, (G u).2.sx = true → (G u).2.e.Setting ∨ (G u).2.ph = .fin) :
    U (upd G 0 ((G 0).1, x₁)) rX m' := by
  have hX0 : (upd G 0 ((G 0).1, x₁) 0).2 = x₁ := by rw [upd_self]
  have hX : ∀ u, u ≠ 0 → upd G 0 ((G 0).1, x₁) u = G u := fun u h => upd_ne _ _ h
  have h10 : (1 : ThreadId) ≠ 0 := by decide
  have h20 : (2 : ThreadId) ≠ 0 := by decide
  have hmain := fd0 hu
  obtain ⟨hwG, hhG⟩ := hu.wg.fields_size hb ha hf hts hclk
  obtain ⟨hwE, hhE⟩ := hu.ev.fields_size hb ha hf hts hclk
  have hkE : EV.key m' = EV.key m := Mem.wordKey_of_blocks hb _ _ _
  have hkL : L.key m' = L.key m := Mem.wordKey_of_blocks hb _ _ _
  have hI : E.Inv L (upd G 0 ((G 0).1, x₁)) m' :=
    hu.einv.frame (t := 0) (fun u hu => upd_ne _ _ hu) (by rw [upd_self]; exact he)
      (by rw [upd_self]; rfl) hhE hw hclk (Nat.le_of_eq hts.symm)
      (fun h => by rw [upd_self]; show x₁.wk = true; rw [hwk]; exact h)
      (fun h => absurd hmain (by rw [h.2]; decide)) (hu.einv.fresh.of_eq ha hn) hkE hkL
  have hattr := attr_step hu (G' := G) (fun _ => rfl) hclk hhE
    (fun e he _ _ => .inl ⟨e, hf ▸ he, .refl e⟩)
  have hbnd : ∀ u, (u = 1 ∨ u = 2) → bnd (upd G 0 ((G 0).1, x₁)) m' u = bnd G m' u := by
    rintro u (rfl | rfl) <;> unfold bnd <;> rw [hX _ (by decide)]
  obtain ⟨blk, hb1, hb2⟩ := hu.blk
  refine ⟨hsh, hu.rest.congr fun l _ => hh l, ⟨blk, by rw [hb]; exact hb1, hb2⟩,
    hwG.anti fun u h => ?_, hwE.anti fun u h => ?_, hI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, fun w hw' => by rw [hkL, hkE]; exact hu.q w (by rw [← hw]; exact hw')⟩
  · by_cases e : u = 0
    · subst e; exact hmain
    · rwa [hX u e] at h
  · by_cases e : u = 0
    · subst e; exact .inl hmain
    · rwa [hX u e] at h
  · -- gv
    show (newest WG m').Val _
    unfold newest; rw [hhG, hX0, hX 1 h10, hX 2 h20, hgv]; exact hu.gv
  · -- gw
    intro u h; unfold newest; rw [hhG]
    by_cases e : u = 0
    · subst e; rw [hX0, hfd] at h; cases h
    · rw [hX u e] at h ⊢; exact hu.gw u h
  · -- sto
    intro u h
    have e : u ≠ 0 := by
      intro e; subst e; rw [hX0, hsx] at h; cases h
    rw [hX u e] at h ⊢
    obtain ⟨a, b, c, d, f⟩ := hu.sto u h
    refine ⟨a, by rw [hX0, hwa]; exact b, by rw [hX 1 h10]; exact c, by rw [hX 2 h20]; exact d,
      fun hs ho => ?_⟩
    rw [hX 1 h10, hX 2 h20]
    obtain ⟨x, y⟩ := f hs ho
    exact ⟨VClock.le_trans x (hclk u), VClock.le_trans y (hclk u)⟩
  · -- last3
    intro h0 h1 h2
    rw [hX0, hwk] at h0; rw [hX 1 h10] at h1; rw [hX 2 h20] at h2
    obtain ⟨u, hu'⟩ := hu.last3 h0 h1 h2
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
      intro e; subst e; rw [hX0, hsx] at h1; cases h1
    rw [hX u e] at h1 h2
    exact E.IsSet_of_hist_eq hhE (hu.sfin u h1 h2)
  · -- lg
    intro u h
    by_cases e : u = 0
    · subst e; rw [hX0, hfd] at h; cases h
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
    · subst e; rw [hX0] at h ⊢; rw [hwk] at h; rw [hwa]; exact hu.wk0 0 h
    · rw [hX u e] at h ⊢; exact hu.wk0 u h
  · -- sx1
    intro u v h1 h2
    have e1 : u ≠ 0 := by
      intro e; subst e; rw [hX0, hsx] at h1; cases h1
    have e2 : v ≠ 0 := by
      intro e; subst e; rw [hX0, hsx] at h2; cases h2
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
        intro e; subst e; rw [hX0, hsx] at hx; cases hx
      rw [hX u e] at hx ⊢; exact k u hx

/-- **`main` at a new place `x₁` at the same memory** (`U_main`; the lock's invariant
relabelled: the counter does not read `main`'s place). -/
theorem inv_main0 {G : ThreadId → Gh} {m : Mem} {rM : Res} {x₀ x₁ : X}
    (hi : proto.inv (upd G 0 (gO rM x₀)) m)
    (he : x₁.e = x₀.e) (hsx : x₁.sx = false) (hfd : x₁.ph.fd = false)
    (hwa : x₁.ph.wa = x₀.ph.wa) (hwk : x₁.wk = x₀.wk)
    (hgv : wgv x₁ (G 1).2 (G 2).2 = wgv x₀ (G 1).2 (G 2).2) (hm : x₁.ph.isMain = true)
    (h1 : x₀.ph.rank ≤ 1 → x₁.ph.rank ≤ 1) (h2 : x₀.ph = .sp1 → x₁.ph = .sp1)
    (h3 : 3 ≤ x₀.ph.rank → 3 ≤ x₁.ph.rank ∧ (x₀.ph = .j1 ↔ x₁.ph = .j1))
    (hdone : 6 ≤ x₁.ph.rank → (G 1).2.ph.fd = true ∧ (G 2).2.ph.fd = true ∧
      VClock.le (G 1).2.fc (m.clocks[0]!) = true ∧ VClock.le (G 2).2.fc (m.clocks[0]!) = true ∧
      (∀ j < (EV.hist m).size, IsSetW m j →
        VClock.le (EV.hist m)[j]!.clock (m.clocks[0]!) = true) ∧
      ∀ u, u ≠ 0 → (G u).2.sx = true → (G u).2.e.Setting ∨ (G u).2.ph = .fin) :
    proto.inv (upd G 0 (gO rM x₁)) m := by
  obtain ⟨rX, hL, hu⟩ := hi
  have hg : upd G 0 (gO rM x₀) 0 = gO rM x₀ := upd_self _ _ _
  have h10 : (1 : ThreadId) ≠ 0 := by decide
  have h20 : (2 : ThreadId) ≠ 0 := by decide
  have hU := U_main (x₁ := x₁) hu rfl rfl rfl (fun _ => rfl) rfl rfl (Nat.le_refl _)
    (fun _ => VClock.le_refl _) (by rw [hg]; exact he) hsx hfd (by rw [hg]; exact hwa)
    (by rw [hg]; exact hwk) (by rw [hg, upd_ne _ _ h10, upd_ne _ _ h20]; exact hgv)
    (shape_main hu.shape hm (by rw [hg]; exact h1) (by rw [hg]; exact h2) (by rw [hg]; exact h3))
    (fun h => by
      rw [upd_ne _ _ h10, upd_ne _ _ h20]
      obtain ⟨a, b, c, d, f, k⟩ := hdone h
      refine ⟨a, b, c, d, f, fun u hx => ?_⟩
      have e := sx_ne0 hu hx
      rw [upd_ne _ _ e] at hx ⊢; exact k u e hx)
  rw [hg, upd_upd] at hU
  refine ⟨rX, ?_, hU⟩
  have := hL.relabel (t := 0) (g := gO rM x₁) (by rw [hg]; rfl) (by rw [hg]; rfl) (by rw [hg]; rfl)
    fun _ hR => R_upd0 hR
  rwa [upd_upd] at this

/-! ## The wait: `add(1)` and the event wait -/

/-- The group's value with `main` past `pre`. -/
theorem wgv_main {x0 x1 x2 : X} (h : x0.ph ≠ .pre) {b1 b2 : Bool} (h1 : x1.ph.fd = b1)
    (h2 : x2.ph.fd = b2) :
    wgv x0 x1 x2 = 4 + (if x0.ph.wa then 1 else 0) - 2 * (cond b1 1 0 + cond b2 1 0) := by
  unfold wgv X.fdn; rw [if_neg h, h1, h2]; cases b1 <;> cases b2 <;> rfl

/-- **The wait's `add(1)`** at `run` (an acquire RMW): it read 4 or 2 (a task pending: `main` to
`ev`, with the waiter's role `wk`) or 0 (both finished: `main` to `rd`, after both finishes by the
acquire of the release sequence, `gw`). -/
theorem wp_waRmw {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat} {rM : Res}
    (hi : proto.inv (upd G 0 (gO rM { ph := .run })) m)
    {Q : BitVec 64 × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' (old : BitVec 64), m'.current = 0 →
      (old = 0 ∧ proto.inv (upd G₁ 0 (gO rM { ph := .rd })) m') ∨
      ((old = 2 ∨ old = 4) ∧ proto.inv (upd G₁ 0 (gO rM { ph := .ev, wk := true })) m') →
      Q (old, s) G₁ m' k) :
    proto.WP 0 ((atomicRmwC .add false .acquire 8 bPtr (1 : BitVec 64) : CM Tgt σ (BitVec 64)).run s)
      Q G m n := by
  refine FLock.wp_wordRmw fitsE wg_inRest apG hi (hlv := rfl) ?_
  intro k hk G₁ rY m₁ m' old hg₁ hc₁ hU _ hY hv hH hh hacq hw' _ _ _ hA _ _ hL
  have hx₀ : (G₁ 0).2 = { ph := .run } := by rw [hg₁]; rfl
  have hcur : m'.current = 0 := (hA (fun _ => none) (fun _ _ _ => rfl)).current.trans hc₁
  have hgv := hU.gv
  rw [hx₀] at hgv
  have hold := Word.Entry.val_inj hv hgv
  have hnsx : ∀ u, (G₁ u).2.sx = false := fun u => by
    cases e : (G₁ u).2.sx
    · rfl
    · have := (hU.sto u e).2.1; rw [hx₀] at this; cases this
  have hnis : ∀ j < (EV.hist m₁).size, ¬ IsSetW m₁ j := fun j hj hs => by
    obtain ⟨⟨u, hu, -⟩, -⟩ := hU.isw j hj hs; rw [hnsx u] at hu; cases hu
  refine h k hk G₁ m' old hcur ?_
  cases h1 : (G₁ 1).2.ph.fd <;> cases h2 : (G₁ 2).2.ph.fd <;>
    rw [wgv_main (by decide) h1 h2] at hold
  rotate_right
  · -- both finished: to `rd`
    have ho : old = 0 := by rw [hold]; decide
    refine .inl ⟨ho, inv_mainRmw hg₁ hU hY hc₁ hh rfl ?_ hw' hA hL rfl rfl rfl rfl (fun _ => rfl)
      (fun h => by cases h) (fun h => by cases h) rfl (fun h => by simp [Ph.rank] at h)
      (fun h => by cases h) (fun _ => ⟨by decide, by decide⟩) (fun h => by cases h)
      fun _ => ⟨h1, h2, VClock.le_trans (hU.gw 1 h1) (hacq rfl),
        VClock.le_trans (hU.gw 2 h2) (hacq rfl), fun j hj hs => absurd hs (hnis j hj),
        fun u hu => by rw [hnsx u] at hu; cases hu⟩⟩
    rw [wgv_main (by decide) h1 h2]
    refine (congrArg (WG.Holds m') ?_).mp hH
    rw [hold]; decide
  -- a task pending: to `ev`
  all_goals
    have ho : old = 4 ∨ old = 2 := by rw [hold]; decide
    refine .inr ⟨ho.symm, inv_mainRmw hg₁ hU hY hc₁ hh rfl ?_ hw' hA hL rfl rfl rfl rfl
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (fun h => by simp [Ph.rank] at h)
      (fun h => by cases h) (fun _ => ⟨by decide, by decide⟩)
      (fun _ a b => by first | exact absurd (a.symm.trans h1) (by decide) | exact absurd (b.symm.trans h2) (by decide))
      (fun h => by simp [Ph.rank] at h)⟩
    rw [wgv_main (by decide) h1 h2]
    refine (congrArg (WG.Holds m') ?_).mp hH
    rw [hold]; decide

/-- **`main`'s event wait**: the premises `hone` and `hhb` of `EventImpl.wait_wp` (only `main` has
the waiter's role, `wk0`). -/
theorem ewait_ok {G : ThreadId → Gh} {m : Mem} {g : Gh} (hi : proto.inv (upd G 0 g) m) :
    (∀ u, u ≠ 0 → ¬ (E.ph (G u)).Waiting) ∧
    (∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[0]!) = true) := by
  obtain ⟨rX, -, hu⟩ := hi
  refine ⟨fun u hu0 hw => ?_, fun j hj hv => ?_⟩
  · have hx := hu.einv.wx u (by rw [upd_ne _ _ hu0]; exact hw)
    exact hu0 (hu.wk0 u hx).1
  · obtain ⟨u, hx, hle⟩ := hu.einv.wby j hj hv
    obtain rfl := (hu.wk0 u hx).1
    exact hle

/-- **`main`'s sleep at the event is no deadlock** (`hlive` of `EventImpl.wait_wp`): if every task
ended, both finished and one read 3 (`last3`), whose end set the event (`sfin`); a task asleep at
a futex waits at none (the mutex: `Fits.noWaits`; the event: only `main` waits there). -/
theorem ewait_live (G₁ : ThreadId → Gh) (m₁ : Mem) (hw : E.ph (G₁ 0) = .w1)
    (_ : L.ph (G₁ 0) = .away) (hi : proto.inv G₁ m₁) (hs : ¬ E.IsSet m₁) :
    proto.Live 0 G₁ m₁ := by
  intro _ hall
  obtain ⟨rX, hL, hu⟩ := hi
  have hwk : (G₁ 0).2.wk = true := hu.einv.wx 0 (.inr hw)
  have hwa := (hu.wk0 0 hwk).2
  obtain ⟨hsz, ht1, ht2⟩ : m₁.threads.size = 3 ∧ (G₁ 1).2.ph.isTask = true ∧
      (G₁ 2).2.ph.isTask = true := by
    obtain ⟨-, -, -, ⟨-, h0, -⟩ | ⟨-, h0, -⟩ | ⟨h3, -, h1, h2, -⟩⟩ := hu.shape
    · exfalso
      have h0' : (G₁ 0).2.ph.rank ≤ 1 := h0
      revert h0' hwa; generalize (G₁ 0).2.ph = p; cases p <;> decide
    · exfalso
      have h0' : (G₁ 0).2.ph = .sp1 := h0
      rw [h0'] at hwa; cases hwa
    · exact ⟨h3, h1, h2⟩
  have hfin : ∀ u, (u = 1 ∨ u = 2) → (G₁ u).2.ph = .fin := fun u hu12 => by
    have htk : (G₁ u).2.ph.isTask = true := by rcases hu12 with rfl | rfl <;> assumption
    rcases hall u (by rw [hsz]; rcases hu12 with rfl | rfl <;> decide) with h | h | h
    · exact h.2.1
    · exfalso
      obtain ⟨w, hw', he⟩ := Array.any_eq_true'.mp h
      have e : w.1 = u := by simpa using he
      rcases hu.q w hw' with hq | hq
      · exact fitsL.noWaits hL hu hall (Array.any_eq_true'.mpr ⟨w, hw', by simp [hq]⟩)
      · have h1 := (hu.einv.q w hw' hq).1
        have := (hu.wk0 w.1 (hu.einv.wx w.1 (.inr h1))).1
        rw [e] at this; rcases hu12 with rfl | rfl <;> cases this
    · exfalso
      obtain ⟨-, hr, -⟩ := h
      rcases hr with hr | hr <;> rw [hr] at htk <;> cases htk
  have h1 := hfin 1 (.inl rfl)
  have h2 := hfin 2 (.inr rfl)
  obtain ⟨u, hx⟩ := hu.last3 hwk (by rw [h1]; rfl) (by rw [h2]; rfl)
  rcases (hu.sto u hx).1 with rfl | rfl
  · exact hs (hu.sfin _ hx h1)
  · exact hs (hu.sfin _ hx h2)

/-- **`main` after its wait** (`ev` → `rd`): the event is set, so the setter read 3 and both
tasks finished below its `is_set` write (`isw`), the only one (`one`), which `main` synchronized
with (`FEvent.Inv.synced_first`). -/
theorem inv_rd {G : ThreadId → Gh} {m : Mem} {rM : Res}
    (hi : proto.inv (upd G 0 (gO rM { ph := .ev, wk := true })) m) (hs : E.IsSet m)
    (hy : E.Synced 0 m) : proto.inv (upd G 0 (gO rM { ph := .rd, wk := true })) m := by
  obtain ⟨rX, -, hu⟩ := id hi
  have h10 : (1 : ThreadId) ≠ 0 := by decide
  have h20 : (2 : ThreadId) ≠ 0 := by decide
  have hpos := FEvent.hist_pos hu.ev
  have hfirst : ∀ j < (EV.hist m).size, IsSetW m j →
      ∀ i < j, ¬ (EV.hist m)[i]!.Val (2 : BitVec 32) :=
    fun j hj hsj i hij hv => by have := hu.one i (by omega) j hj hv hsj; omega
  have hle : ∀ j < (EV.hist m).size, IsSetW m j →
      VClock.le (EV.hist m)[j]!.clock (m.clocks[0]!) = true :=
    fun j hj hsj => hu.einv.synced_first hy hj hsj (hfirst j hj hsj)
  have hlast : IsSetW m ((EV.hist m).size - 1) := hs
  obtain ⟨⟨u, hxu, hSu⟩, hc1, hc2⟩ := hu.isw _ (by omega) hlast
  obtain ⟨-, -, hf1, hf2, -⟩ := hu.sto u hxu
  rw [upd_ne _ _ h10] at hc1 hf1
  rw [upd_ne _ _ h20] at hc2 hf2
  have hu0 : u ≠ 0 := sx_ne0 hu hxu
  refine inv_main0 hi rfl rfl rfl rfl rfl
    (by simp [wgv, Ph.wa]) rfl
    (fun h => by simp [Ph.rank] at h) (fun h => by cases h) (fun _ => ⟨by decide, by decide⟩)
    fun _ => ⟨hf1, hf2, VClock.le_trans hc1 (hle _ (by omega) hlast),
      VClock.le_trans hc2 (hle _ (by omega) hlast), hle, fun v hv0 hxv => ?_⟩
  have hxv' : (upd G 0 (gO rM { ph := .ev, wk := true }) v).2.sx = true := by
    rw [upd_ne _ _ hv0]; exact hxv
  obtain rfl := hu.sx1 v u hxv' hxu
  rw [upd_ne _ _ hu0] at hSu
  exact hSu

section Sync

variable (ei : EventImpl Tgt)

/-- **`main`'s event wait** at `ev`: to `rd`. -/
theorem wp_ewait {p : Ptr} (hp : p = EV.ptr) (io : Io) {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {rM : Res} (hpl : rM.Plain) (hi : proto.inv (upd G 0 (gO rM { ph := .ev, wk := true })) m) :
    proto.WP 0 (ei.wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = 0 ∧
      proto.inv (upd G' 0 (gO rM { ph := .rd, wk := true })) m') G m d := by
  obtain ⟨hone, hhb⟩ := ewait_ok hi
  exact WP.mono (fun _ _ _ _ ⟨hd, hc, hs, hy, hi'⟩ => ⟨hd, hc, inv_rd hi' hs hy⟩)
    (ei.wait_wp fitsE rfl hp 0 (gO rM { ph := .ev, wk := true }) rfl rfl rfl io G m d hone hhb
      ewait_live hpl hi)

end Sync

set_option maxHeartbeats 800000 in
/-- **`main`'s `wait`** on the group at `run`: to `rd`, with the waiter's role if its `add(1)`
read a pending task. -/
theorem wp_wgWait [Zig.Os.HasEnv] {G : ThreadId → Gh} {m : Mem} {d : Nat} {rM : Res}
    (hpl : rM.Plain) (hi : proto.inv (upd G 0 (gO rM { ph := .run })) m) :
    proto.WP 0 (Thread_WaitGroup_wait bPtr) (fun _ G' m' d' => d' < d ∧ m'.current = 0 ∧
      ∃ w, proto.inv (upd G' 0 (gO rM { ph := .rd, wk := w })) m') G m d := by
  unfold Thread_WaitGroup_wait
  fsym [wp_waRmw, debug_assert, WP.liftMem_pure (projI _ _) rfl,
    wp_ewait resetEvent rfl ⟨⟩ hpl]

end Threadsync.WG
