import Proofs.Sync.Mailbox.Protocol

/-!
# The mailbox's semaphore operations and the producer's places

The premises of the semaphore's contract (`SemImpl.wait_wp`, `SemImpl.post_wp`) for the mailbox's
protocol (`Proofs/Sync/Mailbox/Protocol.lean`), for every implementation `I : SemImpl Tgt`:

- **`main`'s wait** (`wp_waitM`): `main` is the waiting role (`wt`) and takes the permit to `got`;
  the count goes from 1 to 0 and the pool's message (`Msg 2`) moves into its part. Only `main`
  registers at the condition (`hroom`), and its sleep at count 0 is no deadlock: the producer has
  not posted, so it has not ended, and it sleeps at no futex (`wait_live`).
- **The producer's post** (`wp_postP`): it gives the written message to the pool (`pr 2` to `pd`):
  `main` has not taken the permit (the producer has not posted), so the count goes from 0 to 1.

The program places move out of the sync code with `inv_move` (the producer's writes, its end,
`main`'s join).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Sync.Mailbox

variable {K : Cfg}

/-! ## The count and the pool -/

theorem pv_took {Y : ThreadId → Ph} (h : (Y 0).took = true) : pv Y = 0 := by
  simp [pv, avail, h]

theorem pv_npost {Y : ThreadId → Ph} (h : (Y 1).posted = false) : pv Y = 0 := by
  simp [pv, avail, h]

theorem pv_one {Y : ThreadId → Ph} (h : avail Y = true) : pv Y = 1 := by simp [pv, h]

theorem avail_of_pv {Y : ThreadId → Ph} (h : pv Y ≠ 0) : avail Y = true := by
  cases ha : avail Y <;> simp_all [pv]

theorem pool_on {Y : ThreadId → Ph} (h : avail Y = true) : Pool Y = Msg 2 := by simp [Pool, h]

theorem pool_off {Y : ThreadId → Ph} (h : avail Y = false) : Pool Y = emp := by simp [Pool, h]

/-- `R` reads the permit's availability only. -/
theorem R_avail {Y Y' : ThreadId → X}
    (h : avail (fun u => (Y' u).ph) = avail (fun u => (Y u).ph)) : R Y' = R Y := by
  unfold R pv Pool; rw [h]

theorem upd0_1 (G : ThreadId → Gh) (g : Gh) : upd G 0 g 1 = G 1 := upd_ne _ _ (by decide)
theorem upd1_0 (G : ThreadId → Gh) (g : Gh) : upd G 1 g 0 = G 0 := upd_ne _ _ (by decide)

/-! ## The threads' shape -/

/-- `main` took the permit only after the producer posted. -/
theorem Shape.took {Y : ThreadId → X} {m : Mem} (h : Shape Y m) (ht : (Y 0).ph.took = true) :
    (Y 1).ph.posted = true := by
  obtain ⟨-, ⟨-, hy, -⟩ | ⟨-, -, -, -, -, htk, -⟩⟩ := h
  · rw [hy] at ht; cases ht
  · exact htk ht

/-- After the spawn, the producer is at a producer's place. -/
theorem Shape.prodPh {Y : ThreadId → X} {m : Mem} (h : Shape Y m) (h0 : (Y 0).ph ≠ .pre) :
    (Y 1).ph.isProd = true ∧ m.threads.size = 2 := by
  obtain ⟨-, ⟨-, hy, -⟩ | ⟨hs, -, -, -, hp, -⟩⟩ := h
  · exact absurd hy h0
  · exact ⟨hp, hs⟩

/-- **`main` moves** past its spawn (`main` may take the permit only after the producer's post). -/
theorem Shape.main {Y Y' : ThreadId → X} {m : Mem} (h : Shape Y m) (hpre : (Y 0).ph ≠ .pre)
    (h0 : (Y' 0).ph.isMain = true) (h0' : (Y' 0).ph ≠ .pre)
    (htk : (Y' 0).ph.took = true → (Y 1).ph.posted = true) (hu : ∀ u, u ≠ 0 → Y' u = Y u) :
    Shape Y' m := by
  obtain ⟨h00, ⟨-, hy, -⟩ | ⟨hs, h1, -, -, hp, -, hrest⟩⟩ := h
  · exact absurd hy hpre
  · refine ⟨h00, .inr ⟨hs, h1, h0, h0', by rw [hu 1 (by decide)]; exact hp,
      fun ht => by rw [hu 1 (by decide)]; exact htk ht, fun u hu' => ?_⟩⟩
    rw [hu u (by simp only [ThreadId] at *; omega)]; exact hrest u hu'

/-- **The producer moves** (`main` took the permit only after the producer's post). -/
theorem Shape.prod {Y Y' : ThreadId → X} {m : Mem} (h : Shape Y m) (hp : (Y 1).ph.isProd = true)
    (h1 : (Y' 1).ph.isProd = true) (htk : (Y 0).ph.took = true → (Y' 1).ph.posted = true)
    (hu : ∀ u, u ≠ 1 → Y' u = Y u) : Shape Y' m := by
  obtain ⟨h00, ⟨-, -, hy⟩ | ⟨hs, h1', hm, hnp, -, -, hrest⟩⟩ := h
  · rw [hy 1 (Nat.le_refl _)] at hp; cases hp
  · refine ⟨h00, .inr ⟨hs, h1', by rw [hu 0 (by decide)]; exact hm,
      by rw [hu 0 (by decide)]; exact hnp, h1, fun ht => htk (by rw [← hu 0 (by decide)]; exact ht),
      fun u hu' => ?_⟩⟩
    rw [hu u (by simp only [ThreadId] at *; omega)]; exact hrest u hu'

/-! ## Moves out of the sync code -/

/-- A thread out of the condition's code gets another ghost value out of it, at the same memory
(`FCond.Inv.frame`). -/
theorem cinv_out {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh}
    (hI : C.Inv (L K) G m) (h₀ : (G t).2.c = .out) (h₁ : g.2.c = .out) :
    C.Inv (L K) (upd G t g) m := by
  have hcg : C.ph g = .out := h₁
  have hct : C.ph (G t) = .out := h₀
  refine hI.frame rfl rfl rfl (fun w hw _ _ => hw) (Nat.le_refl _) (fun _ => VClock.le_refl _)
    (fun h => by rw [hcg, hct] at h; rcases h with h | h <;> cases h)
    (fun _ _ h => by rw [hcg] at h; cases h) (fun _ _ _ _ h => by rw [hcg] at h; cases h)
    (fun h => by obtain ⟨_, _, _, h'⟩ := hI.qd_reg h; rw [hct] at h'; cases h')
    (fun h => by rw [hcg] at h; cases h) (fun h => by rw [hcg] at h; cases h)
    (fun h => absurd hcg h)
    (hI.cnt_frame rfl rfl (fun _ => rfl) (fun _ _ _ h => h) (by rw [hcg, hct]) (by rw [hcg, hct])
      (by simp [FCond.cl, hcg, hct, FCond.regCl, CPh.incN]))

/-- **A move of thread `t`'s program place** out of the condition's and the semaphore's code, at
the same memory: its lock place stays or it ends (`out` to `gone`), and the permit's
availability stays. -/
theorem U_move {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {g₀ g₁ : Gh}
    (hu : U K (upd G t g₀) rX m) (hc₀ : g₀.2.c = .out) (hc₁ : g₁.2.c = .out)
    (hs₀ : g₀.2.s = .out) (hs₁ : g₁.2.s = .out)
    (hl : g₁.1.ph = g₀.1.ph ∨ g₀.1.ph = .out ∧ g₁.1.ph = .gone)
    (hav : avail (fun u => (upd G t g₁ u).2.ph) = avail (fun u => (upd G t g₀ u).2.ph))
    (shape : Shape (fun u => (upd G t g₁ u).2) m) : U K (upd G t g₁) rX m := by
  have hcu : ∀ u, (upd G t g₁ u).2.c = (upd G t g₀ u).2.c := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, upd_self, hc₀, hc₁]
    · rw [upd_ne _ _ e, upd_ne _ _ e]
  have hsu : ∀ u, (upd G t g₁ u).2.s = (upd G t g₀ u).2.s := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, upd_self, hs₀, hs₁]
    · rw [upd_ne _ _ e, upd_ne _ _ e]
  have hhold : ∀ u, (L K).ph (upd G t g₀ u) = .holds → (L K).ph (upd G t g₁ u) = .holds ∨
      ∀ c, VClock.le c (m.clocks[u]!) = true → (L K).Before m c := fun u h => by
    by_cases e : u = t
    · subst e
      rw [upd_self] at h ⊢
      rcases hl with hl | ⟨hl, -⟩
      · exact .inl (by show g₁.1.ph = _; rw [hl]; exact h)
      · exact absurd (h.symm.trans hl) (by decide)
    · rw [upd_ne _ _ e] at h ⊢; exact .inl h
  have hgone : ∀ u, (L K).ph (upd G t g₁ u) ≠ .gone → (L K).ph (upd G t g₀ u) ≠ .gone :=
    fun u h => by
      by_cases e : u = t
      · subst e
        rw [upd_self] at h ⊢
        rcases hl with hl | ⟨-, hl⟩
        · show g₀.1.ph ≠ .gone; rw [← hl]; exact h
        · exact absurd hl h
      · rw [upd_ne _ _ e] at h ⊢; exact h
  have hI := cinv_out (t := t) (g := g₁) hu.cinv (by rw [upd_self]; exact hc₀) hc₁
  rw [upd_upd] at hI
  have hS : (S K).Inv (upd G t g₁) m :=
    hu.sinv.mono hsu hcu
      (by
        show pv (fun u => (upd G t g₁ u).2.ph) = pv (fun u => (upd G t g₀ u).2.ph)
        unfold pv; rw [hav])
      (fun u h => by
        by_cases e : u = t
        · rw [e] at h
          have h' : ((upd G t g₀ t).2.s).isPst = true := h
          rw [upd_self, hs₀] at h'; cases h'
        · rw [upd_ne _ _ e]; have := hu.sinv.pst u h; rwa [upd_ne _ _ e] at this)
      hhold (fun _ => VClock.le_refl _) (fun _ h => h) rfl hgone (fun _ hw => .inl hw) rfl
  refine hu.congr (fun u i e h => by rwa [hcu] at h) (fun u i jr sn e h => by rwa [hcu] at h)
    (fun u q n h' h => by rwa [hcu] at h) rfl rfl shape hu.rest hu.blk hu.ws hu.we hI hS
    (fun u h => ?_) (fun c h => h.mono hhold (fun _ => VClock.le_refl _) (fun _ h => h) rfl hgone)
    hu.q
  by_cases e : u = t
  · subst e; rw [upd_self, hs₁] at h; cases h
  · rw [upd_ne _ _ e] at h ⊢; have := hu.swt u; rw [upd_ne _ _ e] at this; exact this h

/-- **A move of thread `t`'s program place** (`U_move`): the protocol's invariant. -/
theorem inv_move {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g₀ g₁ : Gh}
    (hi : (proto K).inv (upd G t g₀) m) (hc₀ : g₀.2.c = .out) (hc₁ : g₁.2.c = .out)
    (hs₀ : g₀.2.s = .out) (hs₁ : g₁.2.s = .out)
    (hl : g₁.1 = g₀.1 ∨ g₀.1.ph = .out ∧ g₁.1 = ⟨.gone, g₀.1.part, rnil⟩)
    (hav : avail (fun u => (upd G t g₁ u).2.ph) = avail (fun u => (upd G t g₀ u).2.ph))
    (shape : ∀ rX, U K (upd G t g₀) rX m → Shape (fun u => (upd G t g₁ u).2) m) :
    (proto K).inv (upd G t g₁) m := by
  obtain ⟨rX, hL, hu⟩ := hi
  have hRk : ∀ r, (L K).R (upd G t g₀) r → (L K).R (upd (upd G t g₀) t g₁) r := fun r hR => by
    rw [upd_upd]
    show R (fun u => (upd G t g₁ u).2) r
    rw [R_avail (Y := fun u => (upd G t g₀ u).2) hav]; exact hR
  have hL' : (L K).Inv (upd (upd G t g₀) t g₁) rX m := by
    rcases hl with hl | ⟨h0, hl⟩
    · exact hL.relabel (by rw [upd_self]; show g₁.1.ph = g₀.1.ph; rw [hl])
        (by rw [upd_self]; show g₁.1.part = g₀.1.part; rw [hl])
        (by rw [upd_self]; show g₁.1.held = g₀.1.held; rw [hl]) hRk
    · refine hL.ghost (by rw [upd_self]; exact h0) (.inr (.inl (by show g₁.1.ph = _; rw [hl])))
        (by rw [upd_self]; show g₁.1.part = g₀.1.part; rw [hl]) (by show g₁.1.held = _; rw [hl])
        (fun h => absurd (by show g₁.1.ph = _; rw [hl]) h) hRk
  rw [upd_upd] at hL'
  refine ⟨rX, hL', U_move hu hc₀ hc₁ hs₀ hs₁ ?_ hav (shape rX hu)⟩
  rcases hl with hl | ⟨h0, hl⟩
  · exact .inl (by rw [hl])
  · exact .inr ⟨h0, by rw [hl]⟩

/-! ## The producer's places -/

/-- **The producer writes** a field of its message: from `pr k` to `pr k'`. -/
theorem inv_pr {G : ThreadId → Gh} {m : Mem} {r : Res} {k k' : Nat}
    (hi : (proto K).inv (upd G 1 (gO r { ph := .pr k })) m) :
    (proto K).inv (upd G 1 (gO r { ph := .pr k' })) m :=
  inv_move hi rfl rfl rfl rfl (.inl rfl) (by simp [avail, upd_self, gO, Ph.posted])
    fun rX hu => by
      have hs := hu.shape
      refine hs.prod (by show (upd G 1 _ 1).2.ph.isProd = true; rw [upd_self]; rfl)
        (by show (upd G 1 _ 1).2.ph.isProd = true; rw [upd_self]; rfl) (fun ht => ?_)
        (fun _ e => upd_ne₂ e)
      have := hs.took ht
      simp [upd_self, gO, Ph.posted] at this

/-- **The producer's end** after its post: it is `gone` at `fin`. -/
theorem inv_fin {G : ThreadId → Gh} {m : Mem} {r : Res}
    (hi : (proto K).inv (upd G 1 (gO r { ph := .pd })) m) :
    (proto K).inv (upd G 1 (⟨.gone, r, rnil⟩, { ph := .fin })) m :=
  inv_move hi rfl rfl rfl rfl (.inr ⟨rfl, rfl⟩) (by simp [avail, upd_self, upd1_0, gO, Ph.posted])
    fun rX hu => by
      refine hu.shape.prod (by show (upd G 1 _ 1).2.ph.isProd = true; rw [upd_self]; rfl)
        (by show (upd G 1 _ 1).2.ph.isProd = true; rw [upd_self]; rfl)
        (fun _ => by show (upd G 1 _ 1).2.ph.posted = true; rw [upd_self]; rfl)
        (fun _ e => upd_ne₂ e)

/-! ## No deadlock -/

/-- **`main`'s sleep at the condition at count 0 is no deadlock** (`hlive` of `SemImpl.wait_wp`):
`main` waits at the semaphore, so it is past its spawn and has not taken the permit; at count 0
the producer has not posted, so it has not ended, it does not join, and it sleeps at no futex
(at the mutex, `Fits.noWaits`; at the epoch it would be a registered waiter, `U.waits0`). -/
theorem wait_live (G₁ : ThreadId → Gh) (m₁ : Mem)
    (hreg : ∃ i jr e, C.ph (G₁ 0) = .reg i jr false e) (_ : (L K).ph (G₁ 0) = .away)
    (hi : (proto K).inv G₁ m₁) (_ : FCond.sOf (C.lastS m₁) = 0) (_ : ∀ v, (C.ph (G₁ v)).sig = false)
    (hcnt : (S K).cnt G₁ = 0) : (proto K).Live 0 G₁ m₁ := by
  intro _ hall
  obtain ⟨rX, hL, hu⟩ := hi
  obtain ⟨i, jr, e, hr⟩ := hreg
  have hw0 : ((G₁ 0).2.c).waits = true := by show (C.ph (G₁ 0)).waits = true; rw [hr]; rfl
  have hwt : (G₁ 0).2.ph = .wt := hu.swt 0 (hu.sinv.wt 0 hw0)
  obtain ⟨hp, hs⟩ := hu.shape.prodPh (Y := fun u => (G₁ u).2) (by show (G₁ 0).2.ph ≠ _; rw [hwt]; nofun)
  have hnp : (G₁ 1).2.ph.posted = false := by
    cases h : (G₁ 1).2.ph.posted
    · rfl
    · have : pv (fun u => (G₁ u).2.ph) = 1 :=
        pv_one (by simp [avail, h, hwt, Ph.took])
      have h' : pv (fun u => (G₁ u).2.ph) = 0 := hcnt
      rw [this] at h'; exact absurd h' (by decide)
  rcases hall 1 (by rw [hs]; decide) with h | h | h
  · have : (G₁ 1).2.ph = .fin := by rw [h.2]
    rw [this] at hnp; cases hnp
  · obtain ⟨w, hw, he⟩ := Array.any_eq_true'.mp h
    have e1 : w.1 = 1 := by simpa using he
    rcases hu.q w hw with hq | hq
    · exact (fitsL (K := K)).noWaits hL hall (Array.any_eq_true'.mpr ⟨w, hw, by simp [hq]⟩)
    · obtain ⟨i', jr', e', h1, -⟩ := hu.cinv.q w hw hq
      have hw1 : ((G₁ w.1).2.c).waits = true := by
        show (C.ph (G₁ w.1)).waits = true; rw [h1]; rfl
      have := hu.waits0 hw1
      rw [e1] at this; cases this
  · have : (G₁ 1).2.ph = .joins := by rw [h.2]
    rw [this] at hp; cases hp

/-! ## `main`'s wait -/

section Wait

variable {rM : Res}

/-- `main` at the semaphore's wait, and after its take. -/
abbrev gW (rM : Res) : Gh := gO rM { ph := .wt }
abbrev gT (rM : Res) : Gh := gO rM { ph := .got }

theorem wait_cnt : ∀ (G : ThreadId → Gh) rL m,
    (proto K).inv (upd G 0 ((L K).set ((S K).set (gW rM) .wt) .holds rL)) m →
    (S K).cnt (upd G 0 (gW rM)) ≠ 0 →
    (S K).cnt (upd G 0 ((fun _ => gT rM) ((S K).xs (upd G 0 (gW rM))))) =
      (S K).cnt (upd G 0 (gW rM)) - 1 := by
  intro G _ _ _ hne
  have ha : avail (fun u => (upd G 0 (gW rM) u).2.ph) = true := avail_of_pv hne
  have h1 : pv (fun u => (upd G 0 (gW rM) u).2.ph) = 1 := pv_one ha
  show pv (fun u => (upd G 0 (gT rM) u).2.ph) = pv (fun u => (upd G 0 (gW rM) u).2.ph) - 1
  rw [h1, pv_took (by simp [upd_self, gO, Ph.took])]; decide

theorem wait_pool : ∀ (G : ThreadId → Gh) rL m,
    (proto K).inv (upd G 0 ((L K).set ((S K).set (gW rM) .wt) .holds rL)) m →
    (S K).cnt (upd G 0 (gW rM)) ≠ 0 → ∀ r, (S K).Pool ((S K).xs (upd G 0 (gW rM))) r →
    ((S K).Pool ((S K).xs (upd G 0 ((fun _ => gT rM) ((S K).xs (upd G 0 (gW rM)))))) ⋆
      (fun _ => Msg 2) ((S K).xs (upd G 0 (gW rM)))) r := by
  intro G _ _ _ hne r hr
  have hr' : Pool (fun u => (upd G 0 (gW rM) u).2.ph) r := hr
  have ha : avail (fun u => (upd G 0 (gW rM) u).2.ph) = true := avail_of_pv hne
  rw [pool_on ha] at hr'
  show (Pool (fun u => (upd G 0 (gT rM) u).2.ph) ⋆ Msg 2) r
  rw [pool_off (by simp [avail, upd_self, gO, Ph.took])]
  exact sep_comm (Full.sep_emp.mpr hr')

theorem wait_U : ∀ (G : ThreadId → Gh) rX m h₁ h₂ r sh sc, (S K).cnt (upd G 0 (gW rM)) ≠ 0 →
    (fun _ => Msg 2) ((S K).xs (upd G 0 (gW rM))) r → FHeap.Disjoint ((L K).part (gW rM)).heap r.heap →
    U K (upd G 0 ((S K).set ((L K).set (gW rM) .holds h₁) (.pst sh sc))) rX m →
    (L K).Inv (upd G 0 ((S K).set ((L K).set ((L K).setPart
      ((fun _ => gT rM) ((S K).xs (upd G 0 (gW rM)))) (rsum ((L K).part (gW rM)) r)) .holds h₂)
      (.pst sh sc))) rX m →
    (S K).Inv (upd G 0 ((S K).set ((L K).set ((L K).setPart
      ((fun _ => gT rM) ((S K).xs (upd G 0 (gW rM)))) (rsum ((L K).part (gW rM)) r)) .holds h₂)
      (.pst sh sc))) m →
    C.Inv (L K) (upd G 0 ((S K).set ((L K).set ((L K).setPart
      ((fun _ => gT rM) ((S K).xs (upd G 0 (gW rM)))) (rsum ((L K).part (gW rM)) r)) .holds h₂)
      (.pst sh sc))) m →
    U K (upd G 0 ((S K).set ((L K).set ((L K).setPart
      ((fun _ => gT rM) ((S K).xs (upd G 0 (gW rM)))) (rsum ((L K).part (gW rM)) r)) .holds h₂)
      (.pst sh sc))) rX m := by
  intro G rX m h₁ h₂ r sh sc hne _ _ hu _ hS hC
  have hp1 : (G 1).2.ph.posted = true := by
    have : avail (fun u => (upd G 0 (gW rM) u).2.ph) = true := avail_of_pv hne
    simp only [avail, Bool.and_eq_true] at this
    have h := this.1; rwa [upd0_1] at h
  refine hu.xMove (fun u => ?_) (fun u => ?_) ?_ hC hS (fun u h => ?_)
  · by_cases e : u = 0
    · subst e; rw [upd_self, upd_self]; rfl
    · rw [upd_ne _ _ e, upd_ne _ _ e]
  · by_cases e : u = 0
    · subst e; rw [upd_self, upd_self]; rfl
    · rw [upd_ne _ _ e, upd_ne _ _ e]
  · refine hu.shape.main (by show (upd G 0 _ 0).2.ph ≠ _; rw [upd_self]; nofun)
      (by show (upd G 0 _ 0).2.ph.isMain = true; rw [upd_self]; rfl)
      (by show (upd G 0 _ 0).2.ph ≠ _; rw [upd_self]; nofun)
      (fun _ => by show (upd G 0 _ 1).2.ph.posted = true; rw [upd0_1]; exact hp1)
      (fun _ e => upd_ne₂ e)
  · by_cases e : u = 0
    · subst e; rw [upd_self] at h; cases h
    · rw [upd_ne _ _ e] at h ⊢; have := hu.swt u; rw [upd_ne _ _ e] at this; exact this h

theorem wait_room : ∀ (G₁ : ThreadId → Gh) rL m₁,
    (proto K).inv (upd G₁ 0 ((L K).set ((S K).set (gW rM) .wt) .holds rL)) m₁ →
    (S K).cnt (upd G₁ 0 (gW rM)) = 0 → ∀ n, (∀ u, n ≤ u → C.ph (upd G₁ 0 (gW rM) u) = .out) →
    C.nreg (upd G₁ 0 (gW rM)) n < 65535 := by
  intro G₁ rL m₁ hi _ n _
  obtain ⟨rX, -, hu⟩ := hi
  rw [FCond.nreg_congr (G := upd G₁ 0 ((L K).set ((S K).set (gW rM) .wt) .holds rL)) (fun u => by
    by_cases e : u = 0
    · subst e; rw [upd_self, upd_self]; rfl
    · rw [upd_ne _ _ e, upd_ne _ _ e])]
  exact Nat.lt_of_le_of_lt (hu.nreg_le n) (by decide)

/-- **`main`'s wait** (`SemImpl.wait_wp`): it takes the permit and the message, to `got`. -/
theorem wp_waitM (I : SemImpl Tgt) (hLc : K.c = I.c) (io : Io) {G : ThreadId → Gh} {m : Mem}
    {d : Nat} (hpl : rM.Plain) (hi : (proto K).inv (upd G 0 (gO rM { ph := .wt })) m)
    (hc : m.current = 0) :
    (proto K).WP 0 (I.wait cPtr io) (fun _ G' m' d' => d' < d ∧ m'.current = 0 ∧ ∃ r, Msg 2 r ∧
      FHeap.Disjoint rM.heap r.heap ∧
      (proto K).inv (upd G' 0 (gO (rsum rM r) { ph := .got })) m') G m d :=
  WP.mono (fun _ _ _ _ ⟨hd, hc', _, r, hT, hdj, hi'⟩ => ⟨hd, hc', r, hT, hdj, hi'⟩)
    (I.wait_wp (fitsS (K := K)) rfl hLc rfl 0 (gW rM) (fun _ => gT rM) (fun _ => Msg 2)
      rfl rfl rfl rfl ⟨rfl, .inl rfl⟩ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => ⟨rfl, .inl rfl⟩) wait_cnt wait_pool wait_U wait_room wait_live io G m d hpl hi hc)

end Wait

/-! ## The producer's post -/

section Post

variable {rp rc : Res}

/-- The producer before its post, and after it. -/
abbrev gP (rp rc : Res) : Gh := gO (rsum rp rc) { ph := .pr 2 }
abbrev gD (rp : Res) : Gh := gO rp { ph := .pd }

/-- Before its post `main` has not taken the permit. -/
theorem untaken {G : ThreadId → Gh} {g : Gh} {m : Mem} (hi : (proto K).inv (upd G 1 g) m)
    (hg : g.2.ph.posted = false) : (G 0).2.ph.took = false := by
  obtain ⟨rX, -, hu⟩ := hi
  cases h : (G 0).2.ph.took
  · rfl
  · have := hu.shape.took (Y := fun u => (upd G 1 g u).2) (by show (upd G 1 g 0).2.ph.took = _; rw [upd1_0]; exact h)
    simp only [upd_self] at this; rw [hg] at this; cases this

theorem post_cnt : ∀ (G : ThreadId → Gh) rL m,
    (proto K).inv (upd G 1 ((L K).set (gP rp rc) .holds rL)) m →
    (S K).cnt (upd G 1 (gD rp)) = (S K).cnt (upd G 1 (gP rp rc)) + 1 ∧
      ((S K).cnt (upd G 1 (gP rp rc))).toNat + 1 < 2 ^ 64 := by
  intro G _ _ hi
  have h0 := untaken hi rfl
  show pv (fun u => (upd G 1 (gD rp) u).2.ph) = pv (fun u => (upd G 1 (gP rp rc) u).2.ph) + 1 ∧
    (pv (fun u => (upd G 1 (gP rp rc) u).2.ph)).toNat + 1 < 2 ^ 64
  rw [pv_npost (Y := fun u => (upd G 1 (gP rp rc) u).2.ph) (by simp [upd_self, gO, Ph.posted]),
    pv_one (Y := fun u => (upd G 1 (gD rp) u).2.ph)
      (by simp [avail, upd_self, upd1_0, gO, Ph.posted, h0])]
  decide

theorem post_pool (hm : Msg 2 rc) : ∀ (G : ThreadId → Gh) rL m,
    (proto K).inv (upd G 1 ((L K).set (gP rp rc) .holds rL)) m → ∀ r,
    ((fun r => r = rc) ⋆ (S K).Pool ((S K).xs (upd G 1 (gP rp rc)))) r →
    (S K).Pool ((S K).xs (upd G 1 (gD rp))) r := by
  intro G _ _ hi r hr
  have h0 := untaken hi rfl
  have hr' : ((fun r => r = rc) ⋆ Pool (fun u => (upd G 1 (gP rp rc) u).2.ph)) r := hr
  rw [pool_off (by simp [avail, upd_self, gO, Ph.posted]), Full.sep_emp] at hr'
  show Pool (fun u => (upd G 1 (gD rp) u).2.ph) r
  rw [pool_on (by simp [avail, upd_self, upd1_0, gO, Ph.posted, h0]), hr']
  exact hm

theorem post_U : ∀ (G : ThreadId → Gh) rX m h₁ h₂ sh sc,
    U K (upd G 1 ((S K).set ((L K).set (gP rp rc) .holds h₁) (.pst sh sc))) rX m →
    (L K).Inv (upd G 1 ((S K).set ((L K).set (gD rp) .holds h₂) (.pst sh sc))) rX m →
    (S K).Inv (upd G 1 ((S K).set ((L K).set (gD rp) .holds h₂) (.pst sh sc))) m →
    C.Inv (L K) (upd G 1 ((S K).set ((L K).set (gD rp) .holds h₂) (.pst sh sc))) m →
    U K (upd G 1 ((S K).set ((L K).set (gD rp) .holds h₂) (.pst sh sc))) rX m := by
  intro G rX m h₁ h₂ sh sc hu _ hS hC
  refine hu.xMove (fun u => ?_) (fun u => ?_) ?_ hC hS (fun u h => ?_)
  · by_cases e : u = 1
    · subst e; rw [upd_self, upd_self]; rfl
    · rw [upd_ne _ _ e, upd_ne _ _ e]
  · by_cases e : u = 1
    · subst e; rw [upd_self, upd_self]; rfl
    · rw [upd_ne _ _ e, upd_ne _ _ e]
  · refine hu.shape.prod (by show (upd G 1 _ 1).2.ph.isProd = true; rw [upd_self]; rfl)
      (by show (upd G 1 _ 1).2.ph.isProd = true; rw [upd_self]; rfl)
      (fun _ => by show (upd G 1 _ 1).2.ph.posted = true; rw [upd_self]; rfl)
      (fun _ e => upd_ne₂ e)
  · by_cases e : u = 1
    · subst e; rw [upd_self] at h; cases h
    · rw [upd_ne _ _ e] at h ⊢; have := hu.swt u; rw [upd_ne _ _ e] at this; exact this h

/-- **The producer's post** (`SemImpl.post_wp`): it gives the message to the pool, to `pd`. -/
theorem wp_postP (I : SemImpl Tgt) (hLc : K.c = I.c) (io : Io) {G : ThreadId → Gh} {m : Mem}
    {d : Nat} (hpl : rp.Plain) (hm : Msg 2 rc) (hdj : FHeap.Disjoint rp.heap rc.heap)
    (hi : (proto K).inv (upd G 1 (gO (rsum rp rc) { ph := .pr 2 })) m) (hc : m.current = 1) :
    (proto K).WP 1 (I.post cPtr io) (fun _ G' m' d' => d' < d ∧ m'.current = 1 ∧
      (proto K).inv (upd G' 1 (gO rp { ph := .pd })) m') G m d :=
  I.post_wp (fitsS (K := K)) rfl hLc rfl 1 (gP rp rc) (gD rp) rc rfl rfl rfl ⟨rfl, .inl rfl⟩
    rfl rfl rfl rfl ⟨rfl, .inl rfl⟩ rfl hdj post_cnt (post_pool hm) post_U io G m d
    hpl.unmetered hi hc

end Post

/-! ## The producer -/

/-- A store of a `u32` that the thread owns. -/
theorem st32 (p : Ptr) (v w : BitVec 32) :
    FTTriple (up (pts p 4 v)) (Zig.store 4 p w) (fun _ => up (pts p 4 w)) :=
  (FTTotalTriple.ofSeq (FTotalTriple.store (by decide) w)
    (ThreadLocal.store (by rw [LawfulEnc.size_encode]; exact OwnsPtr.pts))).toPartial

theorem msg0 : Msg 0 = (up (pts aPtr 4 (0 : BitVec 32)) ⋆ up (pts bPtr 4 (0 : BitVec 32))) := by
  simp [Msg]
theorem msg1 : Msg 1 = (up (pts aPtr 4 (3 : BitVec 32)) ⋆ up (pts bPtr 4 (0 : BitVec 32))) := by
  simp [Msg]
theorem msg2 : Msg 2 = (up (pts aPtr 4 (3 : BitVec 32)) ⋆ up (pts bPtr 4 (4 : BitVec 32))) := by
  simp [Msg]

/-- The producer's store of `a`, on its part. -/
theorem st_a (rp : Res) :
    FTTriple ((fun r => r = rp) ⋆ Msg 0) (Zig.store 4 (cPtr.add 24) (3 : BitVec 32))
      (fun _ => (fun r => r = rp) ⋆ Msg 1) := by
  rw [msg0, msg1]; exact FTTriple.frameL (FTTriple.frame (st32 aPtr 0 3))

/-- The producer's store of `b`, on its part. -/
theorem st_b (rp : Res) :
    FTTriple ((fun r => r = rp) ⋆ Msg 1) (Zig.store 4 (cPtr.add 28) (4 : BitVec 32))
      (fun _ => (fun r => r = rp) ⋆ Msg 2) := by
  rw [msg1, msg2]; exact FTTriple.frameL (FTTriple.frameL (st32 bPtr 0 4))

/-- **The producer**: it writes the message on its part, posts it (`wp_postP`) and ends. -/
theorem producer_spec (I : SemImpl Tgt) (hLc : K.c = I.c) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    {rp rc : Res} (hp : rp.Plain) (hrc : Msg 0 rc) (hdj : FHeap.Disjoint rp.heap rc.heap)
    (hi : (proto K).inv (upd G 1 (gO (rsum rp rc) { ph := .pr 0 })) m) (hc : m.current = 1) :
    (proto K).WP 1 (producer I cPtr) (fun _ G' m' _ => m'.current = 1 ∧
      (proto K).inv (upd G' 1 (⟨.gone, rp, rnil⟩, { ph := .fin })) m') G m d := by
  have hF := (fitsS (K := K)).toC.toFits
  unfold producer
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (FCond.wp_liftPartM hF (.inl rfl) hi hc (st_a rp) ⟨_, _, hdj, rfl, rfl, hrc⟩
    fun _ m₁ r₁ _ hq hc₁ _ _ hi₁ => ?_)
  obtain ⟨r₀, r₁', hd₁, he, h0, hm₁⟩ := hq
  rw [h0] at hd₁ he; subst he
  have hi₁' : (proto K).inv (upd G 1 (gO (rsum rp r₁') { ph := .pr 1 })) m₁ := inv_pr hi₁
  refine WP.bind (FCond.wp_liftPartM hF (.inl rfl) hi₁' hc₁ (st_b rp) ⟨_, _, hd₁, rfl, rfl, hm₁⟩
    fun _ m₂ r₂ _ hq hc₂ _ _ hi₂ => ?_)
  obtain ⟨r₀, r₂', hd₂, he, h0, hm₂⟩ := hq
  rw [h0] at hd₂ he; subst he
  have hi₂' : (proto K).inv (upd G 1 (gO (rsum rp r₂') { ph := .pr 2 })) m₂ := inv_pr hi₂
  refine WP.callC (WP.mono ?_ (wp_postP I hLc (⟨⟩ : Io) hp hm₂ hd₂ hi₂' hc₂))
  rintro _ G' m' _ ⟨-, hc', hi'⟩
  exact ⟨hc', inv_fin hi'⟩

end Sync.Mailbox
