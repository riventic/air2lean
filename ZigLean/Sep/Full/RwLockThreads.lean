import ZigLean.Sep.Full.RwLockBase
import ZigLean.Sep.Full.LockProdThreads

/-!
# The reader/writer lock's base over a spawn

(ledger #two-lock-product, item (5).) A program whose protocol is the reader/writer lock's
(`FRw.Base` in the two-lock product, `ZigLean/Sep/Full/RwLockBase.lean`) keeps its invariant when a
thread spawns a child, with no proof of its own: the spawning thread `t` is out of the lock's code
and of its components' (`FRw.Out`), it keeps `part g₁` of its part and the child gets `part g₀`,
and both new ghost values are `FRw.Out`. The program supplies only what is its own: its resource
at the new client parts (`hR`) and its threads' fact at the new thread table (`hT`).

- `FClient.Holds.fork`: the program's facts (`ReadShared.fork`: the child's clock is above its
  parent's, so it holds a share of every read too).
- `FRw.Base.fork`: the base, for every reader/writer lock and every client. The rwlock's invariant
  stays (`FRw.Inv.grow`: the counts read no thread out of the code, `counts_grow`; the state word
  stays `Ok` at the threads that have not ended, `Word.Ok.forkLive`; the free resource stays owned
  through the word), the condition's and the semaphore's invariants stay (`FCond.Inv.stay`,
  `FCond.Inv.other`, `FSem.Inv.grow`), the window stays (`FLock.HB.fork`), the readers' shares stay
  (the parent holds no share, so neither part of its part does), and the places' clauses hold at
  the child, which is out of every code.
- `FRw.Base.forkInv`: the invariant `∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m`
  after the spawn (`FLock.Pair.fork`, `ZigLean/Sep/Full/LockProdThreads.lean`).
- `FRw.Base.forkProto`: the same for a protocol whose invariant is that one (`RwProd`'s `inv`,
  `ZigLean/Sep/Full/RwLockGhost.lean`), with the child's id and the current thread, in the form a
  program's spawn step uses.

The memory-level fact of the spawn is the one `FLock.Inv.fork` takes: the run of
`Thread.forkWith gt` at `{ m with current := t }`.

The lemmas of other modules' namespaces stated here are general and belong next to their
families: `Conc.fork_mem_clocks` (`ZigLean/Conc/Base/Lock.lean`), `Word.Ok.forkLive`
(`ZigLean/Sep/Full/Word.lean`, next to `Ok.fork_native`), `FLock.HB.fork`
(`ZigLean/Sep/Full/Lock.lean`, next to `HB.mono`), `FSem.Inv.grow` (`ZigLean/Sep/Full/Sem.lean`,
next to `Inv.mono`), `FClient.Holds.fork` (`ZigLean/Sep/Full/Client.lean`), and `FRw.counts_grow`,
`FRw.Inv.grow`, `FRw.lR_keep` (`ZigLean/Sep/Full/RwLockImpl.lean`, next to `Inv.keep`, `lR_eq`).
-/

namespace Zig

namespace Conc

open Proto

/-- **The clocks over a spawn** by `t`: no thread's clock moves back, and the new thread's clock
is above `t`'s (`fork_clocks`, at every thread id). -/
theorem fork_mem_clocks {m m' : Mem} {t c : ThreadId} {gt : Bool} (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    (∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) ∧
      VClock.le (m.clocks[t]!) (m'.clocks[m.threads.size]!) = true := by
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨-, rfl⟩ := hf
  obtain ⟨hcl, hcn, -⟩ := fork_clocks (cs := m.clocks) (t := t) (by rw [hcs]; exact ht)
  refine ⟨fun u => ?_, by rw [← hcs]; exact hcn⟩
  by_cases hu : u < m.clocks.size
  · exact hcl u hu
  · rw [getElem!_neg m.clocks u hu]; exact VClock.le_default _

namespace Word

open Full

variable {n nb : Nat} {W : Word n nb} {A A' : ThreadId → Prop}

/-- **A spawn keeps a word's validity at a live set that takes the new thread in**
(`Ok.fork_native` with a new live set `A'`): each old thread of `A'` was in `A`, and with the new
thread in `A'` its parent was in `A` (the new thread's clock is above its parent's). -/
theorem Ok.forkLive {m m' : Mem} {t c : ThreadId} {gt : Bool}
    (hw : W.Ok m A) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (hA : ∀ u, u < m.threads.size → A' u → A u) (hAt : A' m.threads.size → A t) :
    W.Ok m' A' ∧ W.hist m' = W.hist m := by
  obtain ⟨hclk, hnew⟩ := fork_mem_clocks ht hcs hf
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨-, rfl⟩ := hf
  refine ⟨⟨hw.blk, hw.only, hw.loc, ?_, hw.val, hw.plain⟩, hist_congr rfl rfl⟩
  intro e he hh
  rcases hw.wfp e he hh with ⟨ha, u, hu, hle⟩ | hall
  · exact .inl ⟨ha, u, by simpa only [Array.size_push] using Nat.lt_succ_of_lt hu,
      VClock.le_trans hle (hclk u)⟩
  · refine .inr ?_
    intro u hu hu₁
    simp only [Array.size_push] at hu
    by_cases hu' : u < m.threads.size
    · exact VClock.le_trans (hall u hu' (hA u hu' hu₁)) (hclk u)
    · have heq : u = m.threads.size := by omega
      subst u
      exact VClock.le_trans (hall t ht (hAt hu₁)) hnew

end Word

end Conc

namespace Full

open FAssn Conc Proto

namespace FLock

variable {γ : Type} {L : FLock γ}

/-- **`HB` over a step that adds a thread** (a spawn by `t`, which has not ended): the new
thread's clock is above `t`'s, so a clock below every thread that has not ended is below the new
thread's too. The holders stay, the clocks grow, the word's newest release stays, and no old
thread comes back from its end. -/
theorem HB.fork {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {c : VClock} (h : L.HB G m c)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hnew : VClock.le (m.clocks[t]!) (m'.clocks[m.threads.size]!) = true)
    (hsz : m'.threads.size = m.threads.size + 1) (hbef : ∀ c, L.Before m c → L.Before m' c)
    (hhold : ∀ u, (L.ph (G u)).held = true → (L.ph (G' u)).held = true)
    (ht : t < m.threads.size) (hgt : L.ph (G t) ≠ .gone)
    (hgone : ∀ u, u < m.threads.size → L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone) :
    L.HB G' m' c := by
  rcases h with ⟨u, hu, hle⟩ | hb | hlive
  · exact .inl ⟨u, hhold u hu, VClock.le_trans hle (hcl u)⟩
  · exact .inr (.inl (hbef c hb))
  · refine .inr (.inr fun u hu hg => ?_)
    by_cases hu' : u < m.threads.size
    · exact VClock.le_trans (hlive u hu' (hgone u hu' hg)) (hcl u)
    · obtain rfl : u = m.threads.size := by omega
      exact VClock.le_trans (hlive t ht hgt) hnew

end FLock

namespace FSem

variable {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C}

/-- **The semaphore's invariant over a step that grows the threads** (a spawn; `Inv.mono` with
the thread table growing and `HB` over the step given): every thread's places and the count stay,
the holders at `pst` stay, the clocks grow, a new queue entry is at the mutex, and the state's
writes stay. -/
theorem Inv.grow {G G' : ThreadId → γ} {m m' : Mem} (hI : S.Inv G m)
    (hsph : ∀ u, S.ph (G' u) = S.ph (G u)) (hcph : ∀ u, C.ph (G' u) = C.ph (G u))
    (hpv : S.cnt G' = S.cnt G)
    (hpst : ∀ u, (S.ph (G u)).isPst → L.ph (G' u) = .holds)
    (hHB : ∀ c, L.HB G m c → L.HB G' m' c)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (ht : m.threads.size ≤ m'.threads.size)
    (hwq : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ w.2 = L.key m) (hkL : L.key m' = L.key m)
    (hS : C.S.hist m' = C.S.hist m) : S.Inv G' m' := by
  have hTk : ∀ v, S.Tk G' v ↔ S.Tk G v := fun v => by unfold FSem.Tk; rw [hsph, hcph]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  refine ⟨fun u hu => ?_, fun u hu => hpst u (by rw [← hsph u]; exact hu),
    fun u hu => by rw [hpv]; exact hI.crit u (by rw [← hcph u]; exact hu),
    fun u hu => by rw [hsph]; exact hI.wt u (by rw [← hcph u]; exact hu),
    fun u v hu hv => hI.cp u v (by rw [← hcph u]; exact hu) (by rw [← hsph v]; exact hv),
    fun w hw hk => ?_, fun p h0 hp => ?_, fun u h c hu => ?_, fun u h c hu p h0 hp => ?_,
    fun u h c hu p h0 hp => ?_, fun hc hpw => ?_⟩
  · exact Nat.lt_of_lt_of_le (hI.ex u (by rw [← hsph u]; exact hu)) ht
  · rw [hkL]
    rcases hwq w hw with hw | hw
    · exact hI.tq w hw ((hTk _).mp hk)
    · exact hw
  · rw [hS] at hp ⊢
    rcases hI.hw p h0 hp with h | h | ⟨u, hu, hle⟩
    · exact .inl h
    · exact .inr (.inl (hHB _ h))
    · exact .inr (.inr ⟨u, (hTk u).mpr hu, VClock.le_trans hle (hcl u)⟩)
  · obtain ⟨⟨r, hr⟩, hc⟩ := hI.sp u h c (by rw [← hsph u]; exact hu)
    exact ⟨⟨r, by rw [hS]; exact hr⟩, VClock.le_trans hc (hcl u)⟩
  · rcases hI.sb u h c (by rw [← hsph u]; exact hu) p h0 hp with h | h | ⟨v, hv⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨v, (hTk v).mpr hv⟩)
  · rw [hS] at hp ⊢
    rcases hI.sa u h c (by rw [← hsph u]; exact hu) p h0 hp with h | ⟨v, hv⟩
    · exact .inl h
    · exact .inr ⟨v, (hTk v).mpr hv⟩
  · rw [hlast] at hpw ⊢
    rcases hI.live (by rwa [← hpv]) hpw with h | ⟨u, hu⟩ | ⟨v, hv⟩
    · exact .inl h
    · exact .inr (.inl ⟨u, by rw [hsph]; exact hu⟩)
    · exact .inr (.inr ⟨v, (hTk v).mpr hv⟩)

end FSem

namespace FClient

variable {X : Type} {E : FClient X} {xs xs' : ThreadId → X} {rX : Res} {m m' : Mem}

/-- **A spawn keeps the program's facts** (module doc): the new thread holds a share of every
read of the region (`ReadShared.fork`), the rest keeps the region's bytes, and the program gives
its threads' fact at the new client parts and thread table (`hT`). -/
theorem Holds.fork {t c : ThreadId} {gt : Bool} (h : E.Holds xs rX m) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (hT : E.T xs' m'.threads) : E.Holds xs' rX m' := by
  obtain ⟨hclk, hnew⟩ := fork_mem_clocks ht hcs hf
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨-, rfl⟩ := hf
  exact ⟨hT, h.sh.fork (t := t) ht (by simp) (fun u _ => hclk u) hnew fun _ he _ => he, h.io⟩

end FClient

namespace FRw

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C} {W : FRw γ X Y M L C S}

/-- **The counts read no thread out of the rwlock's code**: over a thread table with one more
thread, when each thread in the code is in the old one (`Inv.ex`). -/
theorem counts_grow {G : ThreadId → γ} {m m' : Mem}
    (hex : ∀ u, W.ph (G u) ≠ .out → u < m.threads.size)
    (hsz : m'.threads.size = m.threads.size + 1) :
    W.nrd G m' = W.nrd G m ∧ W.nwi G m' = W.nwi G m ∧ W.writing G m' = W.writing G m ∧
      W.fsum G m' = W.fsum G m := by
  have hN : W.ph (G m.threads.size) = .out :=
    Classical.byContradiction fun h => Nat.lt_irrefl _ (hex _ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [nrd, hsz, tsum_succ, hN, RwPh.isRd]
  · simp [nwi, hsz, tsum_succ, hN, RwPh.isWi]
  · simp [writing, hsz, List.range_succ, hN, RwPh.isW]
  · simp [fsum, hsz, ftot, hN, RwPh.frac, Frac.zero]

/-- **The invariant over a step that adds a thread and keeps the state word** (a spawn; as
`Inv.keep`, with the thread table growing by one and the client parts changing): the word stays
`Ok` at the threads that have not ended after the step, its history and cells stay, the places
stay, the resource holds at the new client parts (`hR`), the writer's hold of the outer mutex
stays, and the free resource stays owned through the word. -/
theorem Inv.grow {G G' : ThreadId → γ} {rX : Res} {m m' : Mem} (hI : W.Inv G rX m)
    (hsz : m'.threads.size = m.threads.size + 1)
    (hok : W.st.Ok m' fun u => M.ph (G' u) ≠ .gone) (hhist : W.st.hist m' = W.st.hist m)
    (hcells : W.st.cellsR m' = W.st.cellsR m)
    (hph : ∀ u, W.ph (G' u) = W.ph (G u))
    (hR : ∀ r, W.R (W.xs G) r → W.R (W.xs G') r)
    (hwm : ∀ u, (W.ph (G u)).isW = true → (M.ph (G' u)).held = true)
    (how : ∀ rF, W.Owns G m rF → W.Owns G' m' rF) : W.Inv G' rX m' := by
  obtain ⟨hn1, hn2, hn3, hn4⟩ := counts_grow (W := W) hI.ex hsz
  have hnrd : W.nrd G' m' = W.nrd G m := by rw [← hn1]; simp only [nrd, hph]
  have hnwi : W.nwi G' m' = W.nwi G m := by rw [← hn2]; simp only [nwi, hph]
  have hwr : W.writing G' m' = W.writing G m := by rw [← hn3]; simp only [writing, hph]
  have hfs : W.fsum G' m' = W.fsum G m := by rw [← hn4]; simp only [fsum, hph]
  have hbusy : W.Busy G' ↔ W.Busy G := by simp only [Busy, RwPosted, hph]
  obtain ⟨rF, rO, he, hoffF, hd, hfr, ho⟩ := hI.rest
  exact {
    ok := hok
    ex := fun u h => by rw [hsz]; exact Nat.lt_succ_of_lt (hI.ex u (by rwa [← hph u]))
    room := by rw [hnrd, hnwi]; exact hI.room
    word := by rw [hnrd, hnwi, hwr, hhist]; exact hI.word
    msgs := by rw [hhist]; exact hI.msgs
    one := fun u v hu hv => hI.one u v (by rwa [← hph u]) (by rwa [← hph v])
    wm := fun u hu => hwm u (by rwa [← hph u])
    wr := fun u hu => by rw [hnrd]; exact hI.wr u (by rwa [← hph u])
    rp := fun u hu => by
      obtain ⟨h1, ⟨w, hw⟩, h3⟩ := hI.rp u (by rwa [← hph u])
      exact ⟨by rw [hnrd]; exact h1, ⟨w, by rw [hph w]; exact hw⟩,
        fun v hv => h3 v (by rwa [← hph v])⟩
    rpR := fun u r hu => hR r (hI.rpR u r (by rwa [← hph u]))
    rest := ⟨rF, rO, by rw [hcells]; exact he, hoffF, hd,
      ⟨fun hb => hfr.1 (hbusy.mp hb),
        fun hb h0 => hR rF (hfr.2.1 (fun h => hb (hbusy.mpr h)) (by rwa [← hnrd])),
        fun hb h0 => by
          obtain ⟨H, f, hRr, hf, hs, hr, hq⟩ :=
            hfr.2.2 (fun h => hb (hbusy.mpr h)) (by rwa [← hnrd])
          exact ⟨H, f, hR _ hRr, hf, by rw [hfs]; exact hs, hr,
            fun u q H' hu => hq u q H' (by rwa [← hph u])⟩⟩,
      how rF ho⟩ }

/-- **The semaphore's mutex's resource at new client parts** (as `lR_eq`, with the client parts
changing): the rwlock's places stay, so the count stays and the pool is the protected resource or
nothing as before, and the protected resource holds at the new client parts (`hR`). -/
theorem lR_keep {G G' : ThreadId → γ} (hph : ∀ u, W.ph (G' u) = W.ph (G u))
    (hR : ∀ r, W.R (W.xs G) r → W.R (W.xs G') r) : ∀ r, L.R G r → L.R G' r := by
  intro r hr
  have hp : RwPosted W.ph G' ↔ RwPosted W.ph G := by simp only [RwPosted, hph]
  rw [S.R_cnt G] at hr
  rw [S.R_cnt G', cnt_congr (W := W) hph]
  by_cases hP : RwPosted W.ph G
  · rw [W.pool_posted G hP] at hr
    rw [W.pool_posted G' (hp.mpr hP)]
    obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hr
    exact ⟨r₁, r₂, hd, rfl, h1, hR r₂ h2⟩
  · rw [W.pool_idle G hP] at hr
    rw [W.pool_idle G' fun h => hP (hp.mp h)]
    exact hr

namespace Base

variable {E : FClient X} {Sz : Nat} {K : BlockKind} {G : ThreadId → γ} {rX : Res} {m m' : Mem}

/-- **A spawn keeps the base** (module doc), for every reader/writer lock and every client. The
spawning thread `t` is out of the lock's code and of its components' (`FRw.Out`), and so are its
new ghost value `g₁` and the new thread's `g₀`; `t`'s part is split between them (`hsplit`). The
outer mutex's word invariant (`hMw`, from its invariant) gives that `t` exists and is not joined.
The program gives its resource at the new client parts (`hR`) and its threads' fact at the new
thread table (`hT`). -/
theorem fork {t c : ThreadId} {g₁ g₀ : γ} {gt : Bool} (hu : W.Base E Sz K G rX m)
    (hMw : M.WInv (M.pl G) m)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (hout : W.Out (G t)) (h₁ : W.Out g₁) (h₀ : W.Out g₀)
    (hsplit : M.part (G t) = rsum (M.part g₁) (M.part g₀))
    (hR : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd (upd G c g₀) t g₁)) r)
    (hT : E.T (W.xs (upd (upd G c g₀) t g₁)) m'.threads) :
    W.Base E Sz K (upd (upd G c g₀) t g₁) rX m' := by
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd (upd G c g₀) t g₁ := ⟨_, rfl⟩
  rw [← hG'] at hR hT ⊢
  obtain ⟨hwo, hmo, -, hlo, -, hco, hso⟩ := hout
  obtain ⟨hw1, hm1, -, hl1, -, hc1, hs1⟩ := h₁
  obtain ⟨hw0, hm0, -, hl0, -, hc0, hs0⟩ := h₀
  obtain ⟨ht, hjt⟩ := hMw.live t (by show M.ph (G t) ≠ .gone; rw [hmo]; decide)
  have hcs := hMw.csize
  obtain ⟨⟨hC, hW⟩, hS⟩ := hu.sub
  have hjb := joinedB_fork hf
  have hcl' := FClient.Holds.fork hu.cl ht hcs hf hT
  have hWf : ∀ Wd : Word 32 4, (Wd = C.S ∨ Wd = C.Ep) →
      Wd.Ok m' (fun _ => True) ∧ Wd.hist m' = Wd.hist m :=
    fun Wd hWd => (hW Wd hWd).1.fork_native ht hcs hf
  obtain ⟨hclk, hnew⟩ := fork_mem_clocks ht hcs hf
  obtain ⟨hcN, -, -⟩ := hMw.fork (gt := gt) (by exact hmo) hf
  subst hcN
  have hNt : m.threads.size ≠ t := fun h => by rw [h] at ht; exact Nat.lt_irrefl _ ht
  -- the new ghost values
  have hGt : G' t = g₁ := by rw [hG', upd_self]
  have hGN : G' m.threads.size = g₀ := by rw [hG', upd_ne _ _ hNt, upd_self]
  have hGo : ∀ u, u ≠ t → u ≠ m.threads.size → G' u = G u := fun u h1 h2 => by
    rw [hG', upd_ne _ _ h1, upd_ne _ _ h2]
  have hup : ∀ {α : Type} (f : γ → α), f g₁ = f (G t) → f g₀ = f (G m.threads.size) →
      ∀ u, f (G' u) = f (G u) := fun f e1 e0 u => by
    by_cases h1 : u = t
    · rw [h1, hGt, e1]
    · by_cases h2 : u = m.threads.size
      · rw [h2, hGN, e0]
      · rw [hGo u h1 h2]
  -- the thread id past the table is out of every code
  have hwN : W.ph (G m.threads.size) = .out :=
    Classical.byContradiction fun h => Nat.lt_irrefl _ (hu.winv.ex _ h)
  have hcN : C.ph (G m.threads.size) = .out :=
    Classical.byContradiction fun h => Nat.lt_irrefl _ (hC.ex _ h)
  have hsN : S.ph (G m.threads.size) = .out :=
    Classical.byContradiction fun h => Nat.lt_irrefl _ (hS.ex _ h)
  have hmNg : M.ph (G m.threads.size) = .gone :=
    Classical.byContradiction fun h => Nat.lt_irrefl _ (hMw.live _ h).1
  have hlNh : (L.ph (G m.threads.size)).held = false := by
    cases e : L.ph (G m.threads.size) <;> first
      | rfl
      | (exfalso
         rcases hu.nap _ (.inl ⟨by rw [e]; decide, by rw [e]; decide, by rw [e]; decide⟩)
           with h | h <;> rw [hmNg] at h <;> cases h)
  have hwph := hup W.ph (hw1.trans hwo.symm) (hw0.trans hwN.symm)
  have hcph := hup C.ph (hc1.trans hco.symm) (hc0.trans hcN.symm)
  have hsph := hup S.ph (hs1.trans hso.symm) (hs0.trans hsN.symm)
  have hspl : ∀ u, S.place.ph (G' u) = S.place.ph (G u) := fun u =>
    Prod.ext (hcph u) (hsph u)
  have hmph : ∀ u, u ≠ m.threads.size → M.ph (G' u) = M.ph (G u) := fun u h2 => by
    by_cases h1 : u = t
    · rw [h1, hGt, hm1, hmo]
    · rw [hGo u h1 h2]
  have hlph : ∀ u, u ≠ m.threads.size → L.ph (G' u) = L.ph (G u) := fun u h2 => by
    by_cases h1 : u = t
    · rw [h1, hGt, hl1, hlo]
    · rw [hGo u h1 h2]
  have hmN : M.ph (G' m.threads.size) = .out := by rw [hGN]; exact hm0
  have hlN : L.ph (G' m.threads.size) = .out := by rw [hGN]; exact hl0
  -- the state word at the threads that have not ended after the spawn
  obtain ⟨hokW, hhW⟩ := Word.Ok.forkLive (A' := fun u => M.ph (G' u) ≠ .gone) hu.winv.ok ht hcs hf
    (fun u hu' h => by
      have h' : M.ph (G' u) ≠ .gone := h
      rwa [hmph u (Nat.ne_of_lt hu')] at h')
    (fun _ => by show M.ph (G t) ≠ .gone; rw [hmo]; decide)
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨-, rfl⟩ := hf
  have hhS := (hWf C.S (.inl rfl)).2
  have hhE := (hWf C.Ep (.inr rfl)).2
  have hHB : ∀ c', L.HB G m c' → L.HB G' _ c' := fun c' h =>
    h.fork hclk hnew (by simp) (fun _ h => h)
      (fun u hh => by
        by_cases h2 : u = m.threads.size
        · rw [h2, hlNh] at hh; cases hh
        · rw [hlph u h2]; exact hh)
      ht (by rw [hlo]; decide) (fun u hu' hg => by rwa [hlph u (Nat.ne_of_lt hu')] at hg)
  -- the condition: the memory first, then the two ghost values
  have hC1 := hC.stay hhS hhE rfl rfl rfl (fun _ hw _ => hw) (fun _ _ h => h) (by simp) hclk
  have hC2 := hC1.other (t := m.threads.size) (g' := g₀) (hc0.trans hcN.symm)
    (fun h => by rw [hcN] at h; cases h) (fun h => by rw [hcN] at h; cases h)
    (fun h => by rw [S.sx_iff, hsN] at h; cases h) rfl rfl rfl rfl rfl
    (fun w hw _ => .inl hw) (fun _ _ _ h => h) (Nat.le_refl _) (fun _ => VClock.le_refl _)
  have htN : upd G m.threads.size g₀ t = G t := upd_ne _ _ (Ne.symm hNt)
  have hC3 := hC2.other (t := t) (g' := g₁) (by rw [htN]; exact hc1.trans hco.symm)
    (fun h => by rw [htN, hco] at h; cases h) (fun h => by rw [htN, hco] at h; cases h)
    (fun h => by rw [htN, S.sx_iff, hso] at h; cases h) rfl rfl rfl rfl rfl
    (fun w hw _ => .inl hw) (fun _ _ _ h => h) (Nat.le_refl _) (fun _ => VClock.le_refl _)
  rw [← hG'] at hC3
  exact {
    cl := hcl'
    winv := hu.winv.grow (by simp) hokW hhW rfl hwph hR
      (fun u hw => by
        have h2 : u ≠ m.threads.size := fun e => by rw [e, hwN] at hw; cases hw
        rw [hmph u h2]; exact hu.winv.wm u hw)
      (fun rF ho e he hT' => by
        rcases ho e he hT' with h | h | ⟨hw, hs, u, hu', hcu⟩
        · refine .inl fun u hu' hg => ?_
          by_cases h1 : u < m.threads.size
          · have hg' : M.ph (G' u) ≠ .gone := hg
            rw [hmph u (Nat.ne_of_lt h1)] at hg'
            exact VClock.le_trans (h u h1 hg') (hclk u)
          · have hu'' : u < m.threads.size + 1 := by simpa only [Array.size_push] using hu'
            obtain rfl : u = m.threads.size := by omega
            exact VClock.le_trans (h t ht (by show M.ph (G t) ≠ .gone; rw [hmo]; decide)) hnew
        · exact .inr (.inl (by rw [hhW]; exact h))
        · exact .inr (.inr ⟨hw, hs, u, by rw [hwph u]; exact hu',
            VClock.le_trans hcu (hclk u)⟩))
    sub := ⟨⟨hC3, fun Wd hWd => by
        obtain ⟨-, rY, e, hY⟩ := hW Wd hWd
        exact ⟨(hWf Wd hWd).1, rY, e, hY⟩⟩,
      hS.grow hsph hcph (cnt_congr (W := W) hwph)
        (fun u h => by
          have h2 : u ≠ m.threads.size := fun e => by rw [e, hsN] at h; cases h
          rw [hlph u h2]; exact hS.pst u h)
        hHB hclk (by simp) (fun w hw => .inl hw) rfl hhS⟩
    win := hu.win.keep hcph hhS hhE (hu.win.ehb.step hHB (.inl hhE))
    shares := fun u q H hrd l c hl v hv => by
      rw [hwph u] at hrd
      rw [hwph v]
      have hpar := hu.shares u q H hrd l c hl t hjt
      rw [hsplit, hwo] at hpar
      have hz : ((M.part g₁).gh.share l).add ((M.part g₀).gh.share l) = SCell.zero := by
        rw [← SCell.of_zero c]; exact hpar
      by_cases h1 : v = t
      · rw [h1, hGt, hwo]
        exact (SCell.add_eq_zero hz).1.trans (SCell.of_zero c).symm
      · by_cases h2 : v = m.threads.size
        · rw [h2, hGN, hwN]
          exact (SCell.add_eq_zero hz).2.trans (SCell.of_zero c).symm
        · rw [hGo v h1 h2]
          exact hu.shares u q H hrd l c hl v (by rwa [hjb] at hv)
    pin := hu.pin
    wt := fun u hq => by rw [hwph u]; exact hu.wt u (by rwa [hsph u] at hq)
    nap := fun u hq => by
      by_cases e : u = m.threads.size
      · exfalso
        rw [e, hspl] at hq
        rcases hq with ⟨h, -, -⟩ | h
        · exact h hlN
        · exact h (Prod.ext hcN hsN)
      · rw [hmph u e]
        rw [hlph u e, hspl u] at hq
        exact hu.nap u hq
    live := fun l hl => hu.live l hl
    rdm := fun u hr => by
      rw [hwph u] at hr
      have e : u ≠ m.threads.size := fun e => by
        rw [e, hwN] at hr; rcases hr with h | h <;> cases h
      rw [hmph u e]; exact hu.rdm u hr
    mal := fun u ha => by
      by_cases e : u = m.threads.size
      · rw [e, hmN] at ha; cases ha
      · rw [hlph u e]; exact hu.mal u (by rwa [hmph u e] at ha) }

/-- **A spawn keeps the invariant of a protocol with the reader/writer lock** (module doc): the
outer mutex's invariant and the two-lock product at the base (`FLock.Pair.fork`, `Base.fork`).
The outer mutex protects nothing and the semaphore's mutex's resource reads the rwlock's places
and the client parts (`lR_keep`), so the program gives only `hR` and `hT`. -/
theorem forkInv {t c : ThreadId} {g₁ g₀ : γ} {gt : Bool}
    (hi : ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (hout : W.Out (G t)) (h₁ : W.Out g₁) (h₀ : W.Out g₀)
    (hsplit : M.part (G t) = rsum (M.part g₁) (M.part g₀))
    (hd : FHeap.Disjoint (M.part g₁).heap (M.part g₀).heap)
    (hR : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd (upd G c g₀) t g₁)) r)
    (hT : E.T (W.xs (upd (upd G c g₀) t g₁)) m'.threads) :
    ∃ rX, M.Inv (upd (upd G c g₀) t g₁) rX m' ∧
      FLock.Pair.U L (W.Base E Sz K) (upd (upd G c g₀) t g₁) rX m' := by
  obtain ⟨rX, hM, hU⟩ := hi
  have hout' := hout
  have h₁' := h₁
  have h₀' := h₀
  obtain ⟨hwo, hmo, -, hlo, -, -, -⟩ := hout'
  obtain ⟨hw1, hm1, hmh1, hl1, hlh1, -, -⟩ := h₁'
  obtain ⟨hw0, hm0, hmh0, hl0, hlh0, -, -⟩ := h₀'
  have hwph : ∀ u, W.ph (upd (upd G c g₀) t g₁ u) = W.ph (G u) := by
    obtain ⟨sB, rL, rH, rX', -, -, -, hb⟩ := hU
    obtain ⟨hc, -, -⟩ := hM.w.fork (gt := gt) (by exact hmo) hf
    have hwN : W.ph (G c) = .out := Classical.byContradiction fun h => by
      rw [hc] at h; exact Nat.lt_irrefl _ (hb.winv.ex _ h)
    intro u
    by_cases h1 : u = t
    · rw [h1, upd_self, hw1, hwo]
    · rw [upd_ne _ _ h1]
      by_cases h2 : u = c
      · rw [h2, upd_self, hw0, hwN]
      · rw [upd_ne _ _ h2]
  exact ⟨rX, FLock.Pair.fork hM hU hmo hlo hf hsplit hd hm1 hmh1 hm0 hmh0 hl1 hlh1 hl0 hlh0
    (fun r hr => by rw [W.mR G] at hr; rw [W.mR]; exact hr) (lR_keep hwph hR)
    (fun _ _ _ _ _ _ _ _ hb => hb.fork hM.w hf hout h₁ h₀ hsplit hR hT)⟩

/-- **The spawn step of a program with the reader/writer lock** (module doc), for a protocol
whose invariant is the outer mutex's and the two-lock product at the base: the child is the next
thread id, the spawning thread is current, and the invariant holds with the parent's new ghost
value and the child's. -/
theorem forkProto {Tgt : Type} {P : Proto Tgt γ} {t c : ThreadId} {g₁ g₀ : γ} {gt : Bool}
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m)
    (hi : P.inv G m)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (hout : W.Out (G t)) (h₁ : W.Out g₁) (h₀ : W.Out g₀)
    (hsplit : M.part (G t) = rsum (M.part g₁) (M.part g₀))
    (hd : FHeap.Disjoint (M.part g₁).heap (M.part g₀).heap)
    (hR : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd (upd G c g₀) t g₁)) r)
    (hT : E.T (W.xs (upd (upd G c g₀) t g₁)) m'.threads) :
    c = m.threads.size ∧ m'.current = t ∧ P.inv (upd (upd G c g₀) t g₁) m' := by
  have hi' := (inv G m).mp hi
  have hinv := (inv _ _).mpr (forkInv hi' hf hout h₁ h₀ hsplit hd hR hT)
  obtain ⟨rX, hM, -⟩ := hi'
  have hc := (hM.w.fork (gt := gt) (by exact hout.2.1) hf).1
  refine ⟨hc, ?_, hinv⟩
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨-, rfl⟩ := hf
  rfl

end Base

end FRw

end Full
end Zig
