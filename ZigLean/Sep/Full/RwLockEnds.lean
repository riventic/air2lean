import ZigLean.Sep.Full.RwLockBase
import ZigLean.Sep.Full.LockProdEnds

/-!
# The reader/writer lock's base over a thread's end and a join

(ledger #two-lock-product, item (5).) A program with a reader/writer lock keeps its invariant when
a thread that is out of the outer mutex's and the semaphore's mutex's code ends, and when a thread
joins an ended one. Both are proved here once, for every reader/writer lock `W` and every program's
facts `E`: `FRw.Base` is kept over each, and so is every protocol invariant that is the two-lock
product at the base (`FLock.Pair.inv_ghost`, `FLock.Pair.inv_join`,
`ZigLean/Sep/Full/LockProdEnds.lean`).

The program supplies only what is its own: its threads' fact after the step (`E.T`, at the new
client parts and the new thread table), and that the protected resource stays at the new client
parts (`hRk`, as `FLock.Inv.ghost`'s and `FLock.Inv.join`'s `hRk`). The thread keeps its places in
the rwlock's, the condition's and the semaphore's code; out of the outer mutex's code it is out of
the latter two (`Base.sout_of_m`).

- `FClient.Holds.relabel`, `Holds.threads`, `Holds.join`: the program's facts over a change of the
  client parts and of the thread table that keeps the number of threads and the record of accesses
  and makes no clock smaller. The read-shared region stays shared (`ReadShared.keep`) and its
  bytes stay in the rest.
- `FSem.Inv.keep`: the semaphore's invariant over a step that keeps `FLock.HB`, with at least as
  many threads (`FSem.Inv.monoTk` asks for the same thread table, which a join changes).
- `FRw.Inv.keepR`: the rwlock's invariant over a step that keeps the state word and the number of
  threads, at client parts that keep the resource (`FRw.Inv.keep` asks for the same thread table
  and client parts).
- `FRw.lR_keep`: the semaphore's mutex's resource at client parts that keep the resource.
- `FRw.Shares.join`: the joiner's part takes the ended thread's, which holds no reader's share.
- `FRw.Base.thread`: the base over a change of one thread's ghost value outside both mutexes'
  code, in a memory with a new current thread, clocks and thread table.
- `FRw.Base.ghost`, `Base.join`: the base over the end and over the join.
- `FRw.Base.inv_ghost`, `Base.inv_join`: the invariant of every protocol of the two-lock product
  at the base, over the end and over the join.
- `FRw.Base.wp_join`: the join under such a protocol (`WP.joinC`).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

namespace FClient.Holds

variable {X : Type} {E : FClient X} {xs xs' : ThreadId → X} {rX : Res} {m m' : Mem}

/-- **A change of the client parts keeps the program's facts**, given the threads' fact at the
new parts: the read-shared region and its bytes stay. -/
theorem relabel (h : E.Holds xs rX m) (hT : E.T xs' m.threads) : E.Holds xs' rX m :=
  ⟨hT, h.sh, h.io⟩

/-- **A change of the thread table and the client parts keeps the program's facts**, given the
threads' fact after it: there are as many threads, no clock is smaller and the record of accesses
stays, so the region stays read-shared (`ReadShared.keep`); its bytes stay in the rest. -/
theorem threads (h : E.Holds xs rX m) (hT : E.T xs' m'.threads)
    (hsz : m'.threads.size = m.threads.size)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hfp : m'.footprint = m.footprint) : E.Holds xs' rX m' :=
  ⟨hT, h.sh.keep hsz (fun u _ => hcl u) fun _ he _ => hfp ▸ he, h.io⟩

/-- **A join keeps the program's facts**, given the threads' fact after it (`Holds.threads`). -/
theorem join {t u : ThreadId} (h : E.Holds xs rX m)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hT : E.T xs' m'.threads) : E.Holds xs' rX m' := by
  obtain ⟨cs, ts, rfl, hsz, hcl⟩ := join_mem hj
  exact h.threads hT hsz hcl rfl

end FClient.Holds

namespace FSem

variable {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C}

/-- **`S.Inv` stays** over a step that keeps every thread's places, the count, the holders at
`pst`, the state's writes and the takers' queue entries but for entries at the mutex, grows the
clocks, keeps `HB` (`hHB`: `FLock.HB.mono`, or a step that keeps as many threads) and loses no
thread (`Inv.monoTk` with the thread table free: a join marks a thread joined). -/
theorem Inv.keep {G G' : ThreadId → γ} {m m' : Mem} (hI : S.Inv G m)
    (hsph : ∀ u, S.ph (G' u) = S.ph (G u)) (hcph : ∀ u, C.ph (G' u) = C.ph (G u))
    (hpv : S.cnt G' = S.cnt G)
    (hpst : ∀ u, (S.ph (G u)).isPst → L.ph (G' u) = .holds)
    (hHB : ∀ c, L.HB G m c → L.HB G' m' c)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (ht : m.threads.size ≤ m'.threads.size)
    (hwq : ∀ w ∈ m'.waiters, S.Tk G' w.1 → w ∈ m.waiters ∨ w.2 = L.key m)
    (hkL : L.key m' = L.key m) (hS : C.S.hist m' = C.S.hist m) : S.Inv G' m' := by
  have hTk : ∀ v, S.Tk G' v ↔ S.Tk G v := fun v => by unfold Tk; rw [hsph, hcph]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  refine ⟨fun u hu => ?_, fun u hu => hpst u (by rw [← hsph u]; exact hu),
    fun u hu => by rw [hpv]; exact hI.crit u (by rw [← hcph u]; exact hu),
    fun u hu => by rw [hsph]; exact hI.wt u (by rw [← hcph u]; exact hu),
    fun u v hu hv => hI.cp u v (by rw [← hcph u]; exact hu) (by rw [← hsph v]; exact hv),
    fun w hw hk => ?_, fun p h0 hp => ?_, fun u h c hu => ?_, fun u h c hu p h0 hp => ?_,
    fun u h c hu p h0 hp => ?_, fun hc hpw => ?_⟩
  · exact Nat.lt_of_lt_of_le (hI.ex u (by rw [← hsph u]; exact hu)) ht
  · rw [hkL]
    rcases hwq w hw hk with hw | hw
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

namespace FRw

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C} {W : FRw γ X Y M L C S}

/-- **The invariant over a step that keeps the state word and the number of threads, at client
parts that keep the resource** (`Inv.keep` with the thread table and the client parts free: a join
marks a thread joined, and a thread's end or join changes its client part): the word stays `Ok`,
its history and cells stay, the places stay, the resource stays at the new client parts (`hR`),
the writer's hold of the outer mutex stays, and the free resource stays owned through the word. -/
theorem Inv.keepR {G G' : ThreadId → γ} {rX : Res} {m m' : Mem} (hI : W.Inv G rX m)
    (hok : W.st.Ok m' fun u => M.ph (G' u) ≠ .gone) (hhist : W.st.hist m' = W.st.hist m)
    (hcells : W.st.cellsR m' = W.st.cellsR m) (hth : m'.threads.size = m.threads.size)
    (hph : ∀ u, W.ph (G' u) = W.ph (G u)) (hR : ∀ r, W.R (W.xs G) r → W.R (W.xs G') r)
    (hwm : ∀ u, (W.ph (G u)).isW = true → (M.ph (G' u)).held = true)
    (how : ∀ rF rO, rX = rsum (W.st.cellsR m) (rsum rF rO) → W.FreeRes G m rF → W.Owns G m rF →
      W.Owns G' m' rF) : W.Inv G' rX m' := by
  have hnrd : W.nrd G' m' = W.nrd G m := by simp only [nrd, hth, hph]
  have hnwi : W.nwi G' m' = W.nwi G m := by simp only [nwi, hth, hph]
  have hwr : W.writing G' m' = W.writing G m := by simp only [writing, hth, hph]
  have hfs : W.fsum G' m' = W.fsum G m := by simp only [fsum, hth, hph]
  have hbusy : W.Busy G' ↔ W.Busy G := by simp only [Busy, RwPosted, hph]
  obtain ⟨rF, rO, he, hoffF, hd, hfr, ho⟩ := hI.rest
  obtain ⟨hf1, hf2, hf3⟩ := hfr
  exact {
    ok := hok
    ex := fun u h => by rw [hth]; exact hI.ex u (by rwa [← hph u])
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
      ⟨fun hb => hf1 (hbusy.mp hb),
        fun hb h0 => hR _ (hf2 (fun h => hb (hbusy.mpr h)) (by rwa [← hnrd])),
        fun hb h0 => by
          obtain ⟨H, f, hRr, hf, hs, hr, hq⟩ :=
            hf3 (fun h => hb (hbusy.mpr h)) (by rwa [← hnrd])
          exact ⟨H, f, hR _ hRr, hf, by rw [hfs]; exact hs, hr,
            fun u q H' hu => hq u q H' (by rwa [← hph u])⟩⟩,
      how rF rO he ⟨hf1, hf2, hf3⟩ ho⟩ }

/-- **The semaphore's mutex's resource at client parts that keep the resource**: the places stay,
so the count stays (`cnt_congr`), and the pool is the resource exactly while it is posted
(`pool_posted`, `pool_idle`; `lR_eq` asks for the same client parts). -/
theorem lR_keep {G G' : ThreadId → γ} (hph : ∀ u, W.ph (G' u) = W.ph (G u))
    (hR : ∀ r, W.R (W.xs G) r → W.R (W.xs G') r) (r : Res) (h : L.R G r) : L.R G' r := by
  have hp : RwPosted W.ph G' ↔ RwPosted W.ph G := by simp only [RwPosted, hph]
  rw [S.R_cnt G] at h
  rw [S.R_cnt G', cnt_congr hph]
  refine sep_mono_right (fun r' h' => ?_) h
  by_cases hq : RwPosted W.ph G
  · rw [W.pool_posted _ hq] at h'
    rw [W.pool_posted _ (hp.mpr hq)]
    exact hR _ h'
  · rw [W.pool_idle _ hq] at h'
    rw [W.pool_idle _ fun h => hq (hp.mp h)]
    exact h'

/-- **The readers' shares over a join of `u` by `t`**: the ended thread `u` is out of the rwlock's
code and holds nothing of the outer mutex, so its part holds no share of the readers' heap, and
the joiner's part, which takes it, holds the same share as before. -/
theorem Shares.join {G : ThreadId → γ} {m m' : Mem} {t u : ThreadId} {g : γ}
    (h : W.Shares G m) (hu0 : u ≠ 0)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hwp : W.ph g = W.ph (G t)) (hwu : W.ph (G u) = .out) (hhu : M.held (G u) = rnil)
    (hpart : M.part g = rsum (M.part (G t)) (M.own G m u)) : W.Shares (upd G t g) m' := by
  have hwph : ∀ v, W.ph (upd G t g v) = W.ph (G v) := fun v => by
    by_cases e : v = t
    · rw [e, upd_self, hwp]
    · rw [upd_ne _ _ e]
  have hjb := joinedB_join hu0 hj
  obtain ⟨rec, hr, hrj, -⟩ := Proto.join_eq hj
  have hju : joinedB m u = false := by
    have hr' : m.threads[u]? = some rec := hr
    simp [joinedB, hr', hrj]
  intro u₀ q H hu₀ l c hl v hv
  rw [hwph u₀] at hu₀
  have hvu : v ≠ u := fun e => by rw [hjb, ite_eq_left e] at hv; cases hv
  have hvj : joinedB m v = false := by rw [hjb, ite_eq_right hvu] at hv; exact hv
  rw [hwph v]
  by_cases e : v = t
  · have h1 := h u₀ q H hu₀ l c hl t (e ▸ hvj)
    have h2 := h u₀ q H hu₀ l c hl u hju
    rw [hwu] at h2
    have h2' : (M.part (G u)).gh.share l = SCell.zero := by
      rw [h2]; exact SCell.of_zero c
    rw [e, upd_self, hpart, FLock.own_live (L := M) hju, hhu, rsum_rnil]
    show ((M.part (G t)).gh.share l).add ((M.part (G u)).gh.share l) = _
    rw [h1, h2', SCell.add_zero]
  · rw [upd_ne _ _ e]; exact h u₀ q H hu₀ l c hl v hvj

namespace Base

variable {E : FClient X} {Sz : Nat} {K : BlockKind} {G : ThreadId → γ} {rX : Res} {m : Mem}

/-- **A change of one thread's ghost value outside both mutexes' code, in a memory with a new
current thread, clocks and thread table, keeps the base** (the end of a thread, a join): the thread
is `out` at both mutexes before, and `out` or `gone` after; its places in the rwlock's, the
condition's and the semaphore's code stay (it is out of the latter two, `sout_of_m`); the resource
stays at its new client part (`hRk`); there are as many threads and no clock is smaller. The
program's facts (`hcl`) and the readers' shares (`hsh`) after the step are given: `Base.ghost` and
`Base.join` supply them. -/
theorem thread {t c : ThreadId} {g : γ} {cs : Array VClock} {ts : Array ThreadRec}
    (hu : W.Base E Sz K G rX m) (hm : M.ph (G t) = .out) (hl : L.ph (G t) = .out)
    (hwp : W.place.ph g = W.place.ph (G t))
    (hmg : M.ph g = .out ∨ M.ph g = .gone) (hlg : L.ph g = .out ∨ L.ph g = .gone)
    (hRk : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd G t g)) r)
    (hsz : ts.size = m.threads.size)
    (hclk : ∀ u : Nat, VClock.le (m.clocks[u]!) (cs[u]!) = true)
    (hcl : E.Holds (W.xs (upd G t g)) rX { m with current := c, clocks := cs, threads := ts })
    (hsh : W.Shares (upd G t g) { m with current := c, clocks := cs, threads := ts }) :
    W.Base E Sz K (upd G t g) rX { m with current := c, clocks := cs, threads := ts } := by
  obtain ⟨⟨hC, hW⟩, hS⟩ := hu.sub
  have hso := hu.sout_of_m (u := t) (.inl hm)
  have wph : W.ph g = W.ph (G t) := congrArg Prod.fst hwp
  have spl : S.place.ph g = S.place.ph (G t) := congrArg Prod.snd hwp
  have cph : C.ph g = C.ph (G t) := congrArg Prod.fst spl
  have sph : S.ph g = S.ph (G t) := congrArg Prod.snd spl
  have hcout : C.ph (G t) = .out := congrArg Prod.fst hso
  have hsout : S.ph (G t) = .out := congrArg Prod.snd hso
  have hup : ∀ {α : Type} (f : γ → α), f g = f (G t) → ∀ u, f (upd G t g u) = f (G u) :=
    fun f hf u => by
      by_cases e : u = t
      · rw [e, upd_self, hf]
      · rw [upd_ne _ _ e]
  have hwph := hup W.ph wph
  have hnw : (W.ph (G t)).isW = false := hu.winv.not_isW (.inl hm)
  have hpv : S.cnt (upd G t g) = S.cnt G := cnt_congr hwph
  have hmgone : ∀ u, M.ph (upd G t g u) ≠ .gone → M.ph (G u) ≠ .gone := fun u hg => by
    by_cases e : u = t
    · rw [e, hm]; exact nofun
    · rwa [upd_ne _ _ e] at hg
  have hlgone : ∀ u, L.ph (upd G t g u) ≠ .gone → L.ph (G u) ≠ .gone := fun u hg => by
    by_cases e : u = t
    · rw [e, hl]; exact nofun
    · rwa [upd_ne _ _ e] at hg
  have hheld : ∀ u, (L.ph (G u)).held = true → (L.ph (upd G t g u)).held = true := fun u hh => by
    by_cases e : u = t
    · rw [e, hl] at hh; cases hh
    · rwa [upd_ne _ _ e]
  have hfld : ∀ {Wd : Word 32 4} {A : ThreadId → Prop}, Wd.Ok m A →
      Wd.Ok { m with current := c, clocks := cs, threads := ts } A ∧
        Wd.hist { m with current := c, clocks := cs, threads := ts } = Wd.hist m :=
    fun h => h.fields_size rfl rfl rfl hsz hclk
  have hS' := (hfld (hW C.S (.inl rfl)).1).2
  have hE' := (hfld (hW C.Ep (.inr rfl)).1).2
  have hst := hu.winv.ok.fields_size (m' := { m with current := c, clocks := cs, threads := ts })
    rfl rfl rfl hsz hclk
  -- every clock before the lock's holder, its newest release or every live thread stays so
  have hHB : ∀ c', L.HB G m c' →
      L.HB (upd G t g) { m with current := c, clocks := cs, threads := ts } c' := fun c' h => by
    rcases h with ⟨u, hu', hle⟩ | hb | hlive
    · exact .inl ⟨u, hheld u hu', VClock.le_trans hle (hclk u)⟩
    · exact .inr (.inl hb)
    · exact .inr (.inr fun u hu' hg =>
        VClock.le_trans (hlive u (Nat.lt_of_lt_of_eq hu' hsz) (hlgone u hg)) (hclk u))
  exact {
    cl := hcl
    winv := hu.winv.keepR (hst.1.anti hmgone) hst.2 rfl hsz hwph hRk
      (fun u hw => by
        by_cases e : u = t
        · rw [e, hnw] at hw; cases hw
        · rw [upd_ne _ _ e]; exact hu.winv.wm u hw)
      fun _ _ _ _ ho e he hT => by
        rcases ho e he hT with h | h | ⟨hw, hs, u, hu', hcu⟩
        · exact .inl fun u hu' hg =>
            VClock.le_trans (h u (Nat.lt_of_lt_of_eq hu' hsz) (hmgone u hg)) (hclk u)
        · exact .inr (.inl (by rw [hst.2]; exact h))
        · exact .inr (.inr ⟨hw, hs, u, by rw [hwph u]; exact hu', VClock.le_trans hcu (hclk u)⟩)
    sub := ⟨⟨hC.other (t := t) (g' := g) cph
        (fun hb => by rw [hcout] at hb; cases hb)
        (fun hr _ => by rw [hcout] at hr; cases hr)
        (by rw [S.sx_iff, S.sx_iff, sph]; exact id) hS' hE' rfl rfl rfl
        (fun w hw _ => .inl hw) (fun _ _ _ h => h) (Nat.le_of_eq hsz.symm) hclk,
      fun Wd hWd => by
        obtain ⟨hok, rY, e, hY⟩ := hW Wd hWd
        exact ⟨(hfld hok).1, rY, e, hY⟩⟩,
      hS.keep (G' := upd G t g) (hup S.ph sph) (hup C.ph cph) hpv
        (fun u hp => by
          by_cases e : u = t
          · rw [e, hsout] at hp; cases hp
          · rw [upd_ne _ _ e]; exact hS.pst u hp)
        hHB hclk (Nat.le_of_eq hsz.symm) (fun w hw _ => .inl hw) rfl hS'⟩
    win := hu.win.keep (hup C.ph cph) hS' hE' (hu.win.ehb.step hHB (.inl hE'))
    shares := hsh
    pin := hu.pin
    wt := fun u hq => by rw [hwph u]; exact hu.wt u (by rwa [hup S.ph sph u] at hq)
    nap := fun u hq => by
      by_cases e : u = t
      · rw [e, upd_self, spl, hso] at hq
        rcases hq with ⟨h1, -, h3⟩ | hq
        · rcases hlg with h | h
          · exact absurd h h1
          · exact absurd h h3
        · exact absurd rfl hq
      · rw [upd_ne _ _ e] at hq ⊢; exact hu.nap u hq
    live := hu.live
    rdm := fun u hr => by
      by_cases e : u = t
      · rw [e, upd_self]; rcases hmg with h | h <;> rw [h] <;> exact ⟨nofun, nofun⟩
      · rw [upd_ne _ _ e] at hr ⊢; exact hu.rdm u hr
    mal := fun u ha => by
      by_cases e : u = t
      · rw [e, upd_self] at ha; rcases hmg with h | h <;> rw [h] at ha <;> cases ha
      · rw [upd_ne _ _ e] at ha ⊢; exact hu.mal u ha }

/-- **The end of a thread keeps the base**: thread `t`, out of both mutexes' code, goes to `gone`
at them (or stays `out`: `main` before its joins), keeping its places in the rwlock's, the
condition's and the semaphore's code and its part. The program gives its threads' fact at the new
client parts (`hT`) and that the resource stays at them (`hRk`). -/
theorem ghost {t : ThreadId} {g : γ} (hu : W.Base E Sz K G rX m) (hm : M.ph (G t) = .out)
    (hl : L.ph (G t) = .out) (hwp : W.place.ph g = W.place.ph (G t))
    (hpart : M.part g = M.part (G t))
    (hmg : M.ph g = .out ∨ M.ph g = .gone) (hlg : L.ph g = .out ∨ L.ph g = .gone)
    (hRk : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd G t g)) r)
    (hT : E.T (W.xs (upd G t g)) m.threads) : W.Base E Sz K (upd G t g) rX m := by
  have hup : ∀ {α : Type} (f : γ → α), f g = f (G t) → ∀ u, f (upd G t g u) = f (G u) :=
    fun f hf u => by
      by_cases e : u = t
      · rw [e, upd_self, hf]
      · rw [upd_ne _ _ e]
  exact hu.thread (c := m.current) (cs := m.clocks) (ts := m.threads) hm hl hwp hmg hlg hRk rfl
    (fun _ => VClock.le_refl _) (hu.cl.relabel hT)
    (hu.shares.congr (hup W.ph (congrArg Prod.fst hwp)) (fun _ hv => hv) fun v l => by
      rw [hup M.part hpart])

/-- **A join keeps the base**: thread `t`, out of both mutexes' code, joins `u`, which ended out
of the rwlock's code and holds nothing of the outer mutex; `t` stays `out`, keeps its places in the
rwlock's, the condition's and the semaphore's code, and its part takes `u`'s (`FLock.Inv.join`).
The program gives its threads' fact at the new client parts and thread table (`hT`) and that the
resource stays at the new client parts (`hRk`). -/
theorem join {m' : Mem} {t u : ThreadId} {g : γ} (hu : W.Base E Sz K G rX m) (hu0 : u ≠ 0)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hm : M.ph (G t) = .out) (hl : L.ph (G t) = .out) (hwp : W.place.ph g = W.place.ph (G t))
    (hwu : W.ph (G u) = .out) (hhu : M.held (G u) = rnil)
    (hpart : M.part g = rsum (M.part (G t)) (M.own G m u))
    (hmg : M.ph g = .out) (hlg : L.ph g = .out)
    (hRk : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd G t g)) r)
    (hT : E.T (W.xs (upd G t g)) m'.threads) : W.Base E Sz K (upd G t g) rX m' := by
  have hsh := hu.shares.join hu0 hj (congrArg Prod.fst hwp) hwu hhu hpart
  have hcl := hu.cl.join hj hT
  obtain ⟨cs, ts, rfl, hsz, hclk⟩ := join_mem hj
  exact hu.thread hm hl hwp (.inl hmg) (.inl hlg) hRk hsz hclk hcl hsh

/-- **The invariant of a protocol with the reader/writer lock, after the end of a thread**
(`FLock.Pair.inv_ghost` at the base, `Base.ghost`): for every protocol whose invariant is the
two-lock product at the base. Thread `t`, out of both mutexes' code, goes to `gone` at them (or
stays `out`), holds nothing, keeps its part and its places in the rwlock's, the condition's and
the semaphore's code. The program gives its threads' fact at the new client parts (`hT`) and that
the resource stays at them (`hRk`). -/
theorem inv_ghost {t : ThreadId} {g : γ}
    (hi : ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m)
    (hm : M.ph (G t) = .out) (hl : L.ph (G t) = .out) (hwp : W.place.ph g = W.place.ph (G t))
    (hpart : M.part g = M.part (G t))
    (hmg : M.ph g = .out ∨ M.ph g = .gone) (hmh : M.held g = rnil)
    (hlg : L.ph g = .out ∨ L.ph g = .gone) (hlh : L.held g = rnil)
    (hRk : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd G t g)) r)
    (hT : E.T (W.xs (upd G t g)) m.threads) :
    ∃ rX, M.Inv (upd G t g) rX m ∧ FLock.Pair.U L (W.Base E Sz K) (upd G t g) rX m := by
  obtain ⟨rX, hM, hU⟩ := hi
  have hwph : ∀ u, W.ph (upd G t g u) = W.ph (G u) := fun u => by
    by_cases e : u = t
    · rw [e, upd_self]; exact congrArg Prod.fst hwp
    · rw [upd_ne _ _ e]
  obtain ⟨h1, h2⟩ := FLock.Pair.inv_ghost (t := t) (g := g) hM hU hm (hmg.imp_right .inl) hpart
    hmh (fun r h => by rw [W.mR] at h ⊢; exact h) hl (hlg.imp_right .inl) hlh
    (lR_keep hwph hRk)
    (fun _ _ _ _ _ _ _ _ hb => hb.ghost hm hl hwp hpart hmg hlg hRk hT)
  exact ⟨rX, h1, h2⟩

/-- **The invariant of a protocol with the reader/writer lock, after a join** (`FLock.Pair.inv_join`
at the base, `Base.join`): for every protocol whose invariant is the two-lock product at the base.
Thread `t`, out of both mutexes' code, joins `u`, which ended (`gone` at both mutexes) out of the
rwlock's code; `t` stays `out`, holds nothing, keeps its places in the rwlock's, the condition's
and the semaphore's code, and its part takes `u`'s without gathering a read share (`hgat`:
`FLock.Inv.own_unshared` for an ended thread whose part holds none). The program gives its
threads' fact at the new client parts and thread table (`hT`) and that the resource stays at the
new client parts (`hRk`). -/
theorem inv_join {m' : Mem} {t u : ThreadId} {g : γ}
    (hi : ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m)
    (hut : u ≠ t) (hu0 : u ≠ 0)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hm : M.ph (G t) = .out) (hl : L.ph (G t) = .out)
    (hmu : M.ph (G u) = .gone) (hlu : L.ph (G u) = .gone) (hwu : W.ph (G u) = .out)
    (hwp : W.place.ph g = W.place.ph (G t))
    (hpart : M.part g = rsum (M.part (G t)) (M.own G m u))
    (hmg : M.ph g = .out) (hmh : M.held g = rnil) (hlg : L.ph g = .out) (hlh : L.held g = rnil)
    (hRk : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd G t g)) r)
    (hgat : ∀ l, (M.own G m t).shared l = none ∨ (M.own G m u).shared l = none)
    (hT : E.T (W.xs (upd G t g)) m'.threads) :
    ∃ rX, M.Inv (upd G t g) rX m' ∧ FLock.Pair.U L (W.Base E Sz K) (upd G t g) rX m' := by
  obtain ⟨rX, hM, hU⟩ := hi
  have hwph : ∀ v, W.ph (upd G t g v) = W.ph (G v) := fun v => by
    by_cases e : v = t
    · rw [e, upd_self]; exact congrArg Prod.fst hwp
    · rw [upd_ne _ _ e]
  have hhu : M.held (G u) = rnil := hM.idle u (by rw [hmu]; rfl)
  obtain ⟨h1, h2⟩ := FLock.Pair.inv_join (t := t) (u := u) (g := g) hM hU hut hu0 hj hm hmu
    hpart hmg hmh (fun r h => by rw [W.mR] at h ⊢; exact h) hl hlu hlg hlh (lR_keep hwph hRk)
    hgat (fun _ _ _ _ _ _ _ _ hb => hb.join hu0 hj hm hl hwp hwu hhu hpart hmg hlg hRk hT)
  exact ⟨rX, h1, h2⟩

/-- **A join under a protocol with the reader/writer lock** (`WP.joinC`, `Base.inv_join`): for
every protocol whose invariant is the two-lock product at the base and whose ended threads are
`gone` at both mutexes and out of the rwlock's code. Thread `t` joins `u` at the ghost value `g₀`,
out of both mutexes' code. After the join the invariant holds at every ghost value `g` of `t` that
is `out` at both mutexes, holds nothing, keeps `g₀`'s places in the rwlock's, the condition's and
the semaphore's code and takes `u`'s part, when the program gives what is its own: the resource at
the new client parts, no gathered read share, and its threads' fact. The strict-mode facts of the
join (`hstrict`: the ranks, the handle, that the join runs) are the program's. -/
theorem wp_join {Tgt σ : Type} {P : Proto Tgt γ} {s : σ} {t u : ThreadId} {g₀ : γ} {n : Nat}
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m)
    (finM : ∀ g, P.fin g → M.ph g = .gone) (finL : ∀ g, P.fin g → L.ph g = .gone)
    (kfin : ∀ g, P.fin g → W.ph g = .out)
    (hi : P.inv (upd G t g₀) m) (hut : u ≠ t) (hu0 : u ≠ 0)
    (hm : M.ph g₀ = .out) (hl : L.ph g₀ = .out)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (hstrict : P.strict = true → ∀ G₁ m₁, G₁ t = g₀ → P.inv G₁ m₁ →
      P.rank t < P.rank u ∧ u < m₁.threads.size ∧ P.joins g₀ ∧
        Thread.joinValid m₁ t u = true ∧ (P.fin (G₁ u) → ∃ m',
          ((Thread.join u).run { m₁ with current := t }).run = some (.ok ((), m'))))
    (h : ∀ k G₁ m₁ m', n = k + 1 → G₁ t = g₀ → P.inv G₁ m₁ → P.fin (G₁ u) →
      ((Thread.join u).run { m₁ with current := t }).run = some (.ok ((), m')) →
      (∀ g, W.place.ph g = W.place.ph g₀ → M.part g = rsum (M.part g₀) (M.own G₁ m₁ u) →
        M.ph g = .out → M.held g = rnil → L.ph g = .out → L.held g = rnil →
        (∀ r, W.R (W.xs G₁) r → W.R (W.xs (upd G₁ t g)) r) →
        (∀ l, (M.own G₁ m₁ t).shared l = none ∨ (M.own G₁ m₁ u).shared l = none) →
        E.T (W.xs (upd G₁ t g)) m'.threads → P.inv (upd G₁ t g) m') →
      Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((joinC u : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.joinC (fun k hk => ⟨g₀, hi, fun G₁ m₁ hg hi₁ => ?_⟩) hcost
  refine ⟨fun hs => ?_, fun hfin => ⟨fun hs => ?_, fun m' hj => ?_⟩⟩
  · obtain ⟨a, b, c, d, -⟩ := hstrict hs G₁ m₁ hg hi₁
    exact ⟨a, b, c, d⟩
  · exact (hstrict hs G₁ m₁ hg hi₁).2.2.2.2 hfin
  · refine h k G₁ m₁ m' hk hg hi₁ hfin hj
      fun g hwp hpart hmg hmh hlg hlh hRk hgat hT => ?_
    rw [← hg] at hm hl hwp hpart
    exact (inv _ _).mpr (inv_join ((inv _ _).mp hi₁) hut hu0 hj hm hl (finM _ hfin)
      (finL _ hfin) (kfin _ hfin) hwp hpart hmg hmh hlg hlh hRk hgat hT)

end Base

end FRw

end Full
end Zig
