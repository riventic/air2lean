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

- `FRw.Base.fork`: the base, for every reader/writer lock and every client. The program's facts
  stay (`FClient.Holds.fork`), the rwlock's invariant stays (`FRw.Inv.grow`: the counts read no
  thread out of the code, `counts_grow`; the state word stays `Ok` at the threads that have not
  ended, `Word.Ok.forkLive`; the free resource stays owned through the word), the condition's and
  the semaphore's invariants stay (`FCond.Inv.stay`, `FCond.Inv.other`, `FSem.Inv.grow`), the
  window stays (`FLock.HB.fork`), the readers' shares stay (the parent holds no share, so neither
  part of its part does), and the places' clauses hold at the child, which is out of every code.
- `FRw.Base.forkInv`: the invariant `∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m`
  after the spawn (`FLock.Pair.fork`, `ZigLean/Sep/Full/LockProdThreads.lean`).
- `FRw.Base.forkProto`: the same for a protocol whose invariant is that one (`RwProd`'s `inv`,
  `ZigLean/Sep/Full/RwLockGhost.lean`), with the child's id and the current thread, in the form a
  program's spawn step uses.
- `FRw.Base.spawnProto`, `FRw.Base.spawn`: the spawn as a program's `main` uses it. `main`'s part
  holds the duplicable plain mode; it copies the mode before the spawn
  (`FLock.Pair.eupdPart` with `EUpd.plain_split`; the base over the change of its part at the same
  memory is `FRw.Base.setPart`, `ZigLean/Sep/Full/RwLockBase.lean`), keeps its part and gives the
  copy to the child (`forkProto`). `spawn` is the rule a program passes to `fsym` for
  `Thread.fork`.

The memory-level fact of the spawn is the one `FLock.Inv.fork` takes: the run of
`Thread.forkWith gt` at `{ m with current := t }`.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

namespace FRw

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C} {W : FRw γ X Y M L C S}

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

/-! ## The spawn of a program: the plain mode copied for the child -/

/-- **The spawn step of a program with the reader/writer lock, with the plain mode copied for the
child** (module doc), for a protocol whose invariant is the outer mutex's and the two-lock product
at the base. The spawning thread `t` is out of every code (`FRw.Out`) and its part holds the plain
mode (`hp`, e.g. `main`'s start part); it copies the mode (`EUpd.plain_split`,
`FLock.Pair.eupdPart`, `Base.setPart`) and gives the copy `rP` to the child (`forkProto`). The
client chooses the parent's new ghost value `g₁`, with the parent's old part, and the child's
`g₀`, whose part becomes `rP`; both are out of every code. The part is no place (`hpl`). The
program gives its resource at the new client parts (`hR`) and its threads' fact at the new thread
table (`hT`), which read no part (`FRw.x_part`). -/
theorem spawnProto {Tgt : Type} {P : Proto Tgt γ} {t c : ThreadId} {g₁ g₀ : γ} {gt : Bool}
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m)
    (hpl : ∀ g r, W.place.ph (M.setPart g r) = W.place.ph g)
    (hp : (M.part (G t)).Plain) (hi : P.inv G m) (hout : W.Out (G t))
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (h₁ : W.Out g₁) (hp₁ : M.part g₁ = M.part (G t)) (h₀ : W.Out g₀)
    (hR : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd (upd G c g₀) t g₁)) r)
    (hT : E.T (W.xs (upd (upd G c g₀) t g₁)) m'.threads) :
    c = m.threads.size ∧ m'.current = t ∧ ∃ rP, plain rP ∧
      P.inv (upd (upd G c (M.setPart g₀ rP)) t g₁) m' := by
  obtain ⟨rX, hM, hU⟩ := (inv G m).mp hi
  have hgn : M.ph (G t) ≠ .gone := by rw [hout.2.1]; exact nofun
  have ht : t < m.threads.size := (hM.w.live t (by show M.ph (G t) ≠ .gone; exact hgn)).1
  have hM₀ : M.Inv (upd G t (G t)) rX { m with current := t } := by
    rw [upd_same]; exact hM.cur t
  have hU₀ : FLock.Pair.U L (W.Base E Sz K) (upd G t (G t)) rX { m with current := t } := by
    rw [upd_same]; exact FLock.Pair.U_atStop t hU fun _ h => h.atStop t
  -- the plain mode copied: `t`'s part is its old part and a plain `rP`
  obtain ⟨r, ⟨r₁, rP, -, rfl, hr₁, hpP⟩, hM', hU'⟩ := FLock.Pair.eupdPart W.pair P hM₀ hU₀ rfl hgn
    (EUpd.plain_split (P := fun r => r = M.part (G t)) fun r hr => by rw [hr]; exact hp)
    (fun r _ sB rL rH rX' _ _ _ hMa hMb hu => by
      have h := hu.setPart (t := t) (r := r) hMa (by rw [upd_self, upd_upd]; exact hMb)
        (fun _ => rfl) ht hpl
      rwa [upd_self, upd_upd] at h)
  subst hr₁
  obtain ⟨G₁, hG₁⟩ : ∃ G', G' = upd G t (M.setPart (G t) (rsum (M.part (G t)) rP)) := ⟨_, rfl⟩
  rw [← hG₁] at hM' hU'
  have hG₁t : G₁ t = M.setPart (G t) (rsum (M.part (G t)) rP) := by rw [hG₁, upd_self]
  have hupd : ∀ a, upd (upd G₁ c a) t g₁ = upd (upd G c a) t g₁ := fun a => funext fun u => by
    by_cases h1 : u = t
    · rw [h1, upd_self, upd_self]
    · rw [upd_ne _ _ h1, upd_ne _ _ h1]
      by_cases h2 : u = c
      · rw [h2, upd_self, upd_self]
      · rw [upd_ne _ _ h2, upd_ne _ _ h2, hG₁, upd_ne _ _ h1]
  have hxs : W.xs (upd (upd G c (M.setPart g₀ rP)) t g₁) = W.xs (upd (upd G c g₀) t g₁) :=
    funext fun u => by
      show W.x (upd (upd G c (M.setPart g₀ rP)) t g₁ u) = W.x (upd (upd G c g₀) t g₁ u)
      by_cases h1 : u = t
      · rw [h1, upd_self, upd_self]
      · rw [upd_ne _ _ h1, upd_ne _ _ h1]
        by_cases h2 : u = c
        · rw [h2, upd_self, upd_self, W.x_part]
        · rw [upd_ne _ _ h2, upd_ne _ _ h2]
  have hxs₁ : W.xs G₁ = W.xs G := funext fun u => by
    show W.x (G₁ u) = W.x (G u)
    by_cases h1 : u = t
    · rw [h1, hG₁t, W.x_part]
    · rw [hG₁, upd_ne _ _ h1]
  have hfin := forkProto (P := P) (G := G₁) (m := { m with current := t }) (g₁ := g₁)
    (g₀ := M.setPart g₀ rP) inv ((inv _ _).mpr ⟨rX, hM', hU'⟩) hf
    (by rw [hG₁t]; exact out_setPart hpl hout _) h₁ (out_setPart hpl h₀ rP)
    (by rw [hG₁t, M.part_setPart, M.part_setPart, hp₁])
    (by rw [M.part_setPart, (plain_ghost hpP).1]; exact FHeap.disjoint_empty _)
    (fun r hr => by
      rw [hupd, hxs]
      rw [hxs₁] at hr
      exact hR r hr)
    (by rw [hupd, hxs]; exact hT)
  rw [hupd] at hfin
  exact ⟨hfin.1, hfin.2.1, rP, hpP, hfin.2.2⟩

/-- **`spawnProto` at `Thread.fork`** (a child that is not gated), in the form a program's `main`
passes to `fsym` as its spawn rule (as `inv_spawn` of `Proofs/SemCounter/Start.lean`). -/
theorem spawn {Tgt : Type} {P : Proto Tgt γ} {t c : ThreadId} {g₁ g₀ : γ}
    (inv : ∀ G m, P.inv G m ↔ ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m)
    (hpl : ∀ g r, W.place.ph (M.setPart g r) = W.place.ph g)
    (hp : (M.part (G t)).Plain) (hi : P.inv G m) (hout : W.Out (G t))
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m')))
    (h₁ : W.Out g₁) (hp₁ : M.part g₁ = M.part (G t)) (h₀ : W.Out g₀)
    (hR : ∀ r, W.R (W.xs G) r → W.R (W.xs (upd (upd G c g₀) t g₁)) r)
    (hT : E.T (W.xs (upd (upd G c g₀) t g₁)) m'.threads) :
    c = m.threads.size ∧ m'.current = t ∧ ∃ rP, plain rP ∧
      P.inv (upd (upd G c (M.setPart g₀ rP)) t g₁) m' :=
  spawnProto (gt := false) inv hpl hp hi hout hf h₁ hp₁ h₀ hR hT

end Base

end FRw

end Full
end Zig
