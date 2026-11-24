import ZigLean.Sep.Full.RwLockGhost
import ZigLean.Sep.Full.Share

/-!
# Facts for every client of the reader/writer lock

(ledger #two-lock-product, item (5).) The steps a program with `std.Io.RwLock` takes between the
lock's entry points, stated for every reader/writer lock `W`, every program's facts `E` and every
protocol whose invariant is the two-lock product at the base (`FRw.Base`,
`ZigLean/Sep/Full/RwLockBase.lean`). They are library facts: a client of the lock states none of
them for itself. (They are in this directory until they move next to the facts they extend:
`Share.lean`, `RwLockImpl.lean`, `RwLockBase.lean`.)

- `FTotalTriple.load_sheap`, `ThreadLocal.load_sheap`, `FTTotalTriple.load_sheap`: a typed load
  through the share `q` of a named heap `H` (`sheap H q`), which stays. A reader's part after
  `RwLockImpl.lockShared_wp` holds `shareRes H q` of the heap `H` its place `rd q H` names, and
  `RwLockImpl.unlockShared_wp` asks for that share of that heap; `sload` reads a share of some heap
  with the value (`spts`) and so does not keep the name.
- `FRw.nrd_le`, `FRw.nwi_le`: at most as many readers and pending writers as threads (the room
  premises of `lockShared_wp` and `lock_wp` for a program with a fixed set of threads).
- `FRw.Base.setX`, `FRw.Base.inv_setX`: **the writer changes its client part** while it holds the
  resource (at `wr`). The resource is in its part, so the rest holds none of it (`FreeRes` at
  `Busy`), no thread is a reader or carries the resource, and the semaphore's pool is empty; the
  program gives its threads' fact at the new client parts.
- `FRw.Base.inv_blk`, `FRw.Base.inv_thr`: the lock's block and the program's threads' fact, from
  the invariant.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-! ## A load through a share of a named heap -/

section Sheap

variable {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} {H : FHeap} {q : Frac}

/-- **Load of a typed value through the share `q` of the heap `H`** that holds it: the share of
`H` stays (module doc). -/
theorem FTotalTriple.load_sheap (hq : 0 < q.val) (hn : 0 < Enc.size T)
    (hH : up (pts p a v) ⟨H, Know.none, Ghost.unit⟩) :
    FTotalTriple (sheap H q) (Zig.load T a p) (fun x => ⟪x = v⟫ ⋆ sheap H q) := by
  obtain ⟨A, S, K, bs, ha, hsz, hv, hb, -⟩ := hH.1
  have t := FTotalTriple.load_of_read (P := sheap H q) (q := p) (k := 0) (al := a)
    (fun _ _ _ hh hp => hh.sbytesRead ⟨H, ⟨hb, rfl, rfl⟩, hp⟩ hq) hn (by omega)
    (by simpa using ha) (by rw [Nat.zero_add, ← hsz, Array.extract_size]; exact hv)
  simp only [Int.natCast_zero, Ptr.add_zero] at t
  exact t

/-- The load through a share of a named heap is local to the thread (`ThreadLocal.sload`). -/
theorem ThreadLocal.load_sheap (hq : 0 < q.val)
    (hH : up (pts p a v) ⟨H, Know.none, Ghost.unit⟩) :
    ThreadLocal (sheap H q) (Zig.load T a p) :=
  ThreadLocal.loadOwned fun _ hpb _ hp _ h1 h2 => spts_owned hpb ⟨hq, H, hH, hp⟩ h1 h2

/-- `FTotalTriple.load_sheap` for a thread's step. -/
theorem FTTotalTriple.load_sheap (hq : 0 < q.val) (hn : 0 < Enc.size T)
    (hH : up (pts p a v) ⟨H, Know.none, Ghost.unit⟩) :
    FTTotalTriple (sheap H q) (Zig.load T a p) (fun x => ⟪x = v⟫ ⋆ sheap H q) :=
  FTTotalTriple.ofSeq (FTotalTriple.load_sheap hq hn hH) (ThreadLocal.load_sheap hq hH)

end Sheap

/-- A sum of ones over the threads is their number. -/
theorem tsum_one (N : Nat) : tsum N (fun _ => 1) = N := by
  induction N with
  | zero => rfl
  | succ n ih => rw [tsum_succ, ih]

namespace FRw

variable {γ X Y : Type} {M L : FLock γ} {C : FCond γ} {S : FSem γ Y L C} {W : FRw γ X Y M L C S}

/-! ## The room of a program with a fixed set of threads -/

/-- At most as many readers as threads (`RwLockImpl.lockShared_wp`'s room). -/
theorem nrd_le (G : ThreadId → γ) (m : Mem) : W.nrd G m ≤ m.threads.size :=
  Nat.le_trans (tsum_le fun u _ => by
    show (if _ then 1 else 0) ≤ 1
    split <;> omega) (Nat.le_of_eq (tsum_one _))

/-- At most as many pending writers as threads (`RwLockImpl.lock_wp`'s room). -/
theorem nwi_le (G : ThreadId → γ) (m : Mem) : W.nwi G m ≤ m.threads.size :=
  Nat.le_trans (tsum_le fun u _ => by
    show (if _ then 1 else 0) ≤ 1
    split <;> omega) (Nat.le_of_eq (tsum_one _))

namespace Base

variable {E : FClient X} {Sz : Nat} {K : BlockKind} {G : ThreadId → γ} {rX : Res} {m : Mem}

/-! ## The writer's client part -/

/-- **The writer changes its client part** (module doc): thread `t` at `wr` gets the ghost value
`g'` with the same places and part; the program gives its threads' fact at the new client parts.
The rwlock's invariant by `Inv.relabelBusy` (the resource is away from the rest before and
after). -/
theorem setX {t : ThreadId} {g' : γ} (hu : W.Base E Sz K G rX m) (hw : W.ph (G t) = .wr)
    (hwp : W.place.ph g' = W.place.ph (G t)) (hpart : M.part g' = M.part (G t))
    (hm : M.ph g' = M.ph (G t)) (hl : L.ph g' = L.ph (G t))
    (hT : E.T (W.xs (upd G t g')) m.threads) : W.Base E Sz K (upd G t g') rX m := by
  obtain ⟨⟨hC, hW⟩, hS⟩ := hu.sub
  have wph : W.ph g' = W.ph (G t) := congrArg Prod.fst hwp
  have spl : S.place.ph g' = S.place.ph (G t) := congrArg Prod.snd hwp
  have cph : C.ph g' = C.ph (G t) := congrArg Prod.fst spl
  have sph : S.ph g' = S.ph (G t) := congrArg Prod.snd spl
  have hup : ∀ {α : Type} (f : γ → α), f g' = f (G t) → ∀ u, f (upd G t g' u) = f (G u) :=
    fun f hf u => by
      by_cases e : u = t
      · rw [e, upd_self, hf]
      · rw [upd_ne _ _ e]
  have hwph := hup W.ph wph
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m.clocks[u]!) = true := fun _ => VClock.le_refl _
  have hpv : S.cnt (upd G t g') = S.cnt G := cnt_congr hwph
  have hheld : ∀ u, (L.ph (G u)).held = true → (L.ph (upd G t g' u)).held = true := fun u hh => by
    rw [hup L.ph hl u]; exact hh
  have hlgone : ∀ u, L.ph (upd G t g' u) ≠ .gone → L.ph (G u) ≠ .gone := fun u hg => by
    rwa [hup L.ph hl u] at hg
  -- no thread carries the resource: it would wait for a writer at `ww`, and `t` is the writer
  have hnrp : ∀ u, (W.ph (upd G t g' u)).isRp = false := fun u => by
    rw [hwph u]
    cases h : (W.ph (G u)).isRp
    · rfl
    · obtain ⟨-, ⟨w, hww⟩, -⟩ := hu.winv.rp u h
      have e := hu.winv.one w t (by rw [hww]; rfl) (by rw [hw]; rfl)
      rw [e, hw] at hww; cases hww
  exact {
    cl := ⟨hT, hu.cl.sh, hu.cl.io⟩
    winv := hu.winv.relabelBusy (fun u => by rw [hwph u]) (fun u => by rw [hwph u])
      (fun u => by rw [hwph u]) (fun u h => by rwa [hwph u] at h) (hup M.ph hm)
      (fun u h => hu.winv.wr u (by rwa [hwph u] at h)) hnrp (.inl ⟨t, hw⟩)
      (.inl ⟨t, by rw [hwph t]; exact hw⟩)
    sub := ⟨⟨hC.other (t := t) (g' := g') cph (fun _ => hl) (fun _ ha => by rw [hl]; exact ha)
        (by rw [S.sx_iff, S.sx_iff, sph]; exact id) rfl rfl rfl rfl rfl
        (fun w hw _ => .inl hw) (fun _ _ _ h => h) (Nat.le_refl _) hcl, hW⟩,
      hS.mono (G' := upd G t g') (hup S.ph sph) (hup C.ph cph) hpv
        (fun u hp => by rw [hup L.ph hl u]; exact hS.pst u hp)
        (fun u hh => .inl (hheld u hh)) hcl (fun _ h => h) rfl hlgone (fun w hw => .inl hw) rfl
        rfl⟩
    win := hu.win.keep (hup C.ph cph) rfl rfl (hu.win.ehb.step
      (fun _ hc => hc.mono (fun u hh => .inl (hheld u hh)) hcl (fun _ h => h) rfl hlgone)
      (.inl rfl))
    shares := hu.shares.congr hwph (fun _ hv => hv) fun v l => by rw [hup M.part hpart]
    pin := hu.pin
    wt := fun u hq => by rw [hwph u]; exact hu.wt u (by rwa [hup S.ph sph u] at hq)
    nap := fun u hq => by
      rw [hup M.ph hm u]
      exact hu.nap u (by rwa [hup L.ph hl u, hup S.place.ph spl u] at hq)
    live := hu.live
    rdm := fun u hr => by
      rw [hup M.ph hm u]
      exact hu.rdm u (by rwa [hwph u] at hr)
    mal := fun u ha => by
      rw [hup M.ph hm u] at ha
      rw [hup L.ph hl u]
      exact hu.mal u ha }

/-- **The invariant of a protocol with the reader/writer lock, after the writer changed its
client part** (`setX` under the two-lock product: `FLock.Inv.congrG`, `FLock.Pair.U_relabel`):
thread `t` at `wr` goes from `g` to `g'` with the same places, part and held resources at both
mutexes. No thread is at `ww` (`Inv.one`), so the resource is not posted and the semaphore's pool
is empty before and after. -/
theorem inv_setX {t : ThreadId} {g g' : γ}
    (hi : ∃ rX, M.Inv (upd G t g) rX m ∧ FLock.Pair.U L (W.Base E Sz K) (upd G t g) rX m)
    (hw : W.ph g = .wr) (hwp : W.place.ph g' = W.place.ph g)
    (hmp : M.ph g' = M.ph g) (hmh : M.held g' = M.held g) (hpart : M.part g' = M.part g)
    (hlp : L.ph g' = L.ph g) (hlh : L.held g' = L.held g)
    (hT : E.T (W.xs (upd G t g')) m.threads) :
    ∃ rX, M.Inv (upd G t g') rX m ∧ FLock.Pair.U L (W.Base E Sz K) (upd G t g') rX m := by
  obtain ⟨rX, hM, hU⟩ := hi
  have hwph : ∀ u, W.ph (upd G t g' u) = W.ph (upd G t g u) :=
    congrFun (upd_map W.ph G t (congrArg Prod.fst hwp))
  have hone : ∀ u, W.ph (upd G t g u) ≠ .ww := by
    obtain ⟨_, _, _, _, _, _, _, hb⟩ := hU
    intro u hu
    have e := hb.winv.one u t (by rw [hu]; rfl) (by rw [upd_self, hw]; rfl)
    rw [e, upd_self, hw] at hu; cases hu
  have hnp : ∀ G₁ : ThreadId → γ, (∀ u, W.ph (G₁ u) ≠ .ww) → ¬ RwPosted W.ph G₁ :=
    fun _ h hp => by
      obtain ⟨⟨u, hu⟩, -⟩ := hp
      exact h u hu
  have hR : ∀ r, L.R (upd G t g) r → L.R (upd G t g') r := fun r h => by
    rw [S.R_cnt (upd G t g)] at h
    rw [S.R_cnt (upd G t g'), cnt_congr hwph]
    refine sep_mono_right (fun r' h' => ?_) h
    rw [W.pool_idle _ (hnp _ hone)] at h'
    rw [W.pool_idle _ (hnp _ fun u => by rw [hwph u]; exact hone u)]
    exact h'
  have hM' : M.Inv (upd G t g') rX m := hM.congrG
    (fun u => ⟨congrFun (upd_map M.ph G t hmp) u, congrFun (upd_map M.part G t hpart) u,
      congrFun (upd_map M.held G t hmh) u⟩)
    (fun r h => by rw [W.mR] at h ⊢; exact h)
  refine ⟨rX, hM', FLock.Pair.U_relabel hU hlp hlh hR (fun rL hf => ?_)
    (fun sB rL rH rX₀ _ _ _ hb => ?_)⟩
  · have h := hf.pdisj t
    rw [upd_self] at h
    rw [← W.pair.part, hpart, W.pair.part]; exact h
  · have h := hb.setX (t := t) (g' := g') (by rw [upd_self]; exact hw)
      (by rw [upd_self]; exact hwp) (by rw [upd_self]; exact hpart)
      (by rw [upd_self]; exact hmp) (by rw [upd_self]; exact hlp) (by rw [upd_upd]; exact hT)
    rwa [upd_upd] at h

/-! ## The lock's block and the program's threads -/

/-- **The lock's block is live, with the base's size and kind** (`FLock.Inv.pinned` at the base's
pin). -/
theorem inv_blk (hi : ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m) :
    ∃ blk, m.blocks[W.st.b]? = some blk ∧ blk.live = true ∧ blk.bytes.size = Sz ∧
      blk.kind = K := by
  obtain ⟨rX, hM, sB, rL, rH, rX₀, rfl, -, -, hb⟩ := hi
  obtain ⟨blk, h1, h2, h3, h4, -⟩ := hM.pinned (Res.Pins.right hb.pin)
  exact ⟨blk, h1, h2, h3, h4⟩

/-- The program's threads' fact, from the invariant. -/
theorem inv_thr (hi : ∃ rX, M.Inv G rX m ∧ FLock.Pair.U L (W.Base E Sz K) G rX m) :
    E.T (W.xs G) m.threads := by
  obtain ⟨rX, hM, sB, rL, rH, rX₀, rfl, -, -, hb⟩ := hi
  exact hb.cl.thr

end Base

end FRw

end Full
end Zig
