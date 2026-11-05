import Proofs.Threadsync.WaitGroup.Start
import Proofs.Threadsync.ThreadMutex
import Proofs.Threadsync.Event

/-!
# A task of `waitGroup` (full-state logic)

Each task (thread 1 or 2) runs `task`: it locks the `Thread.Mutex`, adds 1 to the counter
(load, add, store) and unlocks, then finishes (`WaitGroup.finish`: `fetchSub(2, acqRel)` on the
group's state; the task that reads 3 sets the `ResetEvent`). Its places are `lk` (before or in its
`lock`), `hl` (holding the mutex), `un` (after its store), then `st` (the setter, before its `set`)
or `fin`.

The task's operations are the library's contracts, used once each: `MutexImpl.lock_wp` /
`unlock_wp` (`wp_lockT`, `wp_unlockT`), `FLock.Fits.wp_hold` for the holder's steps (obligation
`U_hold`), `FLock.wp_wordRmw` for the finish's RMW (obligation `inv_fin`) and `EventImpl.set_wp`
for the setter (`wp_setT`, then its end `inv_end`). `fsym` walks `task` and `finish` with them
(`task_spec`, `finish_spec`), and `dispatch_spec` gives the spawn's obligation for each target.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn Threadsync

namespace Threadsync.WG

attribute [local irreducible] Proto.WP

/-- The setter after its finish (it read 3), before its `set`. -/
def gS (rp : Res) (fc : VClock) : Gh := (⟨.gone, rp, rnil⟩, { ph := .st, fc := fc, sx := true })

/-- A task after a finish that did not read 3. -/
def gN (rp : Res) (fc : VClock) : Gh := (⟨.gone, rp, rnil⟩, { ph := .fin, fc := fc })

/-- The setter at its end. -/
def gE (rp : Res) (fc : VClock) : Gh := (⟨.gone, rp, rnil⟩, { ph := .fin, fc := fc, sx := true })

/-! ## A task's places before its finish -/

theorem Ph.main_task {p : Ph} (h1 : p.isMain = true) (h2 : p.isTask = true) : False := by
  cases p <;> simp [Ph.isMain, Ph.isTask] at h1 h2

/-- **The threads' shape after a task moves to another task's place.** -/
theorem Shape.task {Y : ThreadId → X} {m : Mem} {t : ThreadId} {x : X} (h : Shape Y m)
    (ht : (Y t).ph.isTask = true) (hx : x.ph.isTask = true) : Shape (upd Y t x) m := by
  obtain ⟨h0, hm, h3, hc⟩ := h
  have t3 : t < 3 := Nat.lt_of_not_le fun h => by rw [h3 t h] at ht; exact absurd ht (by decide)
  have h3' : ∀ u, 3 ≤ u → upd Y t x u = {} := fun u hu => by
    rw [upd_ne _ _ (ne_of_lt3 hu t3)]; exact h3 u hu
  rcases lt3 t3 with rfl | rfl | rfl
  · exact (Ph.main_task hm ht).elim
  · have e0 : upd Y 1 x 0 = Y 0 := upd_ne _ _ (by decide)
    have e2 : upd Y 1 x 2 = Y 2 := upd_ne _ _ (by decide)
    refine ⟨h0, by rw [e0]; exact hm, h3', ?_⟩
    rw [e0, e2, upd_self]
    rcases hc with ⟨-, -, c, -⟩ | ⟨a, b, c, -, f⟩ | ⟨a, b, -, d, f, g⟩
    · rw [c] at ht; exact absurd ht (by decide)
    · exact .inr (.inl ⟨a, b, c, hx, f⟩)
    · exact .inr (.inr ⟨a, b, hx, d, f, g⟩)
  · have e0 : upd Y 2 x 0 = Y 0 := upd_ne _ _ (by decide)
    have e1 : upd Y 2 x 1 = Y 1 := upd_ne _ _ (by decide)
    refine ⟨h0, by rw [e0]; exact hm, h3', ?_⟩
    rw [e0, e1, upd_self]
    rcases hc with ⟨-, -, -, d⟩ | ⟨-, -, -, -, f⟩ | ⟨a, b, c, -, f, g⟩
    · rw [d] at ht; exact absurd ht (by decide)
    · rw [f] at ht; exact absurd ht (by decide)
    · exact .inr (.inr ⟨a, b, c, hx, f, g⟩)

/-- Two places of a thread that `U` reads alike (all but the place in the code itself). -/
structure XEq (x y : X) : Prop where
  e : x.e = y.e
  fc : x.fc = y.fc
  sx : x.sx = y.sx
  wk : x.wk = y.wk
  fd : x.ph.fd = y.ph.fd
  wa : x.ph.wa = y.ph.wa
  st : (x.ph = .st) = (y.ph = .st)
  fin : (x.ph = .fin) = (y.ph = .fin)

theorem XEq.refl (x : X) : XEq x x := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A task before its finish: in or before its lock, holding the mutex, or after its store. -/
def Ph.pre3 : Ph → Bool
  | .lk | .hl | .un => true
  | _ => false

/-- Two places of a task before its finish, with the same event place, clock and role. -/
theorem XEq.pre3 {x y : X} (hx : x.ph.pre3 = true) (hy : y.ph.pre3 = true) (he : x.e = y.e)
    (hfc : x.fc = y.fc) (hsx : x.sx = y.sx) (hwk : x.wk = y.wk) : XEq x y := by
  refine ⟨he, hfc, hsx, hwk, ?_, ?_, ?_, ?_⟩ <;>
  · revert hx hy; cases x.ph <;> cases y.ph <;> simp [Ph.pre3, Ph.fd, Ph.wa]

/-- **`U` after a change of the threads' places that `U` reads alike** (`XEq`), at the same
memory, with `main`'s place kept, the lock's places kept, the shape and the event's invariant. -/
theorem U_congr {G G' : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m)
    (hX : ∀ u, XEq (G' u).2 (G u).2) (h0 : (G' 0).2 = (G 0).2)
    (hP : ∀ u, (G' u).1.ph = (G u).1.ph) (hsh : Shape (fun u => (G' u).2) m)
    (hE : E.Inv L G' m) : U G' rX m := by
  refine ⟨hsh, hu.rest, hu.blk, hu.wg.anti fun u h => ?_, hu.ev.anti fun u h => ?_, hE, ?_,
    fun u h => ?_, fun u h => ?_, fun h0' h1 h2 => ?_, fun j hj hs => ?_, hu.one,
    fun u h1 h2 => ?_, fun u h => ?_, fun u h => ?_, fun u h => ?_, fun u h => ?_,
    fun u v h1 h2 => ?_, fun e he hb hk hl ho => ?_, fun h => ?_, hu.q⟩
  · unfold WLive at h ⊢; rw [← (hX u).fd]; exact h
  · change (G' u).2.ph.fd = false ∨ ((G' u).2.wk = true ∨ ((G' u).2.sx = true ∧
      (G' u).2.ph = .st)) ∧ ¬ (G' u).2.e.Setting at h
    change (G u).2.ph.fd = false ∨ ((G u).2.wk = true ∨ ((G u).2.sx = true ∧
      (G u).2.ph = .st)) ∧ ¬ (G u).2.e.Setting
    rw [(hX u).fd, (hX u).wk, (hX u).sx, (hX u).st, (hX u).e] at h; exact h
  · show (newest WG m).Val _
    have : wgv (G' 0).2 (G' 1).2 (G' 2).2 = wgv (G 0).2 (G 1).2 (G 2).2 := by
      unfold wgv X.fdn; rw [h0, (hX 1).fd, (hX 2).fd]
    rw [this]; exact hu.gv
  · rw [(hX u).fd] at h; rw [(hX u).fc]; exact hu.gw u h
  · rw [(hX u).sx] at h
    rw [h0, (hX 1).fd, (hX 2).fd, (hX u).st, (hX u).e, (hX 1).fc, (hX 2).fc]; exact hu.sto u h
  · rw [h0] at h0'; rw [(hX 1).fd] at h1; rw [(hX 2).fd] at h2
    obtain ⟨u, hu'⟩ := hu.last3 h0' h1 h2; exact ⟨u, by rw [(hX u).sx]; exact hu'⟩
  · rw [(hX 1).fc, (hX 2).fc]
    obtain ⟨⟨u, h1, h2⟩, h3, h4⟩ := hu.isw j hj hs
    exact ⟨⟨u, by rw [(hX u).sx]; exact h1, by rw [(hX u).e, (hX u).fin]; exact h2⟩, h3, h4⟩
  · rw [(hX u).sx] at h1; rw [(hX u).fin] at h2; exact hu.sfin u h1 h2
  · rw [(hX u).fd] at h; rw [hP u]; exact hu.lg u h
  · rw [hP u]; exact hu.out3 u h
  · rw [(hX u).wa] at h; exact hu.wa0 u h
  · rw [(hX u).wk] at h; rw [(hX u).wa]; exact hu.wk0 u h
  · rw [(hX u).sx] at h1; rw [(hX v).sx] at h2; exact hu.sx1 u v h1 h2
  · rcases hu.attr e he hb hk hl ho with h | ⟨u, hu12, h⟩ | h
    · exact .inl h
    · exact .inr (.inl ⟨u, hu12, by unfold bnd at h ⊢; rw [(hX u).fd, (hX u).fc]; exact h⟩)
    · exact .inr (.inr h)
  · rw [h0] at h; rw [(hX 1).fd, (hX 2).fd, (hX 1).fc, (hX 2).fc]
    obtain ⟨a, b, c, d, f, k⟩ := hu.done h
    exact ⟨a, b, c, d, f, fun u hs => by
      rw [(hX u).sx] at hs; rw [(hX u).e, (hX u).fin]; exact k u hs⟩

/-- **A task before its finish moves to another such place** (its lock's return, its store), at
the same memory, keeping its lock place, out of the event's code. -/
theorem U_task {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {g : Gh} (hu : U G rX m)
    (hp : (G t).2.ph.pre3 = true) (hp' : g.2.ph.pre3 = true) (he : g.2.e = .out)
    (he' : (G t).2.e = .out) (hfc : g.2.fc = (G t).2.fc) (hsx : g.2.sx = (G t).2.sx)
    (hwk : g.2.wk = (G t).2.wk) (hph : g.1.ph = (G t).1.ph) : U (upd G t g) rX m := by
  have hx : XEq g.2 (G t).2 := XEq.pre3 hp' hp (he.trans he'.symm) hfc hsx hwk
  have htk : ∀ {p : Ph}, p.pre3 = true → p.isTask = true := fun {p} h => by
    cases p <;> simp [Ph.pre3, Ph.isTask] at h ⊢
  have ht0 : t ≠ 0 := fun e => by
    subst e; exact Ph.main_task hu.shape.2.1 (htk hp)
  have hX : ∀ u, XEq (upd G t g u).2 (G u).2 := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; exact hx
    · rw [upd_ne _ _ e]; exact XEq.refl _
  refine U_congr hu hX (by rw [upd_ne _ _ (Ne.symm ht0)]) (fun u => ?_) ?_ ?_
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hph
    · rw [upd_ne _ _ e]
  · rw [upd_snd]; exact Shape.task hu.shape (htk hp) (htk hp')
  · exact hu.einv.relabel (fun u hu => upd_ne _ _ hu) (by rw [upd_self]; exact he.trans he'.symm)
      (fun h => absurd (by rw [upd_self]; exact he) h)
      (fun h => by
        have h' : (G t).2.wk = true := h
        rw [upd_self]; show g.2.wk = true; rw [hx.wk]; exact h')
      (fun h => by
        have h' : (G t).2.sx = true ∧ (G t).2.ph = .st := h
        rw [upd_self]; show g.2.sx = true ∧ g.2.ph = .st; rw [hx.sx, hx.st]; exact h')

/-- `R` reads only the threads' stores. -/
theorem R_congr {Y Y' : ThreadId → X} {r : Res} (h1 : (Y' 1).cnt = (Y 1).cnt)
    (h2 : (Y' 2).cnt = (Y 2).cnt) (h : R Y r) : R Y' r := by
  unfold R at h ⊢; rw [h1, h2]; exact h

/-- **The lock's invariant after a change of `t`'s places outside the lock** (the same lock
place, part and resource; the same store of the counter). -/
theorem L_relabel {G : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} {g₀ g₁ : Gh}
    (hL : L.Inv (upd G t g₀) rX m) (h1 : g₁.1 = g₀.1) (hc : g₁.2.cnt = g₀.2.cnt) :
    L.Inv (upd G t g₁) rX m := by
  have hcu : ∀ u, (upd G t g₁ u).2.cnt = (upd G t g₀ u).2.cnt := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, upd_self]; exact hc
    · rw [upd_ne _ _ e, upd_ne _ _ e]
  have := hL.relabel (t := t) (g := g₁) (by rw [upd_self]; show g₁.1.ph = g₀.1.ph; rw [h1])
    (by rw [upd_self]; show g₁.1.part = g₀.1.part; rw [h1])
    (by rw [upd_self]; show g₁.1.held = g₀.1.held; rw [h1])
    (fun r hR => by
      rw [upd_upd]
      exact R_congr (Y := fun u => (upd G t g₀ u).2) (Y' := fun u => (upd G t g₁ u).2)
        (hcu 1) (hcu 2) hR)
  rwa [upd_upd] at this

/-- **A task after its `lock`**: it holds the mutex at `hl`. -/
theorem inv_hl {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {rp rL : Res}
    (hi : proto.inv (upd G t (gH rp rL { ph := .lk })) m) :
    proto.inv (upd G t (gH rp rL { ph := .hl })) m := by
  obtain ⟨rX, hL, hu⟩ := hi
  refine ⟨rX, L_relabel hL rfl rfl, ?_⟩
  have := U_task (t := t) (g := gH rp rL { ph := .hl }) hu (by rw [upd_self]; rfl) rfl rfl
    (by rw [upd_self]; rfl) (by rw [upd_self]; rfl) (by rw [upd_self]; rfl) (by rw [upd_self]; rfl)
    (by rw [upd_self]; rfl)
  rwa [upd_upd] at this

/-! ## The holder's steps on the counter -/

/-- **A native step of `t` framed by the lock's word and the protocol's rest** (the holder's step,
`FLock.Fits.wp_hold`) keeps `U` with `t`'s new ghost value at the same places: the lock's
invariant after it pins the block and the cells of the two words (`cell_eq`). -/
theorem U_frame {G G'' : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    (hu : U G rX m) (hc : m.current = t) (hng : (G t).1.ph ≠ .gone)
    (hs : FStepIn (rsum (L.wordR m) rX).heap.erase m m') (hL : L.Inv G'' rX m')
    (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph) : U (upd G t g) rX m' := by
  obtain ⟨rB, hB, hBoff, hrX⟩ := hu.rest
  have hbk' : BlkOk m' := blk_of (hrX ▸ hL) hB rfl
  have hcs : ∀ l, BoxW l → m'.heap l = m.heap l := by
    rintro ⟨b, x⟩ ⟨h0, h1⟩
    simp only at h0 h1; subst h0
    refine cell_eq hu.blk hbk' hL (by omega) ?_
    rw [hrX]; simp only [FHeap.union_apply]
    rw [cellsAt_of (W := BoxW) ⟨rfl, h1⟩, hBoff _ ⟨rfl, h1⟩, Option.or_none]
  have hcov : ∀ l, BoxW l → (rsum (L.wordR m) rX).heap.erase l ≠ none :=
    fun l hl => frame_box hu.rest hl (box_live hu hl)
  have hnG : ∀ l, WG.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm :=
    fun l hl => by rw [hcs l (wg_box hl)]
  have hnE : ∀ l, EV.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm :=
    fun l hl => by rw [hcs l (ev_box hl)]
  exact U_own hu hs hc hng (hu.rest.congr hcs) hbk'
    (hu.wg.fstep hs (fun l hl => hcov l (wg_box hl)) hnG)
    (hu.ev.fstep hs (fun l hl => hcov l (ev_box hl)) hnE)
    (Word.hist_fstep hu.wg hs (fun l hl => hcov l (wg_box hl)) hnG)
    (Word.hist_fstep hu.ev hs (fun l hl => hcov l (ev_box hl)) hnE)
    (hu.einv.fresh.fstep hs (fun x h1 h2 => hcov _ (ev_box ⟨rfl, h1, h2⟩))
      (fun i l hl => (hu.ev.loc i l hl).1)) hX hph

/-- **The holder's load and store of the counter** keep `U` (the obligation of
`FLock.Fits.wp_hold`): its step at `hl` (`U_frame`), then its next place, `hl` (a load) or `un`
(the store). The places first: the walk tries the candidate places by them. -/
theorem U_hold {G G' : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} {rp rL r : Res}
    {x₀ x₁ : X} (hx : x₀ = { ph := .hl } ∧ (x₁ = { ph := .hl } ∨ x₁ = { ph := .un }))
    (hu : U (upd G t (gH rp rL x₀)) rX m) (hc : m.current = t)
    (hs : FStepIn (rsum (L.wordR m) rX).heap.erase m m') (hL : L.Inv G' rX m') :
    U (upd G t (gH rp r x₁)) rX m' := by
  obtain ⟨rfl, hx₁⟩ := hx
  have h1 := U_frame (g := gH rp r { ph := .hl }) hu hc (by rw [upd_self]; nofun) hs hL
    (by rw [upd_self]; rfl) (by rw [upd_self]; rfl)
  rw [upd_upd] at h1
  have h2 := U_task (t := t) (g := gH rp r x₁) h1 (by rw [upd_self]; rfl)
    (by rcases hx₁ with rfl | rfl <;> rfl) (by rcases hx₁ with rfl | rfl <;> rfl)
    (by rw [upd_self]; rfl) (by rw [upd_self]; rcases hx₁ with rfl | rfl <;> rfl)
    (by rw [upd_self]; rcases hx₁ with rfl | rfl <;> rfl)
    (by rw [upd_self]; rcases hx₁ with rfl | rfl <;> rfl) (by rw [upd_self]; rfl)
  rwa [upd_upd] at h2

/-- A task's store counts at most once. -/
theorem cnt_le1 (x : X) : x.cnt ≤ 1 := by unfold X.cnt; split <;> omega

theorem cnt1_le {Y : ThreadId → X} {m : Mem} (_ : Shape Y m) : (Y 1).cnt ≤ 1 := cnt_le1 _
theorem cnt2_le {Y : ThreadId → X} {m : Mem} (_ : Shape Y m) : (Y 2).cnt ≤ 1 := cnt_le1 _

theorem cnt_hl : ({ ph := .hl } : X).cnt = 0 := rfl
/-- The store of the counter (`hl` to `un`), on either side of the sum (the task's place in
`R`'s sum). -/
theorem cnt_un_l (n : Nat) : ({ ph := .un } : X).cnt + n = ({ ph := .hl } : X).cnt + n + 1 := by
  show 1 + n = 0 + n + 1; omega
theorem cnt_un_r (n : Nat) : n + ({ ph := .un } : X).cnt = n + ({ ph := .hl } : X).cnt + 1 := rfl

/-! ## The finish: `fetchSub(2, acqRel)` at the group's state -/

/-- A task after its finish: the setter (`b`: it read 3) at `st`, else at `fin`; `gone` for the
lock, with its clock after the RMW. -/
def gF (rp : Res) (c : VClock) (b : Bool) : Gh :=
  (⟨.gone, rp, rnil⟩, { ph := if b then .st else .fin, fc := c, sx := b })

theorem gS_eq (rp : Res) (c : VClock) : gS rp c = gF rp c true := rfl
theorem gN_eq (rp : Res) (c : VClock) : gN rp c = gF rp c false := rfl

theorem val_eq64 {x : Word.Entry} {a b : BitVec 64} (ha : x.Val a) (hb : x.Val b) : a = b := by
  unfold Word.Entry.Val at ha hb; rw [ha] at hb; cases hb; rfl

/-- The group's values at a finish: `4 + A - 2 * B` (`A`: `main` added, `B`: the other task
finished), then two less; it read 3 iff both. -/
theorem wg_arith {A B : Nat} (hA : A ≤ 1) (hB : B ≤ 1) :
    BitVec.ofNat 64 (4 + A - 2 * B) - 2 = BitVec.ofNat 64 (4 + A - 2 * (B + 1)) ∧
    (BitVec.ofNat 64 (4 + A - 2 * B) = 3 ↔ A = 1 ∧ B = 1) ∧
    (BitVec.ofNat 64 (4 + A - 2 * B) = 2 ∨ BitVec.ofNat 64 (4 + A - 2 * B) = 4 ∨
      BitVec.ofNat 64 (4 + A - 2 * B) = 5 ∨ BitVec.ofNat 64 (4 + A - 2 * B) = 3) := by
  rcases (by omega : A = 0 ∨ A = 1) with rfl | rfl <;>
    rcases (by omega : B = 0 ∨ B = 1) with rfl | rfl <;> decide

/-- The rest's part without the group's word: the cells of the other bytes below the mutex. -/
theorem rY_at {rY : Res} {m : Mem} (h : Rest (rsum (WG.cellsR m) rY) m) {l : Zig.Loc} (hb : BoxW l)
    (hw : ¬ WG.In l) : rY.heap l = (m.heap l).map fun c => ⟨c, none⟩ := by
  obtain ⟨rB, -, hB, hrX⟩ := h
  have := congrFun (congrArg Res.heap hrX) l
  simp only [FHeap.union_apply, Word.cellsR] at this
  rw [cellsAt_none hw, Option.none_or] at this
  rw [this, cellsAt_of hb, hB l hb, Option.or_none]

theorem Shape.threads {Y : ThreadId → X} {m m' : Mem} (h : Shape Y m)
    (ht : m'.threads = m.threads) : Shape Y m' := by
  unfold Shape at *; rw [ht]; exact h

/-- **The protocol after a task's finish** (`fetchSub(2, acqRel)` by `t` at `un`, out of the lock,
from the stop `G`, `m` to `m'`; the facts of `FLock.Fits.wp_wordRmw`): the task leaves the lock
for good with its clock after the RMW as its finish clock; it read 3 iff `main` added and the
other task finished, and then it is the setter, whose clock is above both finish clocks (the other's
by the release sequence and the RMW's acquire). -/
theorem inv_fin {G : ThreadId → Gh} {rY : Res} {m m' : Mem} {t : ThreadId} {rp : Res}
    {old : BitVec 64} (hg : G t = gO rp { ph := .un }) (hc : m.current = t)
    (hu : U G (rsum (WG.cellsR m) rY) m) (hY : ∀ l, WG.In l → rY.heap l = none)
    (hv : (newest WG m).Val old)
    (hh : WG.hist m' = (WG.hist m).push
      (Word.rmwEnt m' t .acqRel (newest WG m) (RmwOp.apply .sub false old 2)))
    (hacq : VClock.le (newest WG m).relClock (m'.clocks[t]!) = true)
    (hw' : WG.Ok m' (fun u => WLive (G u)))
    (hA : ∀ hF : Heap, (∀ x, WG.o ≤ x → x < WG.o + 8 → hF (WG.b, x) = none) → FStepIn hF m m')
    (hL : L.Inv G (rsum (WG.cellsR m') rY) m') :
    (old = 3 ∧ proto.inv (upd G t (gS rp (m'.clocks[t]!))) m') ∨
    ((old = 2 ∨ old = 4 ∨ old = 5) ∧ proto.inv (upd G t (gN rp (m'.clocks[t]!))) m') := by
  -- the task
  have hgt : (G t).1.ph ≠ .gone := by rw [hg]; nofun
  obtain ⟨ht3, -⟩ := live3 hu hgt
  have ht0 : t ≠ 0 := fun e => by
    subst e; have := hu.shape.2.1; change (G 0).2.ph.isMain = true at this
    rw [hg] at this; simp [gO, Ph.isMain] at this
  have ht12 : t = 1 ∨ t = 2 := by
    rcases lt3 ht3 with h | h | h
    · exact absurd h ht0
    · exact .inl h
    · exact .inr h
  have hpre : (G 0).2.ph ≠ .pre := by
    obtain ⟨-, -, -, hc3⟩ := hu.shape
    rcases hc3 with ⟨-, -, h1, h2⟩ | ⟨-, h0, -⟩ | ⟨-, h0, -⟩
    · change (G 1).2 = {} at h1; change (G 2).2 = {} at h2
      rcases ht12 with rfl | rfl
      · have := congrArg X.ph h1; rw [hg] at this; cases this
      · have := congrArg X.ph h2; rw [hg] at this; cases this
    · rw [h0]; nofun
    · intro h; rw [h] at h0; exact absurd h0 (by decide)
  -- the group's values
  have hfdt : (G t).2.ph.fd = false := by rw [hg]; rfl
  obtain ⟨A, B, hA1, hB1, hW0, hW1, hAw, hBo⟩ : ∃ A B : Nat, A ≤ 1 ∧ B ≤ 1 ∧
      wgv (G 0).2 (G 1).2 (G 2).2 = 4 + A - 2 * B ∧
      (∀ g : Gh, g.2.ph.fd = true →
        wgv (upd G t g 0).2 (upd G t g 1).2 (upd G t g 2).2 = 4 + A - 2 * (B + 1)) ∧
      ((G 0).2.ph.wa = true ↔ A = 1) ∧
      ∀ u, (u = 1 ∨ u = 2) → u ≠ t → ((G u).2.ph.fd = true ↔ B = 1) := by
    have hft : (G t).2.fdn = 0 := by unfold X.fdn; rw [hfdt]; rfl
    have hle : ∀ x : X, x.fdn ≤ 1 := fun x => by unfold X.fdn; split <;> omega
    refine ⟨if (G 0).2.ph.wa then 1 else 0, (G 1).2.fdn + (G 2).2.fdn, by split <;> omega, ?_, ?_,
      fun g hgfd => ?_, by cases (G 0).2.ph.wa <;> simp, ?_⟩
    · rcases ht12 with rfl | rfl
      · rw [hft]; have := hle (G 2).2; omega
      · rw [hft]; have := hle (G 1).2; omega
    · unfold wgv; rw [ite_eq_right hpre]
    · have h0 : (upd G t g 0).2 = (G 0).2 := by rw [upd_ne _ _ (Ne.symm ht0)]
      have hg1 : g.2.fdn = 1 := by unfold X.fdn; rw [hgfd]; rfl
      unfold wgv; rw [h0, ite_eq_right hpre]
      rcases ht12 with rfl | rfl
      · rw [upd_self, upd_ne _ _ (by decide : (2 : Nat) ≠ 1), hg1, hft]; omega
      · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 2), hg1, hft]
    · rintro u hu12 hne
      rcases hu12 with rfl | rfl <;> rcases ht12 with rfl | rfl
      · exact absurd rfl hne
      · rw [hft]; unfold X.fdn; cases (G 1).2.ph.fd <;> simp
      · rw [hft]; unfold X.fdn; cases (G 2).2.ph.fd <;> simp
      · exact absurd rfl hne
  have hold : old = BitVec.ofNat 64 (4 + A - 2 * B) := by
    rw [← hW0]; exact val_eq64 hv hu.gv
  obtain ⟨hsub, h3, hcases⟩ := wg_arith hA1 hB1
  -- the step's facts
  have hs : FStepIn rY.heap.erase m m' := hA _ fun x h1 h2 => by
    simp [FHeap.erase, hY (WG.b, x) ⟨rfl, h1, h2⟩]
  obtain ⟨rB, hB, -, hrX⟩ := hu.rest
  have hgB : rY.gh = rB.gh := by
    have := congrArg Res.gh hrX; simpa [cellsAt, Word.cellsR] using this
  have hbk' : BlkOk m' := blk_of hL hB hgB
  have hcs : ∀ l, BoxW l → ¬ WG.In l → m'.heap l = m.heap l := by
    rintro ⟨b, x⟩ ⟨h0, h1⟩ hw
    simp only at h0 h1; subst h0
    refine cell_eq hu.blk hbk' hL (by omega) ?_
    simp only [FHeap.union_apply, Word.cellsR]
    rw [cellsAt_none hw, Option.none_or, rY_at hu.rest ⟨rfl, h1⟩ hw]
  have hcovE : ∀ l, EV.In l → rY.heap.erase l ≠ none := fun l hl => by
    simp only [FHeap.erase, ne_eq, Option.map_eq_none_iff]
    rw [rY_at hu.rest (ev_box hl) (fun h => wg_ev h hl)]
    simpa using box_live hu (ev_box hl)
  have hnE : ∀ l, EV.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm :=
    fun l hl => by rw [hcs l (ev_box hl) (fun h => wg_ev h hl)]
  have hwE := hu.ev.fstep hs hcovE hnE
  have hhE : EV.hist m' = EV.hist m := Word.hist_fstep hu.ev hs hcovE hnE
  have hfr : EV.Fresh m' := hu.einv.fresh.fstep hs (fun x h1 h2 => hcovE _ ⟨rfl, h1, h2⟩)
    (fun i l hl => (hu.ev.loc i l hl).1)
  have hclk := hs.clock
  have hcm : m.current = t := hc
  -- no thread has the setter's role yet: `t` did not finish
  have hnosx : ∀ u, (G u).2.sx = true → False := fun u h => by
    obtain ⟨-, -, h1, h2, -⟩ := hu.sto u h
    rcases ht12 with rfl | rfl
    · rw [hfdt] at h1; cases h1
    · rw [hfdt] at h2; cases h2
  -- the new ghost value
  suffices key : ∀ b : Bool, (b = true ↔ old = 3) →
      proto.inv (upd G t (gF rp (m'.clocks[t]!) b)) m' by
    by_cases e : old = 3
    · exact .inl ⟨e, key true (iff_of_true rfl e)⟩
    · refine .inr ⟨?_, key false (iff_of_false (by decide) e)⟩
      rw [hold] at e ⊢; rcases hcases with h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
      · exact absurd h e
  intro b hb
  have hb3 : b = true ↔ A = 1 ∧ B = 1 := by rw [hb, hold]; exact h3
  let g' : Gh := gF rp (m'.clocks[t]!) b
  show proto.inv (upd G t g') m'
  have hG : ∀ u, u ≠ t → upd G t g' u = G u := fun u h => upd_ne _ _ h
  have hGt : upd G t g' t = g' := upd_self _ _ _
  have hfd' : g'.2.ph.fd = true := by
    show (if b then Ph.st else Ph.fin).fd = true; cases b <;> rfl
  have hwa' : g'.2.ph.wa = false := by
    show (if b then Ph.st else Ph.fin).wa = false; cases b <;> rfl
  have hfin' : g'.2.ph = .fin ↔ b = false := by
    show (if b then Ph.st else Ph.fin) = .fin ↔ b = false; cases b <;> simp
  -- both tasks finished after it iff the other did
  have hbothfd : B = 1 → ∀ u, (u = 1 ∨ u = 2) → (upd G t g' u).2.ph.fd = true := fun hB u hu12 => by
    by_cases e : u = t
    · subst e; rw [hGt]; exact hfd'
    · rw [hG u e]; exact (hBo u hu12 e).mpr hB
  have hbnd : ∀ u, VClock.le (bnd G m u) (bnd (upd G t g') m' u) = true := fun u => by
    by_cases e : u = t
    · subst e; unfold bnd; rw [hGt, hfd', hfdt]; exact hclk _
    · unfold bnd; rw [hG u e]; split
      · exact VClock.le_refl _
      · exact hclk u
  have hnew : newest WG m' = Word.rmwEnt m' t .acqRel (newest WG m) (RmwOp.apply .sub false old 2) :=
    newest_push hh
  refine ⟨rsum (WG.cellsR m') rY, ?_, ?_⟩
  · -- the lock: `t` leaves it for good; the counter keeps its store
    refine hL.ghost (t := t) (g := g') (by rw [hg]; rfl) (.inr (.inl rfl)) (by rw [hg]; rfl) rfl
      (fun h => absurd rfl h) (fun r hR => ?_)
    have hcu : ∀ u, (upd G t g' u).2.cnt = (G u).2.cnt := fun u => by
      by_cases e : u = t
      · subst e; rw [hGt, hg]; cases b <;> rfl
      · rw [hG u e]
    exact R_congr (Y := fun u => (G u).2) (Y' := fun u => (upd G t g' u).2) (hcu 1) (hcu 2) hR
  refine ⟨?_, Rest.step (fun _ => wg_box) hu.rest rfl hY hcs, hbk',
    hw'.anti fun u h => ?_, hwE.anti fun u h => ?_, ?_, ?_, fun u h => ?_, fun u h => ?_,
    fun h0 h1 h2 => ?_, fun j hj hsj => ?_, ?_, fun u h1 h2 => ?_, fun u h => ?_, fun u h3 => ?_,
    fun u h => ?_, fun u h => ?_, fun u v h1 h2 => ?_, fun e he hb0 hk hl ho => ?_, fun h => ?_, ?_⟩
  · -- shape
    rw [upd_snd]
    exact (Shape.task hu.shape (by rw [hg]; rfl) (by cases b <;> rfl)).threads hs.threads
  · -- the group's live set: `t` leaves it
    by_cases e : u = t
    · subst e; unfold WLive at h; rw [hGt, hfd'] at h; cases h
    · rwa [hG u e] at h
  · -- the event's live set: `t` was in it (before its finish)
    by_cases e : u = t
    · subst e; exact .inl hfdt
    · rwa [hG u e] at h
  · -- the event: its word stays; `t` stays out of its code
    have hI := hu.einv.frame (t := t) (G' := G) (fun _ _ => rfl) rfl rfl hhE hs.waiters hclk
      (Nat.le_of_eq (by rw [hs.threads])) id id hfr
    refine hI.relabel (fun u hu => upd_ne _ _ hu) (by rw [hGt, hg]; rfl)
      (fun h => absurd (by rw [hGt]; rfl) h) (fun h => ?_) (fun h => ?_)
    · have h' : (G t).2.wk = true := h; rw [hg] at h'; cases h'
    · exact (hnosx t h.1).elim
  · -- gv: two less
    show (newest WG m').Val _
    rw [hnew, hW1 g' hfd', ← hsub, ← hold]; exact intOfBytes_rmw _
  · -- gw: the RMW continues the release sequence and releases `t`'s clock
    rw [hnew]
    show VClock.le _ (VClock.merge (newest WG m).relClock (m'.clocks[t]!)) = true
    by_cases e : u = t
    · subst e; rw [hGt]; exact VClock.le_merge_right _ _
    · rw [hG u e] at h ⊢
      exact VClock.le_trans (hu.gw u h) (VClock.le_merge_left _ _)
  · -- sto: the setter is `t`
    by_cases e : u = t
    · subst e
      rw [hGt] at h
      obtain ⟨hA', hB'⟩ := hb3.mp h
      have h0 : (upd G u g' 0).2 = (G 0).2 := by rw [hG 0 (Ne.symm ht0)]
      refine ⟨ht12, by rw [h0]; exact hAw.mpr hA', hbothfd hB' 1 (.inl rfl), hbothfd hB' 2 (.inr rfl),
        fun _ _ => ?_⟩
      -- the other task's finish clock is below the RMW's release clock it acquired
      have hle : ∀ v, (v = 1 ∨ v = 2) →
          VClock.le (upd G u g' v).2.fc (m'.clocks[u]!) = true := fun v hv => by
        by_cases e' : v = u
        · subst e'; rw [hGt]; exact VClock.le_refl _
        · rw [hG v e']
          exact VClock.le_trans (hu.gw v ((hBo v hv e').mpr hB')) hacq
      exact ⟨hle 1 (.inl rfl), hle 2 (.inr rfl)⟩
    · rw [hG u e] at h; exact (hnosx u h).elim
  · -- last3: `main` the waiter and both finished: `t` read 3
    have h0w : (G 0).2.wk = true := by rwa [hG 0 (Ne.symm ht0)] at h0
    have hB' : B = 1 := by
      rcases ht12 with rfl | rfl
      · rw [hG 2 (by decide)] at h2; exact (hBo 2 (.inr rfl) (by decide)).mp h2
      · rw [hG 1 (by decide)] at h1; exact (hBo 1 (.inl rfl) (by decide)).mp h1
    have hA' : A = 1 := hAw.mp (hu.wk0 0 h0w).2
    exact ⟨t, by rw [hGt]; exact hb3.mpr ⟨hA', hB'⟩⟩
  · -- isw: no `is_set` write before the setter's
    unfold IsSetW at hsj; rw [hhE] at hj hsj
    obtain ⟨⟨u, h1, -⟩, -⟩ := hu.isw j hj hsj
    exact (hnosx u h1).elim
  · intro i hi j hj h1 h2; unfold IsSetW at h1 h2; rw [hhE] at hi hj h1 h2
    exact hu.one i hi j hj h1 h2
  · -- sfin: the setter is at `st`
    by_cases e : u = t
    · subst e; rw [hGt] at h1 h2
      have h1' : b = true := h1
      rw [hfin'.mp h2] at h1'; cases h1'
    · rw [hG u e] at h1; exact (hnosx u h1).elim
  · by_cases e : u = t
    · subst e; rw [hGt]; rfl
    · rw [hG u e] at h ⊢; exact hu.lg u h
  · rw [hG u (ne_of_lt3 h3 ht3)]; exact hu.out3 u h3
  · by_cases e : u = t
    · subst e; rw [hGt, hwa'] at h; cases h
    · rw [hG u e] at h; exact hu.wa0 u h
  · by_cases e : u = t
    · subst e; rw [hGt] at h; cases h
    · rw [hG u e] at h ⊢; exact hu.wk0 u h
  · have hu' : u = t := Classical.byContradiction fun e => by
      rw [hG u e] at h1; exact hnosx u h1
    have hv' : v = t := Classical.byContradiction fun e => by
      rw [hG v e] at h2; exact hnosx v h2
    rw [hu', hv']
  · -- attr: the RMW's write access is below `t`'s finish clock
    rw [hhE]
    rcases hs.fpc e he with ⟨e₀, he₀, hn⟩ | hle
    · have hp := narrows_box hn hl ho
      obtain ⟨-, hb₀, hk₀, -, -, hc'⟩ := hn
      rcases hu.attr e₀ he₀ (hb₀ ▸ hb0) (hk₀ ▸ hk) hp.1 hp.2 with h | ⟨u, hu12, h⟩ | ⟨j, hj, hsj, h⟩
      · exact .inl (VClock.le_trans hc' (VClock.le_trans h (hclk 0)))
      · exact .inr (.inl ⟨u, hu12, VClock.le_trans hc' (VClock.le_trans h (hbnd u))⟩)
      · refine .inr (.inr ⟨j, hj, ?_, VClock.le_trans hc' h⟩)
        unfold IsSetW; rw [hhE]; exact hsj
    · refine .inr (.inl ⟨t, ht12, ?_⟩)
      unfold bnd; rw [hGt, hfd']; rw [hcm] at hle; exact hle
  · -- done: `main` did not pass its wait (`t` had not finished)
    rw [hG 0 (Ne.symm ht0)] at h
    obtain ⟨h1, h2, -⟩ := hu.done h
    rcases ht12 with rfl | rfl
    · rw [hfdt] at h1; cases h1
    · rw [hfdt] at h2; cases h2
  · intro w hw; rw [hs.waiters] at hw; exact hu.q w hw

/-- **`U` after the setter's end**: `t` (not `main`, past its finish) moves to `fin` at the same
memory, keeping its lock place, finish clock and roles, with the event set (`sfin`). `sto`'s clock
clause holds only at `st`, and every `is_set` write has the setter at `fin`. -/
theorem U_end {G₀ G₁ : ThreadId → Gh} {rX : Res} {m : Mem} {t : ThreadId} (hu : U G₀ rX m)
    (hset : E.IsSet m) (ht0 : t ≠ 0) (hne : ∀ u, u ≠ t → G₁ u = G₀ u)
    (hP : (G₁ t).1.ph = (G₀ t).1.ph) (hfc : (G₁ t).2.fc = (G₀ t).2.fc)
    (hsx : (G₁ t).2.sx = (G₀ t).2.sx) (hwk : (G₁ t).2.wk = (G₀ t).2.wk)
    (hfd : (G₀ t).2.ph.fd = true) (hfin : (G₁ t).2.ph = .fin) (hsxt : (G₁ t).2.sx = true)
    (hsh : Shape (fun u => (G₁ u).2) m) (hE : E.Inv L G₁ m) : U G₁ rX m := by
  have lift : ∀ {α : Type} (f : Gh → α), f (G₁ t) = f (G₀ t) → ∀ u, f (G₁ u) = f (G₀ u) :=
    fun f h u => by
      by_cases e : u = t
      · subst e; exact h
      · rw [hne u e]
  have hwa0 : (G₀ t).2.ph.wa = false := Bool.eq_false_iff.mpr fun h => ht0 (hu.wa0 t h)
  have hfd' : ∀ u, (G₁ u).2.ph.fd = (G₀ u).2.ph.fd :=
    lift (fun g => g.2.ph.fd) (by show (G₁ t).2.ph.fd = _; rw [hfin, hfd]; rfl)
  have hwa' : ∀ u, (G₁ u).2.ph.wa = (G₀ u).2.ph.wa :=
    lift (fun g => g.2.ph.wa) (by show (G₁ t).2.ph.wa = _; rw [hfin, hwa0]; rfl)
  have hfc' : ∀ u, (G₁ u).2.fc = (G₀ u).2.fc := lift (fun g => g.2.fc) hfc
  have hsx' : ∀ u, (G₁ u).2.sx = (G₀ u).2.sx := lift (fun g => g.2.sx) hsx
  have hwk' : ∀ u, (G₁ u).2.wk = (G₀ u).2.wk := lift (fun g => g.2.wk) hwk
  have hP' : ∀ u, (G₁ u).1.ph = (G₀ u).1.ph := lift (fun g => g.1.ph) hP
  have h0 : G₁ 0 = G₀ 0 := hne 0 (Ne.symm ht0)
  refine ⟨hsh, hu.rest, hu.blk, hu.wg.anti fun u h => ?_, hu.ev.anti fun u h => ?_, hE, ?_,
    fun u h => ?_, fun u h => ?_, fun _ _ _ => ⟨t, hsxt⟩, fun j hj hs => ?_, hu.one,
    fun _ _ _ => hset, fun u h => ?_, fun u h => ?_, fun u h => ?_, fun u h => ?_,
    fun u v h1 h2 => ?_, fun e he hb hk hl ho => ?_, fun h => ?_, hu.q⟩
  · unfold WLive at h ⊢; rw [← hfd' u]; exact h
  · by_cases e : u = t
    · subst e; exfalso
      change (G₁ u).2.ph.fd = false ∨ ((G₁ u).2.wk = true ∨ ((G₁ u).2.sx = true ∧
        (G₁ u).2.ph = .st)) ∧ ¬ (G₁ u).2.e.Setting at h
      rw [hfin] at h
      rcases h with h | ⟨h | ⟨-, h⟩, -⟩
      · exact absurd h (by decide)
      · rw [hwk] at h; exact ht0 (hu.wk0 _ h).1
      · cases h
    · rwa [hne u e] at h
  · show (newest WG m).Val _
    have : wgv (G₁ 0).2 (G₁ 1).2 (G₁ 2).2 = wgv (G₀ 0).2 (G₀ 1).2 (G₀ 2).2 := by
      unfold wgv X.fdn; rw [h0, hfd' 1, hfd' 2]
    rw [this]; exact hu.gv
  · rw [hfd' u] at h; rw [hfc' u]; exact hu.gw u h
  · rw [hsx' u] at h
    obtain ⟨a, b, c, d, f⟩ := hu.sto u h
    refine ⟨a, by rw [h0]; exact b, by rw [hfd' 1]; exact c, by rw [hfd' 2]; exact d,
      fun hs he => ?_⟩
    by_cases e : u = t
    · subst e; rw [hfin] at hs; cases hs
    · rw [hne u e] at hs he; rw [hfc' 1, hfc' 2]; exact f hs he
  · obtain ⟨-, h3, h4⟩ := hu.isw j hj hs
    exact ⟨⟨t, hsxt, .inr hfin⟩, by rw [hfc' 1]; exact h3, by rw [hfc' 2]; exact h4⟩
  · rw [hfd' u] at h; rw [hP' u]; exact hu.lg u h
  · rw [hP' u]; exact hu.out3 u h
  · rw [hwa' u] at h; exact hu.wa0 u h
  · rw [hwk' u] at h; rw [hwa' u]; exact hu.wk0 u h
  · rw [hsx' u] at h1; rw [hsx' v] at h2; exact hu.sx1 u v h1 h2
  · rcases hu.attr e he hb hk hl ho with h | ⟨u, hu12, h⟩ | h
    · exact .inl h
    · exact .inr (.inl ⟨u, hu12, by unfold bnd at h ⊢; rw [hfd' u, hfc' u]; exact h⟩)
    · exact .inr (.inr h)
  · rw [h0] at h; rw [hfd' 1, hfd' 2, hfc' 1, hfc' 2]
    obtain ⟨a, b, c, d, f, k⟩ := hu.done h
    refine ⟨a, b, c, d, f, fun u hs => ?_⟩
    by_cases e : u = t
    · subst e; exact .inr hfin
    · rw [hne u e] at hs ⊢; exact k u hs

/-- **The protocol after the setter's end** (from its `set`'s end at `sd`, the event set): it
leaves the event's code and finishes. -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {rp : Res} {fc : VClock}
    (hi : proto.inv (upd G t (E.set (gS rp fc) .sd)) m) (hset : E.IsSet m) :
    proto.inv (upd G t (gE rp fc)) m := by
  obtain ⟨rX, hL, hu⟩ := hi
  have ht0 : t ≠ 0 := fun e => by
    subst e; have := hu.shape.2.1
    change (upd G 0 (E.set (gS rp fc) .sd) 0).2.ph.isMain = true at this
    rw [upd_self] at this; exact Bool.false_ne_true this
  have hsh : Shape (fun u => (upd G t (gE rp fc) u).2) m := by
    have hs := hu.shape; rw [upd_snd] at hs ⊢
    have := Shape.task hs (t := t) (x := (gE rp fc).2) (by rw [upd_self]; rfl) rfl
    rwa [upd_upd] at this
  have hE : E.Inv L (upd G t (gE rp fc)) m := by
    have := hu.einv.toOut (t := t) (g := gE rp fc) (by rw [upd_self]; exact .inr rfl) (.inl rfl)
      (fun h => by cases h)
      (fun h => by
        have h' : (upd G t (E.set (gS rp fc) .sd) t).2.wk = true := h
        rw [upd_self] at h'; cases h')
      (fun h => by cases h)
    rwa [upd_upd] at this
  refine ⟨rX, L_relabel hL rfl rfl, U_end hu hset ht0 (fun u h => by rw [upd_ne _ _ h, upd_ne _ _ h])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsh hE⟩ <;> simp only [upd_self] <;> rfl

section Sync

variable (mi : MutexImpl Tgt) (ei : EventImpl Tgt)

theorem wp_lockT (hLc : L.c = mi.c) {p : Ptr} (hp : p = L.ptr) (io : Io) {t : ThreadId}
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {rp : Res} (hpP : rp.Plain)
    (hi : proto.inv (upd G t (gO rp { ph := .lk })) m) :
    proto.WP t (mi.lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, proto.inv (upd G' t (gH rp rL { ph := .hl })) m') G m d :=
  WP.mono (fun _ _ _ _ ⟨hd, hc, rL, hi'⟩ => ⟨hd, hc, rL, inv_hl hi'⟩)
    (mi.lock_wp fitsL rfl hp hLc t (gO rp { ph := .lk }) rfl ⟨rfl, nofun⟩ hpP.unmetered io G m d hi)

theorem wp_unlockT (hLc : L.c = mi.c) {p : Ptr} (hp : p = L.ptr) (io : Io) {t : ThreadId}
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {rp rL : Res}
    (hi : proto.inv (upd G t (gH rp rL { ph := .un })) m) (hc : m.current = t) :
    proto.WP t (mi.unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      proto.inv (upd G' t (gO rp { ph := .un })) m') G m d :=
  mi.unlock_wp fitsL rfl hp hLc t (gH rp rL { ph := .un }) rfl ⟨rfl, nofun⟩ io G m d hi hc

theorem wp_setT {p : Ptr} (hp : p = EV.ptr) (io : Io) {t : ThreadId} {G : ThreadId → Gh} {m : Mem}
    {d : Nat} {rp : Res} {fc : VClock} (hi : proto.inv (upd G t (gS rp fc)) m) :
    proto.WP t (ei.set p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      proto.inv (upd G' t (gE rp fc)) m') G m d :=
  WP.mono (fun _ _ _ _ ⟨hd, hc, hs, hi'⟩ => ⟨hd, hc, inv_end hi' hs⟩)
    (ei.set_wp fitsE rfl hp t (gS rp fc) rfl (.inr rfl) ⟨rfl, rfl⟩ io G m d hi)

end Sync

theorem wp_finRmw {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh} {m : Mem} {n : Nat}
    {rp : Res} (hi : proto.inv (upd G t (gO rp { ph := .un })) m)
    {Q : BitVec 64 × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' (old : BitVec 64), m'.current = t →
      ((old = 3 ∧ proto.inv (upd G₁ t (gS rp (m'.clocks[t]!))) m') ∨
       ((old = 2 ∨ old = 4 ∨ old = 5) ∧ proto.inv (upd G₁ t (gN rp (m'.clocks[t]!))) m')) →
      Q (old, s) G₁ m' k) :
    proto.WP t ((atomicRmwC .sub false .acqRel 8 bPtr (2 : BitVec 64) : CM Tgt σ (BitVec 64)).run s)
      Q G m n := by
  show proto.WP t ((atomicRmwC .sub false .acqRel 8 WG.ptr (2 : BitVec 64) : CM Tgt σ (BitVec 64)).run s)
    Q G m n
  refine FLock.wp_wordRmw fitsL wg_inRest apG hi
    (fun k hk G₁ rY m₁ m' old hg₁ hc₁ hU _ hY hv _ hh hacq hw' _ _ _ hA _ _ hL => ?_) rfl rfl
  have hs := hA (fun _ => none) (fun _ _ _ => rfl)
  exact h k hk G₁ m' old (by rw [hs.current, hc₁])
    (inv_fin hg₁ hc₁ hU hY hv hh (hacq rfl) hw' hA hL)

variable [Zig.Os.HasEnv]

theorem finish_spec {t : ThreadId} (G : ThreadId → Gh) (m : Mem) (d : Nat) {rp : Res}
    (hi : proto.inv (upd G t (gO rp { ph := .un })) m) (hc : m.current = t) :
    proto.WP t (Thread_WaitGroup_finish bPtr) (fun _ G' m' _ => m'.current = t ∧
      ∃ g, proto.fin g ∧ proto.inv (upd G' t g) m') G m d := by
  unfold Thread_WaitGroup_finish
  fsym [WP.liftMem_pure (projI _ _) rfl, fitsL.wp_tick_plain, wp_finRmw,
    debug_assert, wp_setT resetEvent rfl ⟨⟩]

/-! ## A task -/

set_option maxHeartbeats 800000 in
/-- **A task** (thread 1 or 2, at `lk` with a plain part `rp`): `lock`, the counter's load, `+ 1`
and store (the holder's steps, `FLock.Fits.wp_hold`, at `hl` and to `un`), `unlock`, and the
group's `finish` (`finish_spec`); it ends `gone` at `fin`, out of the event's code. The walk splits
on the thread (the counter's sum reads both tasks' stores). -/
theorem task_spec {u : ThreadId} (G : ThreadId → Gh) (m : Mem) (d : Nat) {rp : Res} (hp : rp.Plain)
    (_hu : u = 1 ∨ u = 2) (hi : proto.inv (upd G u (gO rp { ph := .lk })) m) (hc : m.current = u) :
    proto.WP u (task bPtr) (fun _ G' m' _ => m'.current = u ∧
      ∃ g, proto.fin g ∧ proto.inv (upd G' u g) m') G m d := by
  unfold task
  fsym [WP.liftMem_pure (projI _ _) rfl, fitsL.wp_tick_plain, wp_lockT threadMutex rfl rfl ⟨⟩ hp,
    wp_unlockT threadMutex rfl rfl ⟨⟩, fitsL.wp_hold (g' := fun r => gH rp r { ph := .hl }),
    fitsL.wp_hold (g' := fun r => gH rp r { ph := .un }), U_hold, cnt1_le, cnt2_le, cnt_un_l,
    cnt_un_r, cnt_hl, Nat.zero_add, Nat.add_zero, finish_spec]

omit [Zig.Os.HasEnv] in
/-- **A task's end** (`QKid`), for any ghost value at the protocol's end. -/
theorem qkid_fin {G : ThreadId → Gh} {m : Mem} {d : Nat} {u : ThreadId} (hu : 0 < u) {g : Gh}
    (hg : proto.fin g) (hi : proto.inv (upd G u g) m) : proto.QKid u () G m d := by
  refine ⟨g, hi, hg, fun _ => ?_⟩
  obtain ⟨rX, -, hU⟩ := hi
  exact joinedAll_of_main (spawners hU.shape) hu

omit [Zig.Os.HasEnv] in
theorem dispatch_task (p : Ptr) : dispatch (Tgt.task p) = (fun _ => ()) <$> task p := rfl

/-- **A spawned thread runs a task** (the protocol's `init`: the `producer` and `work` targets are
not this program's), from its place `lk` to its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | task p =>
    obtain ⟨rfl, rp, hpP, rfl⟩ := hg
    have hu12 : u = 1 ∨ u = 2 := by
      obtain ⟨rX, -, hU⟩ := id hi
      have ht : (G u).2.ph.isTask = true := by rw [hgu]; rfl
      obtain ⟨-, hm, h3, -⟩ := hU.shape
      have hu3 : u < 3 := Nat.lt_of_not_le fun h => by
        have := h3 u h; change (G u).2 = {} at this; rw [this] at ht; exact absurd ht (by decide)
      rcases lt3 hu3 with rfl | h | h
      · exact absurd hu (by decide)
      · exact .inl h
      · exact .inr h
    rw [dispatch_task]
    refine WP.map (WP.mono ?_ (task_spec G _ d (Res.plain_of hpP) hu12
      (by rw [show gO rp { ph := .lk } = G u from hgu.symm, upd_same]
          exact inv_cur u hi (by rw [hgu]; nofun)) rfl))
    rintro _ G' m' _ ⟨-, g', hfin, hi'⟩
    exact qkid_fin hu hfin hi'
  | producer p => exact hg.elim
  | work p => exact hg.elim

end Threadsync.WG
