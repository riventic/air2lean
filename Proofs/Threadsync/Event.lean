import Proofs.Threadsync.Deadline
import ZigLean.Sep.Full.Event
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.AutoWP

/-!
# `Thread.ResetEvent` of `examples/threadsync` as an event (`EventImpl`, 0.15.2)

The per-item obligation of `Thread.ResetEvent` (0.15.2's `FutexImpl`: the futex event of
`ZigLean/Sep/Full/Event.lean` on bits) in this program's generated code: `wait` (`isSet`, then
`waitUntilSet` with no timeout, whose `Deadline` block is on the waiter's stack:
`Proofs/Threadsync/Deadline.lean`, `FEvent.wp_liftPart`) and `set`, walked with the rules of the
futex event, for every protocol that has the event next to a lock. `waitUntilSet` reaches the
translated `std.time.Timer` (OSK-01), so it takes the OS environment: the results hold for every
`[Zig.Os.HasEnv]`.
-/

open Zig Zig.Conc Zig.Full Zig.Full.FAssn Zig.Conc.Proto

namespace Threadsync

-- Unification must not unfold `WP` into the generated program.
attribute [local irreducible] Proto.WP

theorem debugAssert_true : (debug_assert true).run = some (.ok ()) := rfl

namespace ResetEvent

variable {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- `FutexImpl.set` by a thread out of the event's and the lock's code. -/
theorem futexSet_wp (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : E.ph g = .out) (hgo : L.ph g = .out) (hsx : E.sx g)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_ResetEvent_FutexImpl_set E.W.ptr) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ E.IsSet m' ∧ P.inv (upd G' t g) m') G m d := by
  unfold Thread_ResetEvent_FutexImpl_set
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FEvent.wp_peek hE hgx hgo hi fun k hk G₁ m₁ b hc₁ hi₁ hb2 => ?_)
  by_cases hb : b = 2
  · subst hb
    simp only [show ((2 : BitVec 32) == 2) = true from rfl, ↓reduceIte, StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨by omega, hc₁, hb2 rfl, hi₁⟩)
  simp only [show (b == 2) = false from beq_false_of_ne hb, Bool.false_eq_true, ↓reduceIte,
    StateT.run_pure, pure_bind, StateT.run_bind]
  refine WP.bind (FEvent.wp_xchg hE rfl hgx hgo hsx hi₁
    fun k₂ hk₂ G₂ m₂ o hc₂ hs₂ hcase => ?_)
  rcases hcase with ⟨rfl, hi₂⟩ | ⟨ho, hi₂⟩
  · simp only [show ((1 : BitVec 32) == 1) = true from rfl, ↓reduceIte, StateT.run_bind,
      threadFutexWakeC_eq, bind_assoc]
    refine WP.bind (FEvent.wp_wake hE (by decide) (E.ph_set _ _) (by rw [hE.lph]; exact hgo)
      hi₂ fun k₃ hk₃ G₃ m₃ hc₃ hs₃ hi₃ => ?_)
    rw [E.set_set, FEvent.set_of hgx] at hi₃
    repeat (first
      | exact ⟨by omega, hc₃, hs₃, hi₃⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind])
    done
  · rw [FEvent.set_of hgx] at hi₂
    simp only [show (o == 1) = false from beq_false_of_ne ho, Bool.false_eq_true, ↓reduceIte,
      StateT.run_pure, pure_bind]
    repeat (first
      | exact ⟨by omega, hc₂, hs₂, hi₂⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind])
    done

/-- `ResetEvent.set` by a thread out of the event's and the lock's code. -/
theorem resetEvent_set_wp (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hsx : E.sx g) (_io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_ResetEvent_set p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ P.inv (upd G' t g) m') G m d := by
  subst hp
  unfold Thread_ResetEvent_set
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callC (WP.mono (fun _ G' m' d' h => ?_)
    (futexSet_wp hE hcost t g hgx hgo hsx G m d hi)))
  exact WP.pure' (WP.pure' h)

/-- This actual unticked setter needs no payment admission and preserves every caller part. -/
theorem resetEvent_set_wp_resource (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hsx : E.sx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (_hpre : anyPart t (L.part g)) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_ResetEvent_set p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ ∃ r', keepPart t (L.part g) r' ∧
        P.inv (upd G' t (L.setPart g r')) m') G m d := by
  refine WP.mono ?_ (resetEvent_set_wp hE hcost hp t g hgx hgo hsx io G m d hi)
  rintro _ G' m' d' ⟨hd, hc, hs, hi'⟩
  exact ⟨hd, hc, hs, L.part g, rfl, by simpa only [L.setPart_self] using hi'⟩

/-- A waiter's ghost value: `g` at the event's place `p`, with the part `r` (its deadline
block). -/
abbrev gD (L : FLock γ) (E : FEvent γ) (g : γ) (p : EPh) (r : Res) : γ := L.setPart (E.set g p) r

theorem gD_ph (hE : L.Fits (E.prim L) P U ok) {g : γ} {p : EPh} {r : Res} : E.ph (gD L E g p r) = p := by
  rw [hE.ph_part, E.ph_set]

theorem gD_lph (hE : L.Fits (E.prim L) P U ok) {g : γ} {p : EPh} {r : Res} :
    L.ph (gD L E g p r) = L.ph g := by
  rw [L.ph_setPart, hE.lph]

theorem gD_set (hE : L.Fits (E.prim L) P U ok) {g : γ} {p q : EPh} {r : Res} :
    E.set (gD L E g p r) q = gD L E g q r := by
  rw [hE.set_part, E.set_set]

theorem gD_setPart {g : γ} {p : EPh} {r r' : Res} :
    L.setPart (gD L E g p r) r' = gD L E g p r' := L.setPart_setPart _ _ _

theorem gD_part {g : γ} {p : EPh} {r : Res} : L.part (gD L E g p r) = r := L.part_setPart _ _

theorem gD_self (hE : L.Fits (E.prim L) P U ok) {g : γ} {p : EPh} : gD L E g p (L.part g) = E.set g p := by
  have := L.setPart_self (E.set g p); rwa [hE.lpart] at this

/-- `Deadline.wait` with no timeout, by a waiter at `w1` with its deadline block `q`: one futex
wait at the event's word with the value `waiting`. -/
theorem dwait_wp [Zig.Os.HasEnv] (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {DR : BlockId → FAssn} {t : ThreadId} {g : γ} (hgo : L.ph g = .out)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    {q : Ptr} {r : Res} (G : ThreadId → γ) (m : Mem) (d : Nat) (hc : m.current = t)
    (hdp : DPart DR q bsD r) (hi : P.inv (upd G t (gD L E g .w1 r)) m) :
    P.WP t (Thread_Futex_Deadline_wait q E.W.ptr 1) (fun x G' m' d' => x = .ok () ∧ d' < d ∧
      m'.current = t ∧ ∃ r', DPart DR q bsD r' ∧
        P.inv (upd G' t (gD L E g .w1 r')) m') G m d := by
  fsym [FEvent.wp_liftPart hE (g := gD L E g .w1 r) (t := t)
      (hgo := by simpa only [gD_lph hE] using hgo) (hi := hi) (hc := hc)
      (htt := dload (P := DR) (q := q))
      (hp := by simpa only [gD_part] using hdp) (hret := .inl (.inr hcost)),
    FEvent.wp_wait hE (g := gD L E g .w1 _) (ε := BitVec 32) (w := 32)
      (e := (1 : BitVec 32)) rfl (gD_ph hE)
      (by simpa only [gD_lph hE] using hgo),
    gD_ph hE, gD_lph hE, gD_part, gD_setPart, threadFutexWaitC_eq]

/-- `waitUntilSet`'s loop invariant: `t` is a waiter at `w1` with its deadline block `q`. -/
def wusInv (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ) (E : FEvent γ)
    (t : ThreadId) (g : γ) (q : Ptr)
    (D : Nat) (_ : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d ≤ D ∧ m.current = t ∧ ∃ r, DPart DR q bsD r ∧ P.inv (upd G t (gD L E g .w1 r)) m

/-- The loop ends when `t` reads `is_set`: it is out of the event's code. -/
def wusPost (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ) (E : FEvent γ)
    (t : ThreadId) (g : γ) (q : Ptr)
    (D : Nat) (x : Thread_ResetEvent_FutexImpl_waitUntilSetExit ×
      Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) :
    Prop :=
  x.1 = .br36 ∧ x.2.state = 2 ∧ d ≤ D ∧ m.current = t ∧ E.IsSet m ∧
    ∃ r, DPart DR q bsD r ∧ P.inv (upd G t (gD L E g .out r)) m

/-- One repeat of `waitUntilSet`'s loop: `Deadline.wait`, then an acquire load. -/
theorem wus_body [Zig.Os.HasEnv] (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    (DR : BlockId → FAssn) (hu : ∀ b r, DR b r → 0 < r.gh.ac.frag .unmetered)
    {t : ThreadId} {g : γ} (hgo : L.ph g = .out)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁) (q : Ptr) (D : Nat)
    (s : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : wusInv DR P L E t g q D s G m d) :
    P.WP t ((Thread_ResetEvent_FutexImpl_waitUntilSet.loop37 E.W.ptr q).run s) (fun x G' m' d' =>
      if Thread_ResetEvent_FutexImpl_waitUntilSet.again37 x.1 then wusInv DR P L E t g q D x.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) x.2 <
          (fun (_ : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) => 0) s)
      else wusPost DR P L E t g q D x G' m' d') G m d := by
  fsym [hE.wp_tick_unmetered (g := gD L E g .w1 _) (t := t),
    DPart.unmetered hu, dwait_wp hE hcost hgo hlive,
    FEvent.wp_load hE (g := gD L E g .w1 _) (.inr (gD_ph hE))
      (by simpa only [gD_lph hE] using hgo),
    gD_ph hE, gD_lph hE, gD_set hE, gD_part, gD_setPart, wusInv, wusPost,
    Thread_ResetEvent_FutexImpl_waitUntilSet.again37]


set_option maxHeartbeats 400000 in
/-- `waitUntilSet(null)` by a waiter at `p₀` (`w0` or `w1`): it returns when the event is set,
out of the event's code. -/
theorem wus_wp [Zig.Os.HasEnv] (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    (DR : BlockId → FAssn) (hu : ∀ b r, DR b r → 0 < r.gh.ac.frag .unmetered)
    {t : ThreadId} {g : γ} (hgx : E.ph g = .out) (hgo : L.ph g = .out)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁) {p₀ : EPh} (hp₀ : p₀.Waiting) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hc : m.current = t)
    (halloc : FTTriple ((· = L.part g) ⋆ cur t) (allocStack 48 8)
      (fun q => DPart DR q (Array.replicate 48 .undef) ⋆ cur t))
    (hfree : ∀ q bs, bs.size = 48 → FTTriple (DPart DR q bs ⋆ cur t)
      (free q) (fun _ => (· = L.part g) ⋆ cur t))
    (hi : P.inv (upd G t (gD L E g p₀ (L.part g))) m) :
    P.WP t (Thread_ResetEvent_FutexImpl_waitUntilSet E.W.ptr none) (fun x G' m' d' =>
      x = .ok () ∧ d' ≤ d ∧ m'.current = t ∧ E.IsSet m' ∧ P.inv (upd G' t g) m') G m d := by
  fsym [WP.liftMem_pure (x := StateT.lift (debug_assert true)) (by rfl) rfl,
    FEvent.wp_liftPartCur hE (g := gD L E g p₀ (L.part g)) (t := t)
      (hgo := by simpa only [gD_lph hE] using hgo) (htt := halloc)
      (hp := by simp only [gD_part]) (hret := .inl (.inr hcost)),
    FEvent.wp_liftPartCur hE (t := t) (hret := .inl (.inr hcost)), hfree,
    FEvent.wp_liftPart hE (g := gD L E g .w1 _) (t := t)
      (hgo := by simpa only [gD_lph hE] using hgo)
      (htt := dstore (P := DR) (bs := Array.replicate 48 .undef) (by simp))
      (hret := .inl (.inr hcost)), dstore,
    FEvent.wp_load hE (g := gD L E g p₀ _),
    FEvent.wp_cas hE (g := gD L E g .w0 _),
    (WP.liftMem_liftR (P := P) (t := t)
      (hnone := fun _ => (show P.Partial from Or.inr hcost))),
    (fun (q : Ptr) =>
      WP.loop _ _ (wusInv DR P L E t g q d) (fun _ => 0) (wusPost DR P L E t g q d)
        (wus_body hE hcost DR hu hgo hlive q d)),
    dinit_eq, debugAssert_true, bsD_size, gD_ph hE, gD_lph hE, gD_set hE, gD_part, gD_setPart,
    gD_self hE, hE.lph, hE.lpart, FEvent.set_of, E.IsSet_of_hist_eq, wusInv, wusPost]

/-- **`ResetEvent.wait`** by a thread out of the event's and the lock's code, as the only waiter
(`hone`, `hhb`): it returns when the event is set. -/
theorem resetEvent_wait_wp_resource [Zig.Os.HasEnv]
    (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hwx : E.wx g) (_io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (hpre : deadlinePre t (L.part g)) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_ResetEvent_wait p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ ∃ r', keepPart t (L.part g) r' ∧
        P.inv (upd G' t (L.setPart g r')) m') G m d := by
  subst hp
  have hi0 := hE.enterWait hgx hgo hwx hone hhb hi
  obtain ⟨DR, hu, halloc, hfree⟩ := deadlinePre.elim hpre
  fsym [FEvent.wp_load hE (g := E.set g .w0) (t := t)
      (hg := .inl (E.ph_set _ _)) (hgo := by rw [hE.lph]; exact hgo) (hi := hi0),
    wus_wp hE hcost DR hu hgx hgo hlive,
    halloc, hfree, gD_self, E.set_set, FEvent.set_of, hE.lph, hE.lpart,
    keepPart, L.setPart_self]

/-- Concrete Plain waits specialize the same resource proof and recover the original part. -/
theorem resetEvent_wait_wp [Zig.Os.HasEnv] (hE : L.Fits (E.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hwx : E.wx g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (hpl : (L.part g).Plain) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_ResetEvent_wait p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ P.inv (upd G' t g) m') G m d := by
  refine WP.mono ?_ (resetEvent_wait_wp_resource hE hcost hp t g hgx hgo hwx io G m d
    hone hhb hlive (.inl hpl) hi)
  rintro _ G' m' d' ⟨hd, hc, hs, r', hr, hi'⟩
  change r' = L.part g at hr
  subst r'
  exact ⟨hd, hc, hs, by simpa only [L.setPart_self] using hi'⟩

end ResetEvent

/-- **`Thread.ResetEvent` is an event** (`EventImpl`) in this program. -/
def resetEvent [Zig.Os.HasEnv] : EventImpl Tgt where
  wait p _ := Thread_ResetEvent_wait p
  set p _ := Thread_ResetEvent_set p
  wait_pre := deadlinePre
  wait_post := keepPart
  wait_plain_pre _ _ := .inl
  wait_plain_post _ _ _ _ hr := hr
  set_pre := anyPart
  set_post := keepPart
  set_plain_pre _ _ _ := True.intro
  set_plain_post _ _ _ _ hr := hr
  wait_wp_resource := ResetEvent.resetEvent_wait_wp_resource
  set_wp_resource := ResetEvent.resetEvent_set_wp_resource

end Threadsync
