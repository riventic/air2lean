import Proofs.Threadsync.Deadline
import ZigLean.Sep.Full.Event

/-!
# `Thread.ResetEvent` of `examples/threadsync` as an event (`EventImpl`, 0.15.2)

The per-item obligation of `Thread.ResetEvent` (0.15.2's `FutexImpl`: the futex event of
`ZigLean/Sep/Full/Event.lean` on bits) in this program's generated code: `wait` (`isSet`, then
`waitUntilSet` with no timeout, whose `Deadline` block is on the waiter's stack:
`Proofs/Threadsync/Deadline.lean`, `FEvent.wp_liftPart`) and `set`, walked with the rules of the
futex event, for every protocol that has the event next to a lock.
-/

open Zig Zig.Conc Zig.Full Zig.Conc.Proto

namespace Threadsync

theorem debugAssert_true : (debug_assert true).run = some (.ok ()) := rfl

section
variable {γ : Type} {L : FLock γ} {E : FEvent γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- `FutexImpl.set` by a thread out of the event's and the lock's code. -/
theorem futexSet_wp (hE : E.Fits L P U) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : E.ph g = .out) (hgo : L.ph g = .out) (hsx : E.sx g)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_ResetEvent_FutexImpl_set E.W.ptr) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ E.IsSet m' ∧ P.inv (upd G' t g) m') G m d := by
  unfold Thread_ResetEvent_FutexImpl_set
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FEvent.wp_peek hE hP hgx hgo hi fun k hk G₁ m₁ b hc₁ hi₁ hb2 => ?_)
  by_cases hb : b = 2
  · subst hb
    simp only [show ((2 : BitVec 32) == 2) = true from rfl, ↓reduceIte, StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨by omega, hc₁, hb2 rfl, hi₁⟩)
  simp only [show (b == 2) = false from beq_false_of_ne hb, Bool.false_eq_true, ↓reduceIte,
    StateT.run_pure, pure_bind, StateT.run_bind]
  refine WP.bind (FEvent.wp_xchg hE hP rfl hgx hgo hsx hi₁
    fun k₂ hk₂ G₂ m₂ o hc₂ hs₂ hcase => ?_)
  rcases hcase with ⟨rfl, hi₂⟩ | ⟨ho, hi₂⟩
  · simp only [show ((1 : BitVec 32) == 1) = true from rfl, ↓reduceIte, StateT.run_bind,
      threadFutexWakeC_eq, bind_assoc]
    refine WP.bind (FEvent.wp_wake hE hP (by decide) (E.ph_set _ _) (by rw [hE.lph]; exact hgo)
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
theorem resetEvent_set_wp (hE : E.Fits L P U) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
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
    (futexSet_wp hE hP hcost t g hgx hgo hsx G m d hi)))
  exact WP.pure' (WP.pure' h)

/-- A waiter's ghost value: `g` at the event's place `p`, with the part `r` (its deadline
block). -/
abbrev gD (L : FLock γ) (E : FEvent γ) (g : γ) (p : EPh) (r : Res) : γ := L.setPart (E.set g p) r

theorem gD_ph (hE : E.Fits L P U) {g : γ} {p : EPh} {r : Res} : E.ph (gD L E g p r) = p := by
  rw [hE.ph_part, E.ph_set]

theorem gD_lph (hE : E.Fits L P U) {g : γ} {p : EPh} {r : Res} :
    L.ph (gD L E g p r) = L.ph g := by
  rw [L.ph_setPart, hE.lph]

theorem gD_set (hE : E.Fits L P U) {g : γ} {p q : EPh} {r : Res} :
    E.set (gD L E g p r) q = gD L E g q r := by
  rw [hE.set_part, E.set_set]

theorem gD_setPart {g : γ} {p : EPh} {r r' : Res} :
    L.setPart (gD L E g p r) r' = gD L E g p r' := L.setPart_setPart _ _ _

theorem gD_part {g : γ} {p : EPh} {r : Res} : L.part (gD L E g p r) = r := L.part_setPart _ _

theorem gD_self (hE : E.Fits L P U) {g : γ} {p : EPh} : gD L E g p (L.part g) = E.set g p := by
  have := L.setPart_self (E.set g p); rwa [hE.lpart] at this

/-- `Deadline.wait` with no timeout, by a waiter at `w1` with its deadline block `q`: one futex
wait at the event's word with the value `waiting`. -/
theorem dwait_wp (hE : E.Fits L P U) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {t : ThreadId} {g : γ} (hgo : L.ph g = .out)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    {q : Ptr} {r : Res} (G : ThreadId → γ) (m : Mem) (d : Nat) (hc : m.current = t)
    (hdp : DPart (L.part g) q bsD r) (hi : P.inv (upd G t (gD L E g .w1 r)) m) :
    P.WP t (Thread_Futex_Deadline_wait q E.W.ptr 1) (fun x G' m' d' => x = .ok () ∧ d' < d ∧
      m'.current = t ∧ ∃ r', DPart (L.part g) q bsD r' ∧
        P.inv (upd G' t (gD L E g .w1 r')) m') G m d := by
  have hgoD : L.ph (gD L E g .w1 r) = .out := by rw [gD_lph hE]; exact hgo
  unfold Thread_Futex_Deadline_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FEvent.wp_liftPartM hE hP hgoD hi hc dload (by rw [gD_part]; exact hdp)
    fun a m₁ r₁ _ hq hc₁ _ hi₁ => ?_)
  obtain ⟨rfl, hdq⟩ := sep_lift.mp hq
  rw [gD_setPart] at hi₁
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
    threadFutexWaitC_eq, bind_assoc]
  refine WP.bind (FEvent.wp_wait hE hP (e := (1 : BitVec 32)) (by decide) (gD_ph hE)
    (by rw [gD_lph hE]; exact hgo) hi₁ hlive
    fun k hk G₂ m₂ hc₂ hi₂ => ?_)
  repeat (first
    | exact ⟨trivial, by omega, hc₂, r₁, hdq, hi₂⟩
    | refine WP.pure' ?_
    | simp only [pure_bind])
  done

/-- `waitUntilSet`'s loop invariant: `t` is a waiter at `w1` with its deadline block `q`. -/
def wusInv (P : Proto Tgt γ) (L : FLock γ) (E : FEvent γ) (t : ThreadId) (g : γ) (q : Ptr)
    (D : Nat) (_ : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d ≤ D ∧ m.current = t ∧ ∃ r, DPart (L.part g) q bsD r ∧ P.inv (upd G t (gD L E g .w1 r)) m

/-- The loop ends when `t` reads `is_set`: it is out of the event's code. -/
def wusPost (P : Proto Tgt γ) (L : FLock γ) (E : FEvent γ) (t : ThreadId) (g : γ) (q : Ptr)
    (D : Nat) (x : Thread_ResetEvent_FutexImpl_waitUntilSetExit ×
      Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) :
    Prop :=
  x.1 = .br36 ∧ x.2.state = 2 ∧ d ≤ D ∧ m.current = t ∧ E.IsSet m ∧
    ∃ r, DPart (L.part g) q bsD r ∧ P.inv (upd G t (gD L E g .out r)) m

/-- One repeat of `waitUntilSet`'s loop: `Deadline.wait`, then an acquire load. -/
theorem wus_body (hE : E.Fits L P U) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {t : ThreadId} {g : γ} (hgo : L.ph g = .out)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁) (q : Ptr) (D : Nat)
    (s : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : wusInv P L E t g q D s G m d) :
    P.WP t ((Thread_ResetEvent_FutexImpl_waitUntilSet.loop37 E.W.ptr q).run s) (fun x G' m' d' =>
      if Thread_ResetEvent_FutexImpl_waitUntilSet.again37 x.1 then wusInv P L E t g q D x.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) x.2 <
          (fun (_ : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) => 0) s)
      else wusPost P L E t g q D x G' m' d') G m d := by
  obtain ⟨hD, hc, r, hdp, hi⟩ := h
  unfold Thread_ResetEvent_FutexImpl_waitUntilSet.loop37
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.bind (WP.callC (WP.mono ?_ (dwait_wp hE hP hcost hgo hlive G m d hc hdp hi))))
  rintro x G₁ m₁ d₁ ⟨rfl, hd₁, hc₁, r₁, hdp₁, hi₁⟩
  simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
  refine WP.bind (FEvent.wp_load hE hP (.inr (gD_ph hE)) (by rw [gD_lph hE]; exact hgo)
    hi₁ fun k hk G₂ m₂ b hc₂ hcase => ?_)
  rcases hcase with ⟨-, h0, -⟩ | ⟨rfl, hi₂⟩ | ⟨rfl, hs₂, hi₂⟩
  · rw [gD_ph hE] at h0; cases h0
  · rw [gD_set hE] at hi₂
    simp only [StateT.run_modify, StateT.run_get, StateT.run_pure, pure_bind,
      show ((1 : BitVec 32) != 1) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    repeat (first
      | exact ⟨⟨by omega, hc₂, r₁, hdp₁, hi₂⟩, .inl (by omega)⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, Thread_ResetEvent_FutexImpl_waitUntilSet.again37, ↓reduceIte])
    done
  · rw [gD_set hE] at hi₂
    simp only [StateT.run_modify, StateT.run_get, StateT.run_pure, pure_bind,
      show ((2 : BitVec 32) != 1) = true from rfl, ↓reduceIte]
    repeat (first
      | exact ⟨rfl, rfl, by omega, hc₂, hs₂, r₁, hdp₁, hi₂⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, Thread_ResetEvent_FutexImpl_waitUntilSet.again37,
          Bool.false_eq_true, ↓reduceIte])
    done

/-- `waitUntilSet` at `w1` (it wrote or read `waiting`): `Deadline.init(null)`, its store in the
deadline block `q`, and the loop. -/
theorem wus_loopPath (hE : E.Fits L P U) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {t : ThreadId} {g : γ} (hgo : L.ph g = .out)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁) {q : Ptr} {D : Nat} {β : Type}
    {K : Thread_ResetEvent_FutexImpl_waitUntilSetExit × Thread_ResetEvent_FutexImpl_waitUntilSetLocals →
      ConcM Tgt β} {Q : β → (ThreadId → γ) → Mem → Nat → Prop}
    (hK : ∀ x G m d, wusPost P L E t g q D x G m d → P.WP t (K x) Q G m d)
    (s : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hd : d ≤ D) (hc : m.current = t) {r : Res}
    (hdp : DPart (L.part g) q (Array.replicate 48 .undef) r)
    (hi : P.inv (upd G t (gD L E g .w1 r)) m) :
    P.WP t (do
      let p ← (callC (Thread_Futex_Deadline_init none) :
        CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals _).run s
      let p ← (liftM (storeBytes q 8 p.fst) :
        CM Tgt Thread_ResetEvent_FutexImpl_waitUntilSetLocals Unit).run p.snd
      let p ← (loop (Thread_ResetEvent_FutexImpl_waitUntilSet.loop37 E.W.ptr q)
        Thread_ResetEvent_FutexImpl_waitUntilSet.again37).run p.snd
      K p) Q G m d := by
  rw [dinit_eq]
  refine WP.bind (WP.callC (WP.pure' ?_))
  refine WP.bind (FEvent.wp_liftPartM hE hP (by rw [gD_lph hE]; exact hgo)
    hi hc (dstore (bs := Array.replicate 48 .undef) (by simp))
    (by rw [gD_part]; exact hdp)
    fun _ m₁ r₁ _ hdp₁ hc₁ _ hi₁ => ?_)
  rw [gD_setPart] at hi₁
  exact WP.bind (WP.mono hK (WP.loop _ _ (wusInv P L E t g q D) (fun _ => 0) (wusPost P L E t g q D)
    (wus_body hE hP hcost hgo hlive q D) _ G m₁ d ⟨hd, hc₁, r₁, hdp₁, hi₁⟩))

/-- The end of `waitUntilSet`'s body: `t` is out of the event's code, with its deadline block. -/
def wusEnd (P : Proto Tgt γ) (L : FLock γ) (E : FEvent γ) (t : ThreadId) (g : γ) (q : Ptr)
    (D : Nat) (x : Thread_ResetEvent_FutexImpl_waitUntilSetExit ×
      Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) :
    Prop :=
  x.1 = .ret (.ok ()) ∧ d ≤ D ∧ m.current = t ∧ E.IsSet m ∧ ∃ bs r, bs.size = 48 ∧
    DPart (L.part g) q bs r ∧ P.inv (upd G t (gD L E g .out r)) m

set_option maxHeartbeats 400000 in
/-- `waitUntilSet(null)` by a waiter at `p₀` (`w0` or `w1`): it returns when the event is set,
out of the event's code. -/
theorem wus_wp (hE : E.Fits L P U) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {t : ThreadId} {g : γ} (hgx : E.ph g = .out) (hgo : L.ph g = .out)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁) {p₀ : EPh} (hp₀ : p₀.Waiting) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hc : m.current = t) (hi : P.inv (upd G t (gD L E g p₀ (L.part g))) m) :
    P.WP t (Thread_ResetEvent_FutexImpl_waitUntilSet E.W.ptr none) (fun x G' m' d' =>
      x = .ok () ∧ d' ≤ d ∧ m'.current = t ∧ E.IsSet m' ∧ P.inv (upd G' t g) m') G m d := by
  have hgoD : ∀ {p r}, L.ph (gD L E g p r) = .out := fun {_ _} => by rw [gD_lph hE]; exact hgo
  unfold Thread_ResetEvent_FutexImpl_waitUntilSet
  refine WP.bind (FEvent.wp_liftPart hE hP hgoD hi hc (dalloc _) rfl
    fun q m₁ r₁ _ hdp₁ hc₁ _ hi₁ => ?_)
  rw [gD_part] at hdp₁
  rw [gD_setPart] at hi₁
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map (WP.mono (Q := wusEnd P L E t g q d) (fun x G₂ m₂ d₂ hx => ?_) ?_)
  · -- the tail: `free` the deadline block
    obtain ⟨hx, hd₂, hc₂, hs₂, bs, r₂, hbs, hdp₂, hi₂⟩ := hx
    show P.WP t (ConcM.liftMem (free q) >>= fun _ => _) _ G₂ m₂ d₂
    refine WP.bind (FEvent.wp_liftPart hE hP hgoD hi₂ hc₂ (dfree hbs)
      (by rw [gD_part]; exact hdp₂) fun _ m₃ r₃ _ hr₃ hc₃ hh₃ hi₃ => ?_)
    subst hr₃
    rw [gD_setPart, gD_self hE, FEvent.set_of hgx] at hi₃
    rw [hx]
    refine WP.pure' ⟨rfl, hd₂, hc₃, ?_, hi₃⟩
    unfold FEvent.IsSet FEvent.newest; rw [hh₃]; exact hs₂
  -- the body
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FEvent.wp_load hE hP (g := gD L E g p₀ r₁) (by rw [gD_ph hE]; exact hp₀)
    hgoD hi₁ fun k hk G₂ m₂ b hc₂ hcase => ?_)
  simp only [StateT.run_modify, StateT.run_get, pure_bind]
  rcases hcase with ⟨rfl, hw0, hi₂⟩ | ⟨rfl, hi₂⟩ | ⟨rfl, hs₂, hi₂⟩
  · rw [gD_ph hE] at hw0; subst hw0
    rw [gD_set hE] at hi₂
    simp only [show ((0 : BitVec 32) == 0) = true from rfl, ↓reduceIte, StateT.run_bind,
      StateT.run_get, pure_bind]
    refine WP.bind (WP.bind (FEvent.wp_cas hE hP rfl rfl (gD_ph hE) hgoD hi₂
      fun k₃ hk₃ G₃ m₃ hc₃ => ⟨fun hi₃ => ?_, fun b hcase => ?_⟩))
    · rw [gD_set hE] at hi₃
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
        StateT.run_bind, StateT.run_modify]
      refine WP.pure' ?_
      simp only [show ((1 : BitVec 32) == 1) = true from rfl, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind]
      refine WP.bind (wus_loopPath hE hP hcost hgo hlive (D := d) (fun x G₄ m₄ d₄ hx => ?_) _
        G₃ m₃ k₃ (Nat.le_of_lt (by omega)) hc₃ hdp₁ hi₃)
      obtain ⟨e, s'⟩ := x
      obtain ⟨rfl, hst, hd₄, hc₄, hs₄, r₄, hdp₄, hi₄⟩ := hx
      change s'.state = 2 at hst
      refine WP.pure' ?_
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hst]
      refine WP.bind (WP.callRC_ok debugAssert_true ?_)
      exact WP.pure' ⟨rfl, hd₄, hc₄, hs₄, bsD, r₄, bsD_size, hdp₄, hi₄⟩
    · rcases hcase with ⟨rfl, hi₃⟩ | ⟨rfl, hs₃, hi₃⟩
      · rw [gD_set hE] at hi₃
        simp only [Option.isSome_some, ↓reduceIte, StateT.run_pure, optPayload, StateT.run_bind]
        refine WP.bind (WP.bind (WP.pure' ?_))
        refine WP.pure' ?_
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        refine WP.pure' ?_
        simp only [show ((1 : BitVec 32) == 1) = true from rfl, ↓reduceIte, StateT.run_bind,
          StateT.run_get, pure_bind]
        have hk₃ : k₃ ≤ d := by omega
        refine WP.bind (wus_loopPath hE hP hcost hgo hlive (D := d) (fun x G₄ m₄ d₄ hx => ?_)
          _ G₃ m₃ k₃ hk₃ hc₃ hdp₁ hi₃)
        obtain ⟨e, s'⟩ := x
        obtain ⟨rfl, hst, hd₄, hc₄, hs₄, r₄, hdp₄, hi₄⟩ := hx
        change s'.state = 2 at hst
        refine WP.pure' ?_
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hst]
        refine WP.bind (WP.callRC_ok debugAssert_true ?_)
        exact WP.pure' ⟨rfl, hd₄, hc₄, hs₄, bsD, r₄, bsD_size, hdp₄, hi₄⟩
      · rw [gD_set hE] at hi₃
        simp only [Option.isSome_some, ↓reduceIte, StateT.run_pure, optPayload, StateT.run_bind]
        refine WP.bind (WP.bind (WP.pure' ?_))
        refine WP.pure' ?_
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        refine WP.pure' ?_
        simp only [show ((2 : BitVec 32) == 1) = false from rfl,
          show ((2 : BitVec 32) == 2) = true from rfl, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
        refine WP.bind (WP.callRC_ok debugAssert_true ?_)
        have hk₃ : k₃ ≤ d := by omega
        exact WP.pure' ⟨rfl, hk₃, hc₃, hs₃, Array.replicate 48 .undef, r₁, by simp, hdp₁, hi₃⟩
  · rw [gD_set hE] at hi₂
    simp only [show ((1 : BitVec 32) == 0) = false from rfl, show ((1 : BitVec 32) == 1) = true from rfl,
      Bool.false_eq_true, ↓reduceIte, StateT.run_pure, StateT.run_bind, StateT.run_get, pure_bind]
    refine WP.bind (wus_loopPath hE hP hcost hgo hlive (D := d) (fun x G₃ m₃ d₃ hx => ?_) _
      G₂ m₂ k (Nat.le_of_lt (by omega)) hc₂ hdp₁ hi₂)
    obtain ⟨e, s'⟩ := x
    obtain ⟨rfl, hst, hd₃, hc₃, hs₃, r₃, hdp₃, hi₃⟩ := hx
    change s'.state = 2 at hst
    refine WP.pure' ?_
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hst]
    refine WP.bind (WP.callRC_ok debugAssert_true ?_)
    exact WP.pure' ⟨rfl, hd₃, hc₃, hs₃, bsD, r₃, bsD_size, hdp₃, hi₃⟩
  · rw [gD_set hE] at hi₂
    simp only [show ((2 : BitVec 32) == 0) = false from rfl,
      show ((2 : BitVec 32) == 1) = false from rfl, show ((2 : BitVec 32) == 2) = true from rfl,
      Bool.false_eq_true, ↓reduceIte, StateT.run_pure, StateT.run_bind, StateT.run_get, pure_bind]
    repeat (first
      | exact ⟨rfl, by omega, hc₂, hs₂, _, r₁, by simp, hdp₁, hi₂⟩
      | refine WP.pure' ?_
      | refine WP.bind (WP.callRC_ok debugAssert_true ?_)
      | simp only [StateT.run_pure, StateT.run_bind, StateT.run_get, pure_bind])
    done

/-- **`ResetEvent.wait`** by a thread out of the event's and the lock's code, as the only waiter
(`hone`, `hhb`): it returns when the event is set. -/
theorem resetEvent_wait_wp (hE : E.Fits L P U) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = E.W.ptr) (t : ThreadId) (g : γ) (hgx : E.ph g = .out)
    (hgo : L.ph g = .out) (hwx : E.wx g) (_io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → E.ph (G u) = .out ∨ E.ph (G u) = .sw)
    (hhb : ∀ j < (E.W.hist m).size, (E.W.hist m)[j]!.Val (1 : BitVec 32) →
      VClock.le (E.W.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hlive : ∀ G₁ m₁, E.ph (G₁ t) = .w1 → L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ E.IsSet m₁ →
      P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_ResetEvent_wait p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      E.IsSet m' ∧ P.inv (upd G' t g) m') G m d := by
  subst hp
  have hi0 := hE.enter hP hgx hgo hwx hone hhb hi
  unfold Thread_ResetEvent_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.callC ?_)
  unfold Thread_ResetEvent_FutexImpl_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.bind (WP.callC ?_))
  unfold Thread_ResetEvent_FutexImpl_isSet
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.bind (FEvent.wp_load hE hP (.inl (E.ph_set _ _)) (by rw [hE.lph]; exact hgo)
    hi0 fun k hk G₂ m₂ b hc₂ hcase => ?_))
  rcases hcase with ⟨rfl, -, hi₂⟩ | ⟨rfl, hi₂⟩ | ⟨rfl, hs₂, hi₂⟩
  · rw [E.set_set, ← gD_self hE] at hi₂
    repeat (first
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind,
          show ((0 : BitVec 32) == 2) = false from rfl, Bool.not_false, ↓reduceIte])
    refine WP.bind (WP.callC (WP.mono (fun x G₄ m₄ d₄ h₄ => ?_)
      (wus_wp hE hP hcost hgx hgo hlive (.inl rfl) G₂ m₂ k hc₂ hi₂)))
    obtain ⟨rfl, hd₄, hc₄, hs₄, hi₄⟩ := h₄
    repeat (first
      | exact ⟨by omega, hc₄, hs₄, hi₄⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind, pure_bind, isNonErr, ↓reduceIte])
    done
  · rw [E.set_set, ← gD_self hE] at hi₂
    repeat (first
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind,
          show ((1 : BitVec 32) == 2) = false from rfl, Bool.not_false, ↓reduceIte])
    refine WP.bind (WP.callC (WP.mono (fun x G₄ m₄ d₄ h₄ => ?_)
      (wus_wp hE hP hcost hgx hgo hlive (.inr rfl) G₂ m₂ k hc₂ hi₂)))
    obtain ⟨rfl, hd₄, hc₄, hs₄, hi₄⟩ := h₄
    repeat (first
      | exact ⟨by omega, hc₄, hs₄, hi₄⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind, pure_bind, isNonErr, ↓reduceIte])
    done
  · rw [E.set_set, FEvent.set_of hgx] at hi₂
    repeat (first
      | exact ⟨by omega, hc₂, hs₂, hi₂⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind, pure_bind, isNonErr,
          show ((2 : BitVec 32) == 2) = true from rfl, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte])
    done

end

/-- **`Thread.ResetEvent` is an event** (`EventImpl`) in this program. -/
def resetEvent : EventImpl Tgt where
  wait p _ := Thread_ResetEvent_wait p
  set p _ := Thread_ResetEvent_set p
  wait_wp := resetEvent_wait_wp
  set_wp := resetEvent_set_wp

end Threadsync
