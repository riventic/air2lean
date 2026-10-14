import Proofs.Threadsync.Deadline
import Proofs.Threadsync.ThreadMutex
import ZigLean.Sep.Full.Cond

/-!
# `Thread.Condition` of `examples/threadsync` as a condition (`CondImpl`, 0.15.2)

The per-item obligation of `Thread.Condition` (0.15.2's `FutexImpl`: the futex-epoch condition of
`ZigLean/Sep/Full/Cond.lean` on bits) in this program's generated code: `wait` (with no timeout;
its `Deadline` block is on the waiter's stack, allocated while it holds the mutex and freed after
it locked it again: `Proofs/Threadsync/Deadline.lean`, `FCond.wp_liftPart`) and `signal`
(`wake(1)`), walked with the rules of the condition, with the program's `Thread.Mutex`
(`threadMutex`), for every protocol that has the condition next to its mutex.
-/

open Zig Zig.Conc Zig.Full Zig.Conc.Proto

namespace Threadsync

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

section
variable {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## `signal`: `wake(1)` -/

/-- `wake`'s loop invariant: `t` read the state value `b`; a value other than `(1, 0)` means a
registered waiter was signalled. -/
def wakeInv (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (D : Nat)
    (s : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧ (s.state = 0 ∨ s.state = 1 ∨ s.state = 0x10001) ∧
    (s.state ≠ 1 → ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m)

/-- `wake`'s loop ends with `t` out and a registered waiter signalled. -/
def wakePost (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit ×
      Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  r.1 = .ret ∧ d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧
    ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m

theorem wake_body (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgo : L.ph g = .out) (hsx : C.sx g) (D : Nat)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (s : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (h : wakeInv P C t g D s G m d) :
    P.WP t ((Thread_Condition_FutexImpl_wake__anon_b3c587c57789.loop9 C.S.ptr).run s)
      (fun r G' m' d' =>
        if Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9 r.1 then
          wakeInv P C t g D r.2 G' m' d' ∧ (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 <
            (fun (_ : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals) => 0) s)
        else wakePost P C t g D r G' m' d') G m d := by
  obtain ⟨st⟩ := s
  obtain ⟨hD, hc, hi, hb, hsg⟩ := h
  simp only at hb hsg
  unfold Thread_Condition_FutexImpl_wake__anon_b3c587c57789.loop9
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  rcases hb with rfl | rfl | rfl
  · -- `(0, 0)`: no waiter
    refine WP.bind (WP.callRC_ok (v := 0) (by rfl) ?_)
    refine WP.bind (WP.callRC_ok (v := 0) (by rfl) ?_)
    refine WP.bind (WP.callRC_ok (v := 0) (by rfl) ?_)
    repeat (first
      | exact ⟨rfl, hD, hc, hi, hsg (by decide)⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, StateT.run_bind,
          Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9, Bool.false_eq_true,
          ↓reduceIte, show ((0 : BitVec 32) == 0) = true from rfl])
    done
  · -- `(1, 0)`: signal the waiter
    refine WP.bind (WP.callRC_ok (v := 1) (by rfl) ?_)
    refine WP.bind (WP.callRC_ok (v := 0) (by rfl) ?_)
    refine WP.bind (WP.callRC_ok (v := 1) (by rfl) ?_)
    simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_get,
      show ((1 : BitVec 32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine WP.bind (WP.bind (WP.callRC_ok (v := 0x10001) (by rfl) ?_))
    refine WP.bind (FCond.wp_signal hC hP rfl rfl hgx hgo hsx hseen hi
      fun k hk G₁ m₁ hc₁ => ⟨fun hi₁ => ?_, fun b' hb' hs' hi₁ => ?_⟩)
    · -- success: `epoch += 1`, the wake
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callMC_ptrProject (hC.projE hP hi₁) ?_))
      dsimp only
      rw [FCond.ptr_ep]
      refine WP.bind (FCond.wp_bump hC hP (C.ph_set _ _) (by rw [hC.lph]; exact hgo) hi₁
        fun k₂ hk₂ G₂ m₂ o hc₂ hi₂ => ?_)
      refine WP.bind (WP.callMC_ptrProject (hC.projE hP hi₂) ?_)
      dsimp only
      rw [FCond.ptr_ep, threadFutexWakeC_eq]
      refine WP.bind (FCond.wp_wakeEp hC hP (by decide) (C.ph_set _ _) hi₂
        fun k₃ hk₃ G₃ m₃ hc₃ hsg₃ hi₃ => ?_)
      rw [C.set_set, C.set_set, FCond.set_of hgx] at hi₃
      repeat (first
        | exact ⟨rfl, by omega, hc₃, hi₃, hsg₃⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, pure_bind,
            Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9, Bool.false_eq_true,
            ↓reduceIte])
      done
    · -- failure: the read value
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callRC_ok (x := optPayload (some b')) rfl ?_))
      repeat (first
        | exact ⟨⟨by omega, hc₁, hi₁, hb', hs'⟩, .inl (by omega)⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, StateT.run_modify, StateT.run_bind, pure_bind,
            Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9, ↓reduceIte])
      done
  · -- `(1, 1)`: signalled
    refine WP.bind (WP.callRC_ok (v := 1) (by rfl) ?_)
    refine WP.bind (WP.callRC_ok (v := 1) (by rfl) ?_)
    refine WP.bind (WP.callRC_ok (v := 0) (by rfl) ?_)
    repeat (first
      | exact ⟨rfl, hD, hc, hi, hsg (by decide)⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, StateT.run_bind,
          Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9, Bool.false_eq_true,
          ↓reduceIte, show ((0 : BitVec 32) == 0) = true from rfl])
    done

/-- **`Condition.signal`** (`wake(1)`) by a thread out of the condition's and the lock's code
that may signal, after every registration (`hseen`). -/
theorem cond_signal_wp (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out) (hsx : C.sx g) (_io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Condition_signal p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t g) m' ∧ ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → C.Signalled m')
      G m d := by
  subst hp
  unfold Thread_Condition_signal
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callC (WP.mono (fun _ G₂ m₂ d₂ h => WP.pure' (WP.pure' h)) ?_))
  unfold Thread_Condition_FutexImpl_wake__anon_b3c587c57789
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FCond.wp_sload hC hP hgo hseen hi fun k hk G₁ m₁ b hc₁ hb hsg hi₁ => ?_)
  simp only [StateT.run_modify, pure_bind]
  refine WP.mono ?_ (WP.loop _ _ (wakeInv P C t g d) (fun _ => 0) (wakePost P C t g d)
    (wake_body hC hP hcost t g hgx hgo hsx d hseen) _ G₁ m₁ k ⟨by omega, hc₁, hi₁, hb, hsg⟩)
  rintro ⟨e, s'⟩ G₂ m₂ d₂ ⟨rfl, hd₂, hc₂, hi₂, hsg₂⟩
  exact WP.pure' ⟨hd₂, hc₂, hi₂, hsg₂⟩

/-! ## `wait`

The waiter's ghost values carry its deadline block in its part (`FLock.setPart`): `gD g p r` in
the critical code, `gRD g i jr sn e r` registered and out of the lock's code. -/

/-- `g` at the condition's place `p`, with the part `r`. -/
abbrev gD (L : FLock γ) (C : FCond γ) (g : γ) (p : CPh) (r : Res) : γ := L.setPart (C.set g p) r

/-- The waiter registered, out of the lock's code, with the part `r`. -/
abbrev gRD (L : FLock γ) (C : FCond γ) (g : γ) (i jr : Nat) (sn : Bool) (e : BitVec 32)
    (r : Res) : γ :=
  L.setPart (C.set (L.set g .out rnil) (.reg i jr sn e)) r

theorem gD_ph (hC : C.Fits L P U ok) {g : γ} {p : CPh} {r : Res} : C.ph (gD L C g p r) = p := by
  rw [hC.ph_part, C.ph_set]

theorem gD_lph (hC : C.Fits L P U ok) {g : γ} {p : CPh} {r : Res} :
    L.ph (gD L C g p r) = L.ph g := by
  rw [L.ph_setPart, hC.lph]

theorem gD_set (hC : C.Fits L P U ok) {g : γ} {p q : CPh} {r : Res} :
    C.set (gD L C g p r) q = gD L C g q r := by
  rw [hC.set_part, C.set_set]

theorem gRD_ph (hC : C.Fits L P U ok) {g : γ} {i jr : Nat} {sn : Bool} {e : BitVec 32} {r : Res} :
    C.ph (gRD L C g i jr sn e r) = .reg i jr sn e := by
  rw [hC.ph_part, C.ph_set]

theorem gRD_lph (hC : C.Fits L P U ok) {g : γ} {i jr : Nat} {sn : Bool} {e : BitVec 32}
    {r : Res} : L.ph (gRD L C g i jr sn e r) = .out := by
  rw [L.ph_setPart, hC.lph, L.ph_set]

theorem gRD_set (hC : C.Fits L P U ok) {g : γ} {i jr : Nat} {sn sn' : Bool} {e : BitVec 32}
    {r : Res} : C.set (gRD L C g i jr sn e r) (.reg i jr sn' e) = gRD L C g i jr sn' e r := by
  rw [hC.set_part, C.set_set]

/-- The waiter's `unlock`: registered, out of the lock's code. -/
theorem gD_unlock (hC : C.Fits L P U ok) {g : γ} {i jr : Nat} {e : BitVec 32} {r : Res} :
    L.set (gD L C g (.reg i jr false e) r) .out rnil = gRD L C g i jr false e r := by
  rw [← L.setPart_set, ← hC.set_l]

/-- After the waiter took the signal: `g` out of the lock's code, with the part `r`. -/
theorem gRD_out (hC : C.Fits L P U ok) {g : γ} (hgx : C.ph g = .out) {i jr : Nat} {sn : Bool}
    {e : BitVec 32} {r : Res} :
    C.set (gRD L C g i jr sn e r) .out = L.setPart (L.set g .out rnil) r := by
  rw [hC.set_part, C.set_set, FCond.set_of (by rw [hC.ph_l]; exact hgx)]

/-- The waiter's `lock`: it holds the lock again, with the part `r`. -/
theorem gD_lock {g : γ} {r rL : Res} :
    L.set (L.setPart (L.set g .out rnil) r) .holds rL = L.setPart (L.set g .holds rL) r := by
  rw [← L.setPart_set, L.set_set]

/-- The `free` of the deadline block: the part is `g`'s again. -/
theorem gD_free {g : γ} {r rL : Res} :
    L.setPart (L.setPart (L.set g .holds rL) r) (L.part g) = L.set g .holds rL := by
  rw [L.setPart_setPart, L.setPart_set, L.setPart_self]

/-- `Deadline.wait` with no timeout, by the registered waiter with its deadline block `q`: one
futex wait at the epoch with its value `e`. -/
theorem dwait_wp (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {t : ThreadId} {g : γ} {i jr : Nat} {e : BitVec 32}
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    {q : Ptr} {r : Res} (G : ThreadId → γ) (m : Mem) (d : Nat) (hc : m.current = t)
    (hdp : DPart (L.part g) q bsD r) (hi : P.inv (upd G t (gRD L C g i jr false e r)) m) :
    P.WP t (Thread_Futex_Deadline_wait q C.Ep.ptr e) (fun x G' m' d' => x = .ok () ∧ d' < d ∧
      m'.current = t ∧ ∃ r', DPart (L.part g) q bsD r' ∧
        P.inv (upd G' t (gRD L C g i jr false e r')) m') G m d := by
  unfold Thread_Futex_Deadline_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FCond.wp_liftPartM hC hP (.inl (gRD_lph hC)) hi hc dload
    (by rw [L.part_setPart]; exact hdp) fun a m₁ r₁ _ hq hc₁ _ _ hi₁ => ?_)
  obtain ⟨rfl, hdq⟩ := sep_lift.mp hq
  rw [L.setPart_setPart] at hi₁
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
    threadFutexWaitC_eq, bind_assoc]
  refine WP.bind (FCond.wp_waitEp hC hP (e' := e) (BitVec.setWidth_eq e) (gRD_ph hC)
    (gRD_lph hC) hi₁
    (fun G₁ m₁ h1 h2 h3 h4 => hlive G₁ m₁ ⟨i, jr, e, by rw [h1, gRD_ph hC]⟩ h2 h3 h4)
    fun k hk G₂ m₂ hc₂ hi₂ => ?_)
  repeat (first
    | exact ⟨rfl, by omega, hc₂, r₁, hdq, hi₂⟩
    | refine WP.pure' ?_
    | simp only [pure_bind])
  done

/-- The inner loop's invariant: `t` registered (`sn`: it loaded the next epoch write), the state
value it read, its epoch value `e` while it has not seen the signal, and its deadline block. -/
def inv107 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (s : Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ sn : Bool, ((s.state = 1 ∧ sn = false) ∨ s.state = 0x10001) ∧
    (sn = false → s.epoch = e) ∧ ∃ r, DPart (L.part g) q bsD r ∧
      P.inv (upd G t (gRD L C g i jr sn e r)) m

/-- The inner loop ends with no signal to take (`br106`), or with `t` holding the mutex again. -/
def post107 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat)
    (x : Thread_Condition_FutexImpl_waitExit × Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
  ((x.1 = .br106 ∧ x.2.epoch = e ∧ ∃ r, DPart (L.part g) q bsD r ∧
      P.inv (upd G t (gRD L C g i jr false e r)) m) ∨
    (x.1 = .ret (.ok ()) ∧ ∃ rL r, DPart (L.part g) q bsD r ∧
      P.inv (upd G t (L.setPart (L.set g .holds rL) r)) m))

theorem loop107_body (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (hLc : L.c = mutexC) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (s : Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : inv107 P L C t g q i jr e D s G m d) :
    P.WP t ((Thread_Condition_FutexImpl_wait.loop107 C.S.ptr L.ptr).run s) (fun x G' m' d' =>
      if Thread_Condition_FutexImpl_wait.again107 x.1 then inv107 P L C t g q i jr e D x.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) x.2 <
          (fun (_ : Thread_Condition_FutexImpl_waitLocals) => 0) s)
      else post107 P L C t g q i jr e D x G' m' d') G m d := by
  obtain ⟨ep, st, fd⟩ := s
  obtain ⟨hD, hc, sn, hb, hep, r, hdp, hi⟩ := h
  simp only at hb hep
  unfold Thread_Condition_FutexImpl_wait.loop107
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  rcases hb with ⟨rfl, rfl⟩ | rfl
  · -- `(1, 0)`: no signal to take
    repeat (first
      | exact ⟨hD, hc, .inl ⟨rfl, hep rfl, r, hdp, hi⟩⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, Thread_Condition_FutexImpl_wait.again107, Bool.false_eq_true, ↓reduceIte,
          show ((1 : BitVec 32) &&& 4294901760 != 0) = false from rfl])
    done
  · -- `(1, 1)`: take the signal
    simp only [show ((0x10001 : BitVec 32) &&& 4294901760 != 0) = true from rfl, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    refine WP.bind (WP.bind (WP.callRC_ok (v := 0x10000) (by rfl) ?_))
    refine WP.bind (WP.callRC_ok (v := 0) (by dsimp only; rfl) ?_)
    refine WP.bind (FCond.wp_consume hC hP rfl (gRD_ph hC) (gRD_lph hC) hi
      fun k hk G₁ m₁ hc₁ => ⟨fun hi₁ => ?_, fun b' hb' hi₁ => ?_⟩)
    · -- the signal taken: `lock`
      rw [gRD_out hC hgx] at hi₁
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callC (WP.mono ?_ (threadMutex.lock_wp hP hcost rfl hLc t _
        (by rw [L.ph_setPart, L.ph_set]) ((hP.ok_setPart _ _).mpr ((hP.ok_set _ _ _).mpr hok))
        ⟨⟩ G₁ m₁ k hi₁))))
      rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, rL, hi₂⟩
      rw [gD_lock] at hi₂
      repeat (first
        | exact ⟨by omega, hc₂, .inr ⟨rfl, rL, r, hdp, hi₂⟩⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, pure_bind, Thread_Condition_FutexImpl_wait.again107,
            Bool.false_eq_true, ↓reduceIte])
      done
    · -- the `cmpxchg` failed: the read value
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callRC_ok (x := optPayload (some b')) rfl ?_))
      repeat (first
        | exact ⟨⟨by omega, hc₁, sn, hb', hep, r, hdp, hi₁⟩, .inl (by omega)⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, StateT.run_modify, StateT.run_bind, pure_bind,
            Thread_Condition_FutexImpl_wait.again107, ↓reduceIte])
      done

/-- The outer loop's invariant: `t` registered, before the signal, with its epoch value `e` and
its deadline block. -/
def inv29 (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (s : Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ s.epoch = e ∧ ∃ r, DPart (L.part g) q bsD r ∧
    P.inv (upd G t (gRD L C g i jr false e r)) m

/-- The outer loop ends with `t` holding the mutex again, with its deadline block. -/
def post29 (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (q : Ptr) (D : Nat)
    (x : Thread_Condition_FutexImpl_waitExit × Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ x.1 = .ret (.ok ()) ∧ m.current = t ∧ ∃ rL r, DPart (L.part g) q bsD r ∧
    P.inv (upd G t (L.setPart (L.set g .holds rL) r)) m

theorem loop29_body (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (hLc : L.c = mutexC) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (s : Thread_Condition_FutexImpl_waitLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : inv29 P L C t g q i jr e D s G m d) :
    P.WP t ((Thread_Condition_FutexImpl_wait.loop29 C.S.ptr L.ptr q).run s) (fun x G' m' d' =>
      if Thread_Condition_FutexImpl_wait.again29 x.1 then inv29 P L C t g q i jr e D x.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) x.2 <
          (fun (_ : Thread_Condition_FutexImpl_waitLocals) => 0) s)
      else post29 P L t g q D x G' m' d') G m d := by
  obtain ⟨ep, st, fd⟩ := s
  obtain ⟨hD, hc, hep, r, hdp, hi⟩ := h
  simp only at hep
  subst hep
  unfold Thread_Condition_FutexImpl_wait.loop29
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hP hi) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (WP.callC (WP.mono ?_ (dwait_wp hC hP hcost hlive G m d hc hdp hi)))
  rintro x G₁ m₁ d₁ ⟨rfl, hd₁, hc₁, r₁, hdp₁, hi₁⟩
  simp only [isNonErr, isErr, Bool.not_false, ↓reduceIte, StateT.run_pure, pure_bind]
  simp only [StateT.run_bind]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hP hi₁) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_loadEp hC hP (gRD_ph hC) (gRD_lph hC) hi₁
    fun k₂ hk₂ G₂ m₂ v hc₂ hcase => ?_)
  -- the epoch read: `t`'s own value, or the next write
  obtain ⟨sn, hsn, hi₂⟩ : ∃ sn : Bool, (sn = false → v = ep) ∧
      P.inv (upd G₂ t (gRD L C g i jr sn ep r₁)) m₂ := by
    rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact ⟨false, fun _ => rfl, h⟩
    · exact ⟨true, nofun, by rw [gRD_set hC] at h; exact h⟩
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (FCond.wp_loadS hC hP (gRD_ph hC) (gRD_lph hC) hi₂
    fun k₃ hk₃ G₃ m₃ b hc₃ hb hi₃ => ?_)
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv107 P L C t g q i jr ep d) (fun _ => 0)
    (post107 P L C t g q i jr ep d) (loop107_body hC hP hcost hLc t g hgx hok q i jr ep d) _ G₃ m₃
    k₃ ⟨by omega, hc₃, sn, hb, fun h' => hsn h', r₁, hdp₁, hi₃⟩))
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, hc₄, ⟨rfl, hep₄, r₄, hdp₄, hi₄⟩ | ⟨rfl, rL, r₄, hdp₄, hi₄⟩⟩
  · repeat (first
      | exact ⟨⟨by omega, hc₄, hep₄, r₄, hdp₄, hi₄⟩, .inl (by omega)⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, StateT.run_bind, ↓reduceIte,
          Thread_Condition_FutexImpl_wait.again29])
    done
  · repeat (first
      | exact ⟨by omega, rfl, hc₄, rL, r₄, hdp₄, hi₄⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, StateT.run_bind,
          Thread_Condition_FutexImpl_wait.again29, Bool.false_eq_true, ↓reduceIte])
    done

/-- The end of `FutexImpl.wait`'s body: `t` holds the mutex again, with its deadline block. -/
def fwEnd (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (q : Ptr) (D : Nat)
    (x : Thread_Condition_FutexImpl_waitExit) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ x = .ret (.ok ()) ∧ m.current = t ∧ ∃ rL r, DPart (L.part g) q bsD r ∧
    P.inv (upd G t (L.setPart (L.set g .holds rL) r)) m

/-- `FutexImpl.wait(null)` by the mutex's holder, out of the condition's code: its deadline
block is in its part from the `alloc` (while it holds the mutex) to the `free` (after it locked
the mutex again). -/
theorem fwait_wp (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    (hLc : L.c = mutexC) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds)
    (hok : ok g) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hpl : (L.part g).Plain) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Thread_Condition_FutexImpl_wait C.S.ptr L.ptr none) (fun x G' m' d' => d' < d ∧
      x = .ok () ∧ m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  have hi0 := hC.enter hP hgx hgh hone hhb hent hi
  have hgh0 : L.ph (C.set g .en) = .holds := by rw [hC.lph]; exact hgh
  unfold Thread_Condition_FutexImpl_wait
  refine WP.bind (FCond.wp_liftPart hC hP (.inr hgh0) hi0 hc
    (dalloc _ (by rw [hC.lpart]; exact hpl)) rfl
    fun q m₁ r₁ _ hdp₁ hc₁ _ _ hi₁ => ?_)
  rw [hC.lpart] at hdp₁
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map (WP.mono (Q := fun x => fwEnd P L t g q d x.1) (fun x G₂ m₂ d₂ hx => ?_) ?_)
  · -- the tail: `free` the deadline block
    obtain ⟨hd₂, hx, hc₂, rL, r₂, hdp₂, hi₂⟩ := hx
    show P.WP t (ConcM.liftMem (free q) >>= fun _ => _) _ G₂ m₂ d₂
    refine WP.bind (FCond.wp_liftPart hC hP (.inr (by rw [L.ph_setPart, L.ph_set])) hi₂ hc₂
      (dfree bsD_size) (by rw [L.part_setPart]; exact hdp₂)
      fun _ m₃ r₃ _ hr₃ hc₃ _ _ hi₃ => ?_)
    subst hr₃
    rw [gD_free] at hi₃
    rw [hx]
    exact WP.pure' ⟨hd₂, rfl, hc₃, rL, hi₃⟩
  -- the body
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hP hi₁) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (WP.bind (FCond.wp_ldEp hC hP (g := gD L C g .en r₁) (gD_ph hC)
    (by rw [gD_lph hC]; exact hgh) hi₁ fun k₁ hk₁ G₁ m₂ v i hc₂ hi₂ => ?_))
  rw [gD_set hC] at hi₂
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  refine WP.bind (WP.bind (FCond.wp_reg hC hP (gD_ph hC) (by rw [gD_lph hC]; exact hgh) hi₂
    fun k₂ hk₂ G₂ m₃ jr hc₃ hi₃ => ?_))
  rw [gD_set hC] at hi₃
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind,
    show ((0 : BitVec 32) &&& 65535 != 65535) = true from rfl]
  refine WP.bind (WP.callRC_ok (v := ()) (by rfl) ?_)
  refine WP.bind (WP.callRC_ok (v := 1) (by rfl) ?_)
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (threadMutex.unlock_wp hP hcost rfl hLc t _
    (by rw [gD_lph hC]; exact hgh)
    ((hP.ok_setPart _ _).mpr (by rw [hC.ok_c _ _ .out rfl rfl, FCond.set_of hgx]; exact hok))
    ⟨⟩ G₂ m₃ k₂ hi₃ hc₃)))
  rintro _ G₃ m₄ d₃ ⟨hd₃, hc₄, hi₄⟩
  rw [gD_unlock hC] at hi₄
  -- `Deadline.init(null)` and its store in the deadline block
  rw [dinit_eq]
  refine WP.bind (WP.callC (WP.pure' ?_))
  refine WP.bind (FCond.wp_liftPartM hC hP (.inl (gRD_lph hC)) hi₄ hc₄
    (dstore (bs := Array.replicate 48 .undef) (by simp)) (by rw [L.part_setPart]; exact hdp₁)
    fun _ m₅ r₅ _ hdp₅ hc₅ _ _ hi₅ => ?_)
  rw [L.setPart_setPart] at hi₅
  refine WP.mono ?_ (WP.loop _ _ (inv29 P L C t g q i jr v d) (fun _ => 0) (post29 P L t g q d)
    (loop29_body hC hP hcost hLc t g hgx hok q i jr v d hlive) _ G₃ m₅ d₃
    ⟨by omega, hc₅, rfl, r₅, hdp₅, hi₅⟩)
  rintro ⟨x, s'⟩ G₄ m₆ d₄ ⟨hd₄, rfl, hc₆, rL, r₆, hdp₆, hi₆⟩
  exact ⟨hd₄, rfl, hc₆, rL, r₆, hdp₆, hi₆⟩

/-- **`Condition.wait`** by the mutex's holder, out of the condition's code: it returns holding
the mutex again. -/
theorem cond_wait_wp (hC : C.Fits L P U ok) (hP : L.FitsOn P U ok) (hcost : P.cost = none)
    {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = mutexC) (t : ThreadId) (g : γ)
    (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (_io : Io) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hpl : (L.part g).Plain) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Thread_Condition_wait p q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp hq
  unfold Thread_Condition_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.callC (WP.mono ?_ (fwait_wp hC hP hcost hLc t g hgx hgh hok G m d hone hhb
    hent hlive hpl hi hc)))
  rintro x G₁ m₁ d₁ ⟨hd₁, rfl, hc₁, rL, hi₁⟩
  repeat (first
    | exact ⟨hd₁, hc₁, rL, hi₁⟩
    | refine WP.pure' ?_
    | simp only [StateT.run_pure, StateT.run_bind, pure_bind, isNonErr, ↓reduceIte])
  done

end

/-- **`Thread.Condition` is a condition** (`CondImpl`) in this program, with its `Thread.Mutex`
(`threadMutex`). -/
def threadCond : CondImpl Tgt where
  wait p _ q := Thread_Condition_wait p q
  signal p _ := Thread_Condition_signal p
  c := mutexC
  wait_wp := cond_wait_wp
  signal_wp := cond_signal_wp

end Threadsync
