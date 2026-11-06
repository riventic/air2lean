import Proofs.Threadsync.Deadline
import Proofs.Threadsync.ThreadMutex
import ZigLean.Sep.Full.Cond
import ZigLean.Sep.Full.AutoWP

/-!
# `Thread.Condition` of `examples/threadsync` as a condition (`CondImpl`, 0.15.2)

The per-item obligation of `Thread.Condition` (0.15.2's `FutexImpl`: the futex-epoch condition of
`ZigLean/Sep/Full/Cond.lean` on bits) in this program's generated code: `wait` (with no timeout;
its `Deadline` block is on the waiter's stack, allocated while it holds the mutex and freed after
it locked it again: `Proofs/Threadsync/Deadline.lean`, `FCond.wp_liftPart`) and `signal`
(`wake(1)`), walked with the rules of the condition, with the program's `Thread.Mutex`
(`threadMutex`), for every protocol that has the condition next to its mutex. `wait` reaches the
translated `std.time.Timer` (OSK-01), so it takes the OS environment: the results hold for every
`[Zig.Os.HasEnv]`.
-/

open Zig Zig.Conc Zig.Full Zig.Full.FAssn Zig.Conc.Proto

namespace Threadsync

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

section
variable {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## `signal`: `wake(1)` -/

/-- `wake`'s loop invariant, for the call snapshot `h c` (`FCond.Fits.enterSl`): `t` last read
the state `(waiters, signals)` in the low and the high 16 bits (`waiters ≥ signals`); a served
value (`waiters ≤ signals`) gave the history post and `t` is out, else `t` is still at
`sl h c`. -/
def wakeInv (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (h : Array Word.Entry)
    (c : VClock) (D : Nat) (s : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ FCond.SOk s.state ∧
    (s.state.toNat % 65536 ≤ s.state.toNat / 65536 → ∀ all, C.SigPost h c all m) ∧
    P.inv (upd G t (C.set g (FCond.afterSRead h c s.state))) m

/-- `wake`'s loop ends with `t` out and the history post. -/
def wakePost (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ) (h : Array Word.Entry)
    (c : VClock) (D : Nat)
    (r : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Exit ×
      Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  r.1 = .ret ∧ d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧ C.SigPost h c false m

theorem wake_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (h : Array Word.Entry) (c : VClock) (D : Nat)
    (s : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (hs : wakeInv P C t g h c D s G m d) :
    P.WP t ((Thread_Condition_FutexImpl_wake__anon_b3c587c57789.loop9 C.S.ptr).run s)
      (fun r G' m' d' =>
        if Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9 r.1 then
          wakeInv P C t g h c D r.2 G' m' d' ∧ (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 <
            (fun (_ : Thread_Condition_FutexImpl_wake__anon_b3c587c57789Locals) => 0) s)
        else wakePost P C t g h c D r G' m' d') G m d := by
  obtain ⟨hd, hcur, hok, hsp₀, hi₀⟩ := hs
  -- the loop's tick, paid from the unmetered fragment: the same writes (`m.ticked`)
  unfold Thread_Condition_FutexImpl_wake__anon_b3c587c57789.loop9
  rw [StateT.run_bind]
  refine WP.bind ?_
  show P.WP t (ConcM.liftMem Zig.tick >>= fun a => pure (a, s)) _ _ _ _
  refine WP.bind (hC.wp_tick_unmetered_exact hi₀ hcur
    (by rw [hC.lph]; rcases hgo with hh | hh <;> rw [hh] <;> decide)
    (by rw [hC.lpart]; exact hu) fun hcur hi => WP.pure' ?_)
  have hsp : s.state.toNat % 65536 ≤ s.state.toNat / 65536 → ∀ all, C.SigPost h c all m.ticked :=
    fun hsv all => (hsp₀ hsv all).extend (Word.Extends.congr rfl rfl)
  clear hsp₀ hi₀
  obtain ⟨b⟩ := s
  simp only at hok hsp hi
  by_cases hsv : b.toNat % 65536 ≤ b.toNat / 65536
  · have hp := hsp hsv false
    rw [show FCond.afterSRead h c b = .out by simp [FCond.afterSRead, hsv],
      FCond.set_of hgx] at hi
    clear hsp
    fsym [(WP.liftMem_liftR (P := P) (t := t)
        (hnone := fun _ => (show P.Partial from Or.inr hcost))),
      BitVec.udiv_eq, FCond.SOk, wakePost, Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9]
  · rw [show FCond.afterSRead h c b = .sl h c by simp [FCond.afterSRead, hsv]] at hi
    clear hsp
    fsym [FCond.wp_post hC (sh := h) (c := c), FCond.wp_bump hC, FCond.wp_wakeEp hC,
      hC.wp_projE (t := t), FCond.SigPost.ofPost,
      (WP.liftMem_liftR (P := P) (t := t)
        (hnone := fun _ => (show P.Partial from Or.inr hcost))),
      C.ph_set, hC.lph, C.set_set, FCond.set_of, (FCond.set_of hgx), FCond.ptr_ep,
      threadFutexWakeC_eq, BitVec.udiv_eq, FCond.SOk, FCond.PostOk, wakeInv, wakePost,
      Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9]

/-- **`Condition.signal`** (`wake(1)`) outside or holding the mutex, preserving its complete
resource, with the history post of its call (`FCond.SigPost`). -/
theorem cond_signal_wp (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (_io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Condition_signal p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t g) m' ∧ C.SigPost (C.S.hist m) (m.clocks[t]!) false m') G m d := by
  have hi' := hC.enterSl hgx hgo hsx hi
  generalize C.S.hist m = h at hi' ⊢
  generalize m.clocks[t]! = c at hi' ⊢
  clear hi
  fsym [FCond.wp_sload hC, C.ph_set, hC.lph, C.set_set,
    WP.loop _ _ (wakeInv P C t g h c d) (fun _ => 0) (wakePost P C t g h c d)
      (wake_body hC hcost t g hgx hgo hu h c d),
    wakeInv, wakePost]

/-- The signal contract at its caller part: this implementation's proved profile returns the
part it was called with (`keepPart`). -/
theorem cond_signal_wp_resource (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : payUnmetered t (L.part g)) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Condition_signal p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r', keepPart t (L.part g) r' ∧ P.inv (upd G' t (L.setPart g r')) m' ∧
        C.SigPost (C.S.hist m) (m.clocks[t]!) false m') G m d := by
  refine WP.mono ?_ (cond_signal_wp hC hcost hp t g hgx hgo hsx io G m d hu hi)
  rintro _ G' m' d' ⟨hd, hc, hi', hs⟩
  exact ⟨hd, hc, L.part g, rfl, by simpa only [L.setPart_self] using hi', hs⟩

/-! ## `wait`

The state word's halves on bits: `waiters` the low and `signals` the high 16 bits (`FCond`). -/

/-- The high half of the state word (`signals`), masked in place. -/
theorem condT_hi (b : BitVec 32) : (b &&& 4294901760).toNat = 65536 * (b.toNat / 65536) := by
  fsym_arith

/-- No signal: the high half is zero. -/
theorem condT_hi0 {b : BitVec 32} (h : b.toNat / 65536 = 0) :
    (b &&& 4294901760 != 0) = false := by
  have : b &&& 4294901760 = 0 := BitVec.eq_of_toNat_eq (by rw [condT_hi, h]; rfl)
  rw [this]; rfl

/-- A signal: the high half is not zero. -/
theorem condT_hi1 {b : BitVec 32} (h : ¬b.toNat / 65536 = 0) :
    (b &&& 4294901760 != 0) = true := by
  have : b &&& 4294901760 ≠ 0 := fun he => by
    have := congrArg BitVec.toNat he; rw [condT_hi] at this; simp at this; omega
  simpa using this

/-- Room for one more waiter (`assert(prev_state & waiter_mask != waiter_mask)`). -/
theorem condT_room {b : BitVec 32} (h : FCond.RegOld b) : (b &&& 65535 != 65535) = true := by
  unfold FCond.RegOld at h
  have hm : (b &&& 65535).toNat = b.toNat % 65536 := by
    rw [BitVec.toNat_and, show (65535 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have : b &&& 65535 ≠ 65535 := fun he => by
    have := congrArg BitVec.toNat he; rw [hm] at this; simp at this; omega
  simpa using this

/-! The waiter's ghost values carry its deadline block in its part (`FLock.setPart`): `gD g p r` in
the critical code, `gRD g i jr sn e r` registered and out of the lock's code. -/

/-- `g` at the condition's place `p`, with the part `r`. -/
abbrev gD (L : FLock γ) (C : FCond γ) (g : γ) (p : CPh) (r : Res) : γ := L.setPart (C.set g p) r

/-- The waiter registered, out of the lock's code, with the part `r`. -/
abbrev gRD (L : FLock γ) (C : FCond γ) (g : γ) (i jr : Nat) (sn : Bool) (e : BitVec 32)
    (r : Res) : γ :=
  L.setPart (C.set (L.set g .out rnil) (.reg i jr sn e)) r

theorem gD_ph (hC : L.Fits (C.prim L) P U ok) {g : γ} {p : CPh} {r : Res} : C.ph (gD L C g p r) = p := by
  rw [hC.ph_part, C.ph_set]

theorem gD_lph (hC : L.Fits (C.prim L) P U ok) {g : γ} {p : CPh} {r : Res} :
    L.ph (gD L C g p r) = L.ph g := by
  rw [L.ph_setPart, hC.lph]

theorem gD_set (hC : L.Fits (C.prim L) P U ok) {g : γ} {p q : CPh} {r : Res} :
    C.set (gD L C g p r) q = gD L C g q r := by
  rw [hC.set_part, C.set_set]

theorem gRD_ph (hC : L.Fits (C.prim L) P U ok) {g : γ} {i jr : Nat} {sn : Bool} {e : BitVec 32} {r : Res} :
    C.ph (gRD L C g i jr sn e r) = .reg i jr sn e := by
  rw [hC.ph_part, C.ph_set]

theorem gRD_lph (hC : L.Fits (C.prim L) P U ok) {g : γ} {i jr : Nat} {sn : Bool} {e : BitVec 32}
    {r : Res} : L.ph (gRD L C g i jr sn e r) = .out := by
  rw [L.ph_setPart, hC.lph, L.ph_set]

theorem gRD_set (hC : L.Fits (C.prim L) P U ok) {g : γ} {i jr i' jr' : Nat} {sn sn' : Bool}
    {e e' : BitVec 32} {r : Res} :
    C.set (gRD L C g i jr sn e r) (.reg i' jr' sn' e') = gRD L C g i' jr' sn' e' r := by
  rw [hC.set_part, C.set_set]

/-- The waiter's `unlock`: registered, out of the lock's code. -/
theorem gD_unlock (hC : L.Fits (C.prim L) P U ok) {g : γ} {i jr : Nat} {e : BitVec 32} {r : Res} :
    L.set (gD L C g (.reg i jr false e) r) .out rnil = gRD L C g i jr false e r := by
  rw [← L.setPart_set, ← hC.set_l]

/-- After the waiter took the signal: `g` out of the lock's code, with the part `r`. -/
theorem gRD_out (hC : L.Fits (C.prim L) P U ok) {g : γ} (hgx : C.ph g = .out) {i jr : Nat} {sn : Bool}
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
theorem dwait_wp [Zig.Os.HasEnv] (hC : C.Fits L P U ok) (hcost : P.cost = none)
    {DR : BlockId → FAssn} {t : ThreadId} {g : γ} {i jr : Nat} {e : BitVec 32}
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    {q : Ptr} {r : Res} (G : ThreadId → γ) (m : Mem) (d : Nat) (hc : m.current = t)
    (hdp : DPart DR q bsD r) (hi : P.inv (upd G t (gRD L C g i jr false e r)) m) :
    P.WP t (Thread_Futex_Deadline_wait q C.Ep.ptr e) (fun x G' m' d' => x = .ok () ∧ d' < d ∧
      m'.current = t ∧ ∃ r', DPart DR q bsD r' ∧
        P.inv (upd G' t (gRD L C g i jr true e r')) m') G m d := by
  have hF := hC.toFits
  unfold Thread_Futex_Deadline_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (FCond.wp_liftPartM hF (.inl (gRD_lph hF)) hi hc dload
    (by rw [L.part_setPart]; exact hdp) fun a m₁ r₁ _ hq hc₁ _ _ hi₁ => ?_)
  obtain ⟨rfl, hdq⟩ := sep_lift.mp hq
  rw [L.setPart_setPart] at hi₁
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
    threadFutexWaitC_eq, bind_assoc]
  refine WP.bind (FCond.wp_waitEp hC (e' := e) (BitVec.setWidth_eq e) (gRD_ph hF)
    (gRD_lph hF) hi₁ hlive fun k hk G₂ m₂ hc₂ hi₂ => ?_)
  rw [show FCond.afterWait i jr e = .reg i jr true e from rfl, gRD_set hF] at hi₂
  repeat (first
    | exact ⟨rfl, by omega, hc₂, r₁, hdq, hi₂⟩
    | refine WP.pure' ?_
    | simp only [pure_bind])
  done

/-- The inner loop's invariant: `t` registered at the epoch value `s.epoch` (`sn`: the state
value `s.state` it read has a signal), the state value with `waiters ≥ signals` (`SOk`), and its
deadline block. -/
def inv107 (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ)
    (t : ThreadId) (g : γ) (q : Ptr)
    (jr : Nat) (D : Nat) (s : Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ FCond.SOk s.state ∧ ∃ i r, DPart DR q bsD r ∧
    P.inv (upd G t (gRD L C g i jr (decide (s.state.toNat / 65536 ≠ 0)) s.epoch r)) m

/-- The inner loop ends with no signal to take (`br106`), or with `t` holding the mutex again. -/
def post107 (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ)
    (t : ThreadId) (g : γ) (q : Ptr)
    (jr : Nat) (D : Nat)
    (x : Thread_Condition_FutexImpl_waitExit × Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
  ((x.1 = .br106 ∧ ∃ i r, DPart DR q bsD r ∧
      P.inv (upd G t (gRD L C g i jr false x.2.epoch r)) m) ∨
    (x.1 = .ret (.ok ()) ∧ ∃ rL r, DPart DR q bsD r ∧
      P.inv (upd G t (L.setPart (L.set g .holds rL) r)) m))

theorem loop107_body [Zig.Os.HasEnv] (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (DR : BlockId → FAssn) (hu : ∀ b r, DR b r → 0 < r.gh.ac.frag .unmetered)
    (hLc : L.c = mutexC) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g) (q : Ptr)
    (jr : Nat) (D : Nat) (s : Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : inv107 DR P L C t g q jr D s G m d) :
    P.WP t ((Thread_Condition_FutexImpl_wait.loop107 C.S.ptr L.ptr).run s) (fun x G' m' d' =>
      if Thread_Condition_FutexImpl_wait.again107 x.1 then inv107 DR P L C t g q jr D x.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) x.2 <
          (fun (_ : Thread_Condition_FutexImpl_waitLocals) => 0) s)
      else post107 DR P L C t g q jr D x G' m' d') G m d := by
  obtain ⟨hD, hc, hb, i, r, hdp, hi⟩ := h
  -- the loop's tick, paid from the unmetered fragment of the deadline residual
  unfold Thread_Condition_FutexImpl_wait.loop107
  rw [StateT.run_bind]
  refine WP.bind ?_
  show P.WP t (ConcM.liftMem Zig.tick >>= fun a => pure (a, s)) _ _ _ _
  refine WP.bind (hC.wp_tick_unmetered hi hc (by rw [gRD_lph hC]; decide)
    (by rw [L.part_setPart]; exact DPart.unmetered hu hdp) fun m₀ hc hi => WP.pure' ?_)
  obtain ⟨ep, b, fd⟩ := s
  simp only at hb hi
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  by_cases hs0 : b.toNat / 65536 = 0
  · -- no signal to take
    rw [show decide (b.toNat / 65536 ≠ 0) = false by simp [hs0]] at hi
    repeat (first
      | exact ⟨hD, hc, .inl ⟨rfl, i, r, hdp, hi⟩⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, pure_bind, Thread_Condition_FutexImpl_wait.again107, Bool.false_eq_true, ↓reduceIte,
          condT_hi0 hs0])
    done
  · -- take a signal
    rw [show decide (b.toNat / 65536 ≠ 0) = true by simp [hs0]] at hi
    have hb' := hb
    unfold FCond.SOk at hb'
    simp only [condT_hi1 hs0, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    refine WP.bind (WP.bind (WP.callRC_ok (v := b - 1)
      (by rw [Auto.sub_ok (by simp; omega)]; rfl) ?_))
    refine WP.bind (WP.callRC_ok (v := b - 1 - 65536)
      (by dsimp only; rw [Auto.sub_ok (by bv_omega)]; rfl) ?_)
    refine WP.bind (FCond.wp_consume hC (exp := b) (new := b - 1 - 65536) (by omega) (by bv_omega)
      (gRD_ph hC) hi
      fun k hk G₁ m₁ hc₁ => ⟨fun hi₁ => ?_, fun b' hb' hi₁ => ?_⟩)
    · -- the signal taken: `lock`
      rw [gRD_out hC hgx] at hi₁
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callC (WP.mono ?_ (threadMutex.lock_wp hC hcost rfl hLc t _
        (by rw [L.ph_setPart, L.ph_set]) ((hC.ok_setPart _ _).mpr ((hC.ok_set _ _ _).mpr hok))
        (by rw [L.part_setPart]; exact DPart.unmetered hu hdp) ⟨⟩ G₁ m₁ k hi₁))))
      rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, rL, hi₂⟩
      rw [gD_lock] at hi₂
      repeat (first
        | exact ⟨by omega, hc₂, .inr ⟨rfl, rL, r, hdp, hi₂⟩⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, pure_bind, Thread_Condition_FutexImpl_wait.again107,
            Bool.false_eq_true, ↓reduceIte])
      done
    · -- the `cmpxchg` failed: the read value
      rw [show FCond.afterRead i jr ep b' = .reg i jr (decide (b'.toNat / 65536 ≠ 0)) ep from rfl,
        gRD_set hC] at hi₁
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callRC_ok (x := optPayload (some b')) rfl ?_))
      repeat (first
        | exact ⟨⟨by omega, hc₁, hb', i, r, hdp, hi₁⟩, .inl (by omega)⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, StateT.run_modify, StateT.run_bind, pure_bind,
            Thread_Condition_FutexImpl_wait.again107, ↓reduceIte])
      done

/-- The outer loop's invariant: `t` registered before its futex wait at the epoch value
`s.epoch`, with its deadline block. -/
def inv29 (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ)
    (t : ThreadId) (g : γ) (q : Ptr)
    (jr : Nat) (D : Nat) (s : Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ i r, DPart DR q bsD r ∧
    P.inv (upd G t (gRD L C g i jr false s.epoch r)) m

/-- The outer loop ends with `t` holding the mutex again, with its deadline block. -/
def post29 (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ)
    (t : ThreadId) (g : γ) (q : Ptr) (D : Nat)
    (x : Thread_Condition_FutexImpl_waitExit × Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ x.1 = .ret (.ok ()) ∧ m.current = t ∧ ∃ rL r, DPart DR q bsD r ∧
    P.inv (upd G t (L.setPart (L.set g .holds rL) r)) m

theorem loop29_body [Zig.Os.HasEnv] (hC : C.Fits L P U ok) (hcost : P.cost = none)
    (DR : BlockId → FAssn) (hu : ∀ b r, DR b r → 0 < r.gh.ac.frag .unmetered)
    (hLc : L.c = mutexC) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g) (q : Ptr)
    (jr : Nat) (D : Nat)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (s : Thread_Condition_FutexImpl_waitLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : inv29 DR P L C t g q jr D s G m d) :
    P.WP t ((Thread_Condition_FutexImpl_wait.loop29 C.S.ptr L.ptr q).run s) (fun x G' m' d' =>
      if Thread_Condition_FutexImpl_wait.again29 x.1 then inv29 DR P L C t g q jr D x.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) x.2 <
          (fun (_ : Thread_Condition_FutexImpl_waitLocals) => 0) s)
      else post29 DR P L t g q D x G' m' d') G m d := by
  have hF := hC.toFits
  obtain ⟨hD, hc, i, r, hdp, hi⟩ := h
  -- the loop's tick, paid from the unmetered fragment of the deadline residual
  unfold Thread_Condition_FutexImpl_wait.loop29
  rw [StateT.run_bind]
  refine WP.bind ?_
  show P.WP t (ConcM.liftMem Zig.tick >>= fun a => pure (a, s)) _ _ _ _
  refine WP.bind (hF.wp_tick_unmetered hi hc (by rw [gRD_lph hF]; decide)
    (by rw [L.part_setPart]; exact DPart.unmetered hu hdp) fun m₀ hc hi => WP.pure' ?_)
  obtain ⟨ep, st, fd⟩ := s
  simp only at hi
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  refine WP.bind (WP.callMC_ptrProject (hF.projE hi) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (WP.callC (WP.mono ?_ (dwait_wp hC hcost hlive G m₀ d hc hdp hi)))
  rintro x G₁ m₁ d₁ ⟨rfl, hd₁, hc₁, r₁, hdp₁, hi₁⟩
  simp only [isNonErr, isErr, Bool.not_false, ↓reduceIte, StateT.run_pure, pure_bind]
  simp only [StateT.run_bind]
  refine WP.bind (WP.callMC_ptrProject (hF.projE hi₁) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_loadEp hF (gRD_ph hF) hi₁
    fun k₂ hk₂ G₂ m₂ v i' hc₂ hi₂ => ?_)
  rw [gRD_set hF] at hi₂
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (FCond.wp_loadS hF (gRD_ph hF) hi₂
    fun k₃ hk₃ G₃ m₃ b hc₃ hb hi₃ => ?_)
  rw [show FCond.afterRead i' jr v b = .reg i' jr (decide (b.toNat / 65536 ≠ 0)) v from rfl,
    gRD_set hF] at hi₃
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv107 DR P L C t g q jr d) (fun _ => 0)
    (post107 DR P L C t g q jr d) (loop107_body hF hcost DR hu hLc t g hgx hok q jr d) _ G₃ m₃
    k₃ ⟨by omega, hc₃, hb, i', r₁, hdp₁, hi₃⟩))
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, hc₄, ⟨rfl, i₄, r₄, hdp₄, hi₄⟩ | ⟨rfl, rL, r₄, hdp₄, hi₄⟩⟩
  · repeat (first
      | exact ⟨⟨by omega, hc₄, i₄, r₄, hdp₄, hi₄⟩, .inl (by omega)⟩
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
def fwEnd (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ)
    (q : Ptr) (D : Nat)
    (x : Thread_Condition_FutexImpl_waitExit) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ x = .ret (.ok ()) ∧ m.current = t ∧ ∃ rL r, DPart DR q bsD r ∧
    P.inv (upd G t (L.setPart (L.set g .holds rL) r)) m

/-- `FutexImpl.wait(null)` by the mutex's holder, out of the condition's code: its deadline
block is in its part from the `alloc` (while it holds the mutex) to the `free` (after it locked
the mutex again). -/
theorem fwait_wp [Zig.Os.HasEnv] (hC' : C.Fits L P U ok) (hcost : P.cost = none)
    (DR : BlockId → FAssn) (hu : ∀ b r, DR b r → 0 < r.gh.ac.frag .unmetered)
    (hLc : L.c = mutexC) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds)
    (hok : ok g) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (halloc : FTTriple ((· = L.part g) ⋆ cur t) (allocStack 48 8)
      (fun q => DPart DR q (Array.replicate 48 .undef) ⋆ cur t))
    (hfree : ∀ q bs, bs.size = 48 → FTTriple (DPart DR q bs ⋆ cur t)
      (free q) (fun _ => (· = L.part g) ⋆ cur t))
    (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Thread_Condition_FutexImpl_wait C.S.ptr L.ptr none) (fun x G' m' d' => d' < d ∧
      x = .ok () ∧ m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  have hC := hC'.toFits
  have hi0 := hC.enterEn hgx hgh hroom hent hi
  have hgh0 : L.ph (C.set g .en) = .holds := by rw [hC.lph]; exact hgh
  unfold Thread_Condition_FutexImpl_wait
  refine WP.bind (FCond.wp_liftPartCur hC (.inr hgh0) hi0 hc halloc (hC.lpart _ _)
    (fun q m₁ r₁ _ hdp₁ hc₁ _ _ hi₁ => ?_) (.inl (.inr hcost)))
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map (WP.mono (Q := fun x => fwEnd DR P L t g q d x.1) (fun x G₂ m₂ d₂ hx => ?_) ?_)
  · -- the tail: `free` the deadline block
    obtain ⟨hd₂, hx, hc₂, rL, r₂, hdp₂, hi₂⟩ := hx
    show P.WP t (ConcM.liftMem (free q) >>= fun _ => _) _ G₂ m₂ d₂
    refine WP.bind (FCond.wp_liftPartCur hC (.inr (by rw [L.ph_setPart, L.ph_set])) hi₂ hc₂
      (hfree q bsD bsD_size) (by rw [L.part_setPart]; exact hdp₂)
      (fun _ m₃ r₃ _ hr₃ hc₃ _ _ hi₃ => ?_) (.inl (.inr hcost)))
    subst hr₃
    rw [gD_free] at hi₃
    rw [hx]
    exact WP.pure' ⟨hd₂, rfl, hc₃, rL, hi₃⟩
  -- the body
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hi₁) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (WP.bind (FCond.wp_ldEp hC (g := gD L C g .en r₁) (gD_ph hC)
    (by rw [gD_lph hC]; exact hgh) hi₁ fun k₁ hk₁ G₁ m₂ v i hc₂ hi₂ => ?_))
  rw [gD_set hC] at hi₂
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  refine WP.bind (WP.bind (FCond.wp_reg hC (gD_ph hC) (by rw [gD_lph hC]; exact hgh) hi₂
    fun k₂ hk₂ G₂ m₃ jr old hc₃ hro hi₃ => ?_))
  rw [gD_set hC] at hi₃
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind, condT_room hro]
  refine WP.bind (WP.callRC_ok (v := ()) (by rfl) ?_)
  refine WP.bind (WP.callRC_ok (v := old + 1)
    (by unfold FCond.RegOld at hro; rw [Auto.add_ok (by simp; omega)]; rfl) ?_)
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (threadMutex.unlock_wp hC hcost rfl hLc t _
    (by rw [gD_lph hC]; exact hgh)
    ((hC.ok_setPart _ _).mpr (by rw [hC.ok_calm _ _ .out rfl rfl, FCond.set_of hgx]; exact hok))
    ⟨⟩ G₂ m₃ k₂ hi₃ hc₃)))
  rintro _ G₃ m₄ d₃ ⟨hd₃, hc₄, hi₄⟩
  rw [gD_unlock hC] at hi₄
  -- `Deadline.init(null)` and its store in the deadline block
  rw [dinit_eq]
  refine WP.bind (WP.callC (WP.pure' ?_))
  refine WP.bind (FCond.wp_liftPartM hC (.inl (gRD_lph hC)) hi₄ hc₄
    (dstore (bs := Array.replicate 48 .undef) (by simp)) (by rw [L.part_setPart]; exact hdp₁)
    fun _ m₅ r₅ _ hdp₅ hc₅ _ _ hi₅ => ?_)
  rw [L.setPart_setPart] at hi₅
  refine WP.mono ?_ (WP.loop _ _ (inv29 DR P L C t g q jr d) (fun _ => 0) (post29 DR P L t g q d)
    (loop29_body hC' hcost DR hu hLc t g hgx hok q jr d hlive) _ G₃ m₅ d₃
    ⟨by omega, hc₅, i, r₅, hdp₅, hi₅⟩)
  rintro ⟨x, s'⟩ G₄ m₆ d₄ ⟨hd₄, rfl, hc₆, rL, r₆, hdp₆, hi₆⟩
  exact ⟨hd₄, rfl, hc₆, rL, r₆, hdp₆, hi₆⟩

/-- **`Condition.wait`** by the mutex's holder, out of the condition's code: it returns holding
the mutex again. -/
theorem cond_wait_wp_resource [Zig.Os.HasEnv] (hC : C.Fits L P U ok) (hcost : P.cost = none)
    {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = mutexC) (t : ThreadId) (g : γ)
    (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (_io : Io) (G : ThreadId → γ)
    (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (hpre : deadlinePre t (L.part g)) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Thread_Condition_wait p q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r' rL, keepPart t (L.part g) r' ∧
        P.inv (upd G' t (L.set (L.setPart g r') .holds rL)) m') G m d := by
  subst hp hq
  obtain ⟨DR, hu, halloc, hfree⟩ := deadlinePre.elim hpre
  unfold Thread_Condition_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.callC (WP.mono ?_ (fwait_wp hC hcost DR hu hLc t g hgx hgh hok G m d hroom
    hent hlive halloc hfree hi hc)))
  rintro x G₁ m₁ d₁ ⟨hd₁, rfl, hc₁, rL, hi₁⟩
  rw [← L.setPart_self g] at hi₁
  repeat (first
    | exact ⟨hd₁, hc₁, L.part g, rL, rfl, hi₁⟩
    | refine WP.pure' ?_
    | simp only [StateT.run_pure, StateT.run_bind, pure_bind, isNonErr, ↓reduceIte])
  done

/-- The concrete Plain convenience is an endpoint specialization of the same resource proof. -/
theorem cond_wait_wp [Zig.Os.HasEnv] (hC : C.Fits L P U ok) (hcost : P.cost = none)
    {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = mutexC) (t : ThreadId) (g : γ)
    (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io) (G : ThreadId → γ)
    (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (hpl : (L.part g).Plain) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Thread_Condition_wait p q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  refine WP.mono ?_ (cond_wait_wp_resource hC hcost hp hq hLc t g hgx hgh hok io G m d
    hroom hent hlive (.inl hpl) hi hc)
  rintro _ G' m' d' ⟨hd, hc', r', rL, hr, hi'⟩
  change r' = L.part g at hr
  subst r'
  exact ⟨hd, hc', rL, by simpa only [L.setPart_self] using hi'⟩

end

/-- **`Thread.Condition` is a condition** (`CondImpl`) in this program, with its `Thread.Mutex`
(`threadMutex`). -/
def threadCond [Zig.Os.HasEnv] : CondImpl Tgt where
  wait p _ q := Thread_Condition_wait p q
  signal p _ := Thread_Condition_signal p
  c := mutexC
  wait_pre := deadlinePre
  wait_post := keepPart
  wait_plain_pre _ _ := .inl
  wait_plain_post _ _ _ _ hr := hr
  signal_pre := payUnmetered
  signal_post := keepPart
  signal_unmetered_pre _ _ hu := hu
  signal_unmetered_post _ _ _ _ hr := hr
  wait_wp_resource := cond_wait_wp_resource
  signal_wp_resource hC := cond_signal_wp_resource hC.toFits

end Threadsync
