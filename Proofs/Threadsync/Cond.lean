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

theorem wake_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g) (D : Nat)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
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
  fsym [hC.wp_tick_unmetered_exact (g := g) (t := t),
    FCond.wp_signal hC, FCond.wp_bump hC, FCond.wp_wakeEp hC,
    hC.wp_projE (t := t),
    (WP.liftMem_liftR (P := P) (t := t)
      (hnone := fun _ => (show P.Partial from Or.inr hcost))),
    C.ph_set, hC.lph, C.set_set, FCond.set_of, FCond.ptr_ep,
    FCond.Signalled, FCond.lastS,
    (fun (m : Mem) => Word.hist_congr (W := C.S) (m := m) (m' := m.ticked) rfl rfl),
    threadFutexWakeC_eq, wakeInv, wakePost,
    Thread_Condition_FutexImpl_wake__anon_b3c587c57789.again9]

/-- **`Condition.signal`** (`wake(1)`) outside or holding the mutex, preserving its complete
resource, after every registration (`hseen`). -/
theorem cond_signal_wp_unmetered (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (_io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Condition_signal p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t g) m' ∧ ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → C.Signalled m')
      G m d := by
  fsym [hC.wp_tick_unmetered, FCond.wp_sload hC,
    WP.loop _ _ (wakeInv P C t g d) (fun _ => 0) (wakePost P C t g d)
      (wake_body hC hcost t g hgx hgo hsx d hu hseen),
    wakeInv, wakePost]

/-- The actual resource primary transports the floor through its proved singleton during
assertion; it does not replace an arbitrary profile's intermediate state by the old part. -/
theorem cond_signal_wp_resource (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : payUnmetered t (L.part g))
    (hseen : ∀ rᵢ, keepPart t (L.part g) rᵢ → ∀ G₁ rX m₁,
      G₁ t = L.setPart g rᵢ → U G₁ rX m₁ → ∀ u i jr sn e,
      C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Condition_signal p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r', keepPart t (L.part g) r' ∧ P.inv (upd G' t (L.setPart g r')) m' ∧
        ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → C.Signalled m') G m d := by
  refine WP.mono ?_ (cond_signal_wp_unmetered hC hcost hp t g hgx hgo hsx io G m d hu ?_ hi)
  · rintro _ G' m' d' ⟨hd, hc, hi', hs⟩
    exact ⟨hd, hc, L.part g, rfl, by simpa only [L.setPart_self] using hi', hs⟩
  · intro G₁ rX m₁ hg hU
    exact hseen (L.part g) rfl G₁ rX m₁ (by simpa only [L.setPart_self] using hg) hU

/-- Concrete Plain signal convenience, derived from its actual unmetered resource. -/
theorem cond_signal_wp (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hpl : (L.part g).Plain)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e,
      C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Condition_signal p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t g) m' ∧ ∀ u i jr sn e,
        C.ph (G' u) = .reg i jr sn e → C.Signalled m') G m d :=
  cond_signal_wp_unmetered hC hcost hp t g hgx hgo hsx io G m d hpl.2 hseen hi

/-! ## `wait`

The waiter's ghost values carry its deadline block in its part (`FLock.setPart`): `gD g p r` in
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

theorem gRD_set (hC : L.Fits (C.prim L) P U ok) {g : γ} {i jr : Nat} {sn sn' : Bool} {e : BitVec 32}
    {r : Res} : C.set (gRD L C g i jr sn e r) (.reg i jr sn' e) = gRD L C g i jr sn' e r := by
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
theorem dwait_wp [Zig.Os.HasEnv] (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {DR : BlockId → FAssn} {t : ThreadId} {g : γ} {i jr : Nat} {e : BitVec 32}
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    {q : Ptr} {r : Res} (G : ThreadId → γ) (m : Mem) (d : Nat) (hc : m.current = t)
    (hdp : DPart DR q bsD r) (hi : P.inv (upd G t (gRD L C g i jr false e r)) m) :
    P.WP t (Thread_Futex_Deadline_wait q C.Ep.ptr e) (fun x G' m' d' => x = .ok () ∧ d' < d ∧
      m'.current = t ∧ ∃ r', DPart DR q bsD r' ∧
        P.inv (upd G' t (gRD L C g i jr false e r')) m') G m d := by
  have hwaitLive (r' : Res) : ∀ (G₁ : ThreadId → γ) (m₁ : Mem),
      C.ph (G₁ t) = C.ph (gRD L C g i jr false e r') →
      L.ph (G₁ t) = .away → P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁ := by
    intro G₁ m₁ hph haway hi₁ hnot
    exact hlive G₁ m₁ ⟨i, jr, e, by simpa only [gRD_ph hC] using hph⟩ haway hi₁ hnot
  fsym [FCond.wp_liftPart hC (g := gRD L C g i jr false e r) (t := t)
      (hgo := .inl (gRD_lph hC)) (hi := hi) (hc := hc)
      (htt := dload (P := DR) (q := q))
      (hp := by simpa only [L.part_setPart] using hdp) (hret := .inl (.inr hcost)),
    FCond.wp_waitEp (ε := BitVec 32) (w := 32) hC
      (g := gRD L C g i jr false e _) (t := t) (e' := e) (i := i) (jr := jr) (e := e)
      (he := by simp [Packed.toBits]) (hg := gRD_ph hC) (hgo := gRD_lph hC)
      (hlive := hwaitLive _),
    gRD_ph hC, gRD_lph hC, L.part_setPart, L.setPart_setPart, threadFutexWaitC_eq]

/-- The inner loop's invariant: `t` registered (`sn`: it loaded the next epoch write), the state
value it read, its epoch value `e` while it has not seen the signal, and its deadline block. -/
def inv107 (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ)
    (t : ThreadId) (g : γ) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (s : Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ sn : Bool, ((s.state = 1 ∧ sn = false) ∨ s.state = 0x10001) ∧
    (sn = false → s.epoch = e) ∧ ∃ r, DPart DR q bsD r ∧
      P.inv (upd G t (gRD L C g i jr sn e r)) m

/-- The inner loop ends with no signal to take (`br106`), or with `t` holding the mutex again. -/
def post107 (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ)
    (t : ThreadId) (g : γ) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat)
    (x : Thread_Condition_FutexImpl_waitExit × Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
  ((x.1 = .br106 ∧ x.2.epoch = e ∧ ∃ r, DPart DR q bsD r ∧
      P.inv (upd G t (gRD L C g i jr false e r)) m) ∨
    (x.1 = .ret (.ok ()) ∧ ∃ rL r, DPart DR q bsD r ∧
      P.inv (upd G t (L.setPart (L.set g .holds rL) r)) m))

theorem mutex_pre_unmetered (t : ThreadId) (r : Res)
    (hu : 0 < r.gh.ac.frag .unmetered) : threadMutex.lock_pre t r := by
  first | exact hu | trivial

theorem mutex_post_iff {t : ThreadId} {r r' : Res} :
    threadMutex.lock_post t r r' ↔ r' = r := Iff.rfl

theorem loop107_body [Zig.Os.HasEnv] (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (DR : BlockId → FAssn) (hu : ∀ b r, DR b r → 0 < r.gh.ac.frag .unmetered)
    (hLc : L.c = mutexC) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (s : Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : inv107 DR P L C t g q i jr e D s G m d) :
    P.WP t ((Thread_Condition_FutexImpl_wait.loop107 C.S.ptr L.ptr).run s) (fun x G' m' d' =>
      if Thread_Condition_FutexImpl_wait.again107 x.1 then inv107 DR P L C t g q i jr e D x.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) x.2 <
          (fun (_ : Thread_Condition_FutexImpl_waitLocals) => 0) s)
      else post107 DR P L C t g q i jr e D x G' m' d') G m d := by
  fsym [hC.wp_tick_unmetered, DPart.unmetered hu,
    FCond.wp_consume hC (g := gRD L C g i jr _ e _) (t := t)
      (i := i) (jr := jr) (e := e) (hg := gRD_ph hC) (hgo := gRD_lph hC),
    threadMutex.lock_wp_resource (io := {}) hC hcost rfl hLc t (L.setPart (L.set g .out rnil) _)
      (by simp only [L.ph_setPart, L.ph_set])
      ((hC.ok_setPart _ _).mpr ((hC.ok_set g .out rnil).mpr hok)),
    mutex_pre_unmetered, mutex_post_iff,
    gRD_ph hC, gRD_lph hC, gRD_out hC hgx, gD_lock, hC.ok_setPart, hC.ok_set,
    L.part_setPart, L.setPart_setPart, inv107, post107,
    Thread_Condition_FutexImpl_wait.again107]

/-- The outer loop's invariant: `t` registered, before the signal, with its epoch value `e` and
its deadline block. -/
def inv29 (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ)
    (t : ThreadId) (g : γ) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (s : Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ s.epoch = e ∧ ∃ r, DPart DR q bsD r ∧
    P.inv (upd G t (gRD L C g i jr false e r)) m

/-- The outer loop ends with `t` holding the mutex again, with its deadline block. -/
def post29 (DR : BlockId → FAssn) (P : Proto Tgt γ) (L : FLock γ)
    (t : ThreadId) (g : γ) (q : Ptr) (D : Nat)
    (x : Thread_Condition_FutexImpl_waitExit × Thread_Condition_FutexImpl_waitLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ x.1 = .ret (.ok ()) ∧ m.current = t ∧ ∃ rL r, DPart DR q bsD r ∧
    P.inv (upd G t (L.setPart (L.set g .holds rL) r)) m

theorem loop29_body [Zig.Os.HasEnv] (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (DR : BlockId → FAssn) (hu : ∀ b r, DR b r → 0 < r.gh.ac.frag .unmetered)
    (hLc : L.c = mutexC) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g) (q : Ptr)
    (i jr : Nat) (e : BitVec 32) (D : Nat)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (s : Thread_Condition_FutexImpl_waitLocals) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : inv29 DR P L C t g q i jr e D s G m d) :
    P.WP t ((Thread_Condition_FutexImpl_wait.loop29 C.S.ptr L.ptr q).run s) (fun x G' m' d' =>
      if Thread_Condition_FutexImpl_wait.again29 x.1 then inv29 DR P L C t g q i jr e D x.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) x.2 <
          (fun (_ : Thread_Condition_FutexImpl_waitLocals) => 0) s)
      else post29 DR P L t g q D x G' m' d') G m d := by
  fsym [hC.wp_tick_unmetered, DPart.unmetered hu, hC.wp_projE (t := t),
    dwait_wp hC hcost (DR := DR) (t := t) (g := g) (i := i) (jr := jr) (e := e)
      hlive (q := q),
    FCond.wp_loadEpSn hC (g := gRD L C g i jr false e _) (t := t)
      (i := i) (jr := jr) (e := e) (hg := gRD_ph hC) (hgo := gRD_lph hC),
    FCond.wp_loadS hC (g := gRD L C g i jr _ e _) (t := t)
      (i := i) (jr := jr) (e := e) (hg := gRD_ph hC) (hgo := gRD_lph hC),
    WP.loop _ _ (inv107 DR P L C t g q i jr e d) (fun _ => 0)
      (post107 DR P L C t g q i jr e d)
      (loop107_body hC hcost DR hu hLc t g hgx hok q i jr e d),
    Bool.true_eq_false,
    gRD_ph hC, gRD_lph hC, gRD_set hC, L.part_setPart,
    FCond.ptr_ep, inv29, post29, inv107, post107,
    Thread_Condition_FutexImpl_wait.again29]

/-- `FutexImpl.wait(null)` by the mutex's holder, out of the condition's code: its deadline
block is in its part from the `alloc` (while it holds the mutex) to the `free` (after it locked
the mutex again). -/
theorem fwait_wp [Zig.Os.HasEnv] (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (DR : BlockId → FAssn) (hu : ∀ b r, DR b r → 0 < r.gh.ac.frag .unmetered)
    (hLc : L.c = mutexC) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds)
    (hok : ok g) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (halloc : FTTriple ((· = L.part g) ⋆ cur t) (allocStack 48 8)
      (fun q => DPart DR q (Array.replicate 48 .undef) ⋆ cur t))
    (hfree : ∀ q bs, bs.size = 48 → FTTriple (DPart DR q bs ⋆ cur t)
      (free q) (fun _ => (· = L.part g) ⋆ cur t))
    (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Thread_Condition_FutexImpl_wait C.S.ptr L.ptr none) (fun x G' m' d' => d' < d ∧
      x = .ok () ∧ m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  have hi0 := hC.enterEn hgx hgh hone hhb hent hi
  fsym [FCond.wp_liftPartCur hC (g := C.set g .en) (t := t)
      (hgo := .inr (by simpa only [hC.lph] using hgh)) (hi := hi0) (hc := hc)
      (htt := halloc) (hp := by simp only [hC.lpart]) (hret := .inl (.inr hcost)),
    FCond.wp_liftPartCur hC (hret := .inl (.inr hcost)), hfree,
    FCond.wp_liftPart hC (htt := dstore (P := DR) (bs := Array.replicate 48 .undef) (by simp))
      (hret := .inl (.inr hcost)), dstore,
    hC.wp_projE (t := t),
    FCond.wp_ldEp hC (g := gD L C g .en _) (t := t) (hg := gD_ph hC)
      (hgh := by simpa only [gD_lph hC] using hgh),
    FCond.wp_reg hC (g := gD L C g (.ld _ _) _) (t := t) (hg := gD_ph hC)
      (hgh := by simpa only [gD_lph hC] using hgh),
    threadMutex.unlock_wp (io := {}) hC hcost rfl hLc t
      (gD L C g (.reg _ _ false _) _)
      (by simpa only [gD_lph hC] using hgh)
      ((hC.ok_setPart _ _).mpr
        ((hC.ok_calm g (.reg _ _ false _) .out rfl rfl).mpr
          (by simpa only [FCond.set_of hgx] using hok))),
    (fun (q : Ptr) (i jr : Nat) (e : BitVec 32) =>
      WP.loop _ _ (inv29 DR P L C t g q i jr e d) (fun _ => 0)
        (post29 DR P L t g q d)
        (loop29_body hC hcost DR hu hLc t g hgx hok q i jr e d hlive)),
    dinit_eq, bsD_size, gD_ph hC, gD_lph hC, gD_set hC, gD_unlock hC, gD_free,
    hC.lpart, hC.ok_setPart, hC.ok_calm, FCond.set_of, L.part_setPart, L.setPart_setPart,
    FCond.ptr_ep, inv29, post29]

/-- **`Condition.wait`** by the mutex's holder, out of the condition's code: it returns holding
the mutex again. -/
theorem cond_wait_wp_resource [Zig.Os.HasEnv] (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = mutexC) (t : ThreadId) (g : γ)
    (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (_io : Io) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hpre : deadlinePre t (L.part g)) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Thread_Condition_wait p q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r' rL, keepPart t (L.part g) r' ∧
        P.inv (upd G' t (L.set (L.setPart g r') .holds rL)) m') G m d := by
  subst hp hq
  obtain ⟨DR, hu, halloc, hfree⟩ := deadlinePre.elim hpre
  fsym [fwait_wp hC hcost DR hu hLc t g hgx hgh hok G m d hone hhb hent hlive halloc hfree hi hc,
    keepPart, L.setPart_self]

/-- The concrete Plain convenience is an endpoint specialization of the same resource proof. -/
theorem cond_wait_wp [Zig.Os.HasEnv] (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = mutexC) (t : ThreadId) (g : γ)
    (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    (hpl : (L.part g).Plain) (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (Thread_Condition_wait p q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  refine WP.mono ?_ (cond_wait_wp_resource hC hcost hp hq hLc t g hgx hgh hok io G m d
    hone hhb hent hlive (.inl hpl) hi hc)
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
  signal_during := keepPart
  signal_post := keepPart
  signal_plain_pre _ _ := payUnmetered_plain
  signal_plain_post _ _ _ _ hr := hr
  wait_wp_resource := cond_wait_wp_resource
  signal_wp_resource := cond_signal_wp_resource

end Threadsync
