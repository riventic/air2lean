import Proofs.Threadsync.Variant
import ZigLean.Sep.Full.Mutex

/-!
# `Thread.Mutex` of `examples/threadsync` as a mutex (`MutexImpl`, 0.15.2, Linux and macOS)

The per-item obligation of `Thread.Mutex` (Zig 0.15.2's std code) in this program's generated
code: `Thread_Mutex_lock` and `Thread_Mutex_unlock` satisfy the mutex contract
(`ZigLean/Sep/Full/Mutex.lean`) for every protocol that has the lock (`FLock.Fits`). The steps
are the rules of a lock's code (`ZigLean/Sep/Full/LockRules.lean`); this file follows the
generated control flow. The translation depends on the target (`Proofs/Threadsync/Variant.lean`):

- **Linux** (`FutexImpl`, the committed `Gen.lean`): `tryLock` is an acquire `or(1)`
  (`wp_orLock`), or on aarch64-linux (`tests/golden/0.15.2/threadsync/Gen-linux-aarch64.lean`) a
  weak acquire `cmpxchg` `0 → 1` (`wp_casWeakLock`); `lockSlow` a relaxed load and a loop of
  `xchg(3)` with a futex wait, `unlock` the owner check, an `xchg(0)` with a release and a wake.
  The contended value is `3`.
- **macOS** (`DarwinImpl`): `lock` is `os_unfair_lock_lock` (`Zig.osUnfairLockC`): a loop of an
  acquire `cmpxchg 0 → 1` with a futex wait while the word is `1`; `unlock` the owner check, a
  release `xchg 0` and a wake. The contended value is `1`.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FLock

namespace Threadsync

/-- The states of `Thread.Mutex.FutexImpl`: `unlocked`, `locked`, `contended` (`3`). -/
def threadMutexW : LockWord.States (BitVec 32) where
  unl := 0
  one := 1
  two := 3
  c := 3
  bits0 := rfl
  bits1 := rfl
  bits2 := rfl
  dec0 := rfl
  dec1 := rfl
  dec2 := rfl
  ne01 := by decide
  ne02 := by decide
  ne12 := by decide

namespace ThreadMutex

variable {γ : Type} {L : FLock γ} {K : FPrim γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

if_decl Thread_Mutex_FutexImpl_lock in

/-- `tryLock` by thread `t` at `out` (`g`): `true` and `t` holds the mutex, or `false` and `t` is
at `spin`. -/
theorem tryLock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc3 : L.c = 3) {p : Ptr}
    (hp : p = L.ptr) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_FutexImpl_tryLock p) (fun r G' m' d' => d' < d ∧ m'.current = t ∧
      ((r = true ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') ∨
       (r = false ∧ P.inv (upd G' t (L.set g .spin rnil)) m'))) G m d := by
  unfold Thread_Mutex_FutexImpl_tryLock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
  rw [hp]
  first
  | -- x86 (`lock bts`): an acquire `or(1)`.
    refine WP.bind (wp_orLock hP hc3 hg hok hi fun k hk G₁ m₁ r hc₁ hcase => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    rcases hcase with ⟨rfl, rL, hi₁⟩ | ⟨hr, hi₁⟩
    · exact WP.pure' ⟨by omega, hc₁, .inl ⟨by decide, rL, hi₁⟩⟩
    · rcases hr with rfl | rfl
      · exact WP.pure' ⟨by omega, hc₁, .inr ⟨by decide, hi₁⟩⟩
      · exact WP.pure' ⟨by omega, hc₁, .inr ⟨by decide, hi₁⟩⟩
  | -- Other architectures (0.15.2 on aarch64-linux): a weak acquire `cmpxchg` `0 → 1`.
    refine WP.bind (wp_casWeakLock hP hg hok hi fun k hk G₁ m₁ r hc₁ hcase => ?_)
    refine WP.pure' ?_
    rcases hcase with ⟨rfl, rL, hi₁⟩ | ⟨⟨v, rfl⟩, hi₁⟩
    · exact WP.pure' ⟨by omega, hc₁, .inl ⟨rfl, rL, hi₁⟩⟩
    · exact WP.pure' ⟨by omega, hc₁, .inr ⟨rfl, hi₁⟩⟩

/-- The loop invariant of `lockSlow`: thread `t` is at `spin`. -/
def lockInv (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Thread_Mutex_FutexImpl_lockSlowLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t (L.set g .spin rnil)) m

/-- The loop of `lockSlow` ends when thread `t` holds the mutex. -/
def lockPost (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Thread_Mutex_FutexImpl_lockSlowExit × Thread_Mutex_FutexImpl_lockSlowLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = .br15 ∧ d < D ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

/-- One repeat of `lockSlow`'s loop: `xchg(3)`; the thread holds the mutex, or it waits at the
futex (a stop, so the depth gets smaller). -/
theorem loop16_body (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc3 : L.c = 3)
    (t : ThreadId) (g : γ) (hok : ok g) (D : Nat) (s : Thread_Mutex_FutexImpl_lockSlowLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : lockInv P L t g D s G m d) :
    P.WP t ((Thread_Mutex_FutexImpl_lockSlow.loop16 L.ptr).run s) (fun r G' m' d' =>
      if Thread_Mutex_FutexImpl_lockSlow.again16 r.1 then lockInv P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 <
          (fun (_ : Thread_Mutex_FutexImpl_lockSlowLocals) => 0) s)
      else lockPost P L t g D r G' m' d') G m d := by
  obtain ⟨hD, -, hi⟩ := h
  have hS : threadMutexW.c = L.c := hc3.symm
  have hok' : ∀ q h, ok (L.set g q h) := fun _ _ => (hP.ok_set _ _ _).mpr hok
  unfold Thread_Mutex_FutexImpl_lockSlow.loop16
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [atomicRmwC_eq]
  refine WP.bind (wp_xchgLockOn hP threadMutexW hS (g := L.set g .spin rnil) (L.ph_set _ _ _)
    (hok' _ _) hi fun k hk G₁ m₁ r hc₁ hcase => ?_)
  simp only [L.set_set] at hcase
  rcases hcase with ⟨rfl, rL, hi₁⟩ | ⟨hr, hi₁⟩
  · simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Bool.false_eq_true, ↓reduceIte, Thread_Mutex_FutexImpl_lockSlow.again16]
    exact ⟨rfl, by omega, hc₁, rL, hi₁⟩
  · have hne : (r != (0 : BitVec 32)) = true := by simpa [threadMutexW] using hr
    simp only [StateT.run_pure, pure_bind, hne, ↓reduceIte, StateT.run_bind, bind_assoc]
    rw [threadFutexWaitC_eq]
    refine WP.bind (wp_waitOn hP threadMutexW hS (g := L.set g .wait rnil) (L.ph_set _ _ _)
      (hok' _ _) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Thread_Mutex_FutexImpl_lockSlow.again16, ↓reduceIte]
    rw [L.set_set] at hi₂
    exact ⟨⟨by omega, hc₂, hi₂⟩, .inl (by omega)⟩

/-- `lockSlow` by thread `t` at `spin`: it holds the mutex. -/
theorem lockSlow_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc3 : L.c = 3) {p : Ptr}
    (hp : p = L.ptr) (t : ThreadId) (g : γ) (hok : ok g) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (L.set g .spin rnil)) m) :
    P.WP t (Thread_Mutex_FutexImpl_lockSlow p) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp
  have hS : threadMutexW.c = L.c := hc3.symm
  have hok' : ∀ q h, ok (L.set g q h) := fun _ _ => (hP.ok_set _ _ _).mpr hok
  unfold Thread_Mutex_FutexImpl_lockSlow
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  -- the loop, from `spin`
  have hloop : ∀ G₃ m₃ d₃, lockInv P L t g d default G₃ m₃ d₃ →
      P.WP t ((do
          let __do_lift ← loop (Thread_Mutex_FutexImpl_lockSlow.loop16 L.ptr)
            Thread_Mutex_FutexImpl_lockSlow.again16
          match __do_lift with
          | Thread_Mutex_FutexImpl_lockSlowExit.br15 => pure Thread_Mutex_FutexImpl_lockSlowExit.ret
          | e => pure e : CM Tgt Thread_Mutex_FutexImpl_lockSlowLocals
            Thread_Mutex_FutexImpl_lockSlowExit).run default)
        (fun a G₄ m₄ d₄ => P.WP t (match a.1 with
          | Thread_Mutex_FutexImpl_lockSlowExit.ret => pure ()
          | _ => throw Error.panic)
          (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
            ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G₄ m₄ d₄)
        G₃ m₃ d₃ := by
    intro G₃ m₃ d₃ h₃
    simp only [StateT.run_bind]
    refine WP.bind (WP.mono ?_ (WP.loop _ _ (lockInv P L t g d) (fun _ => 0) (lockPost P L t g d)
      (loop16_body hP hcost hc3 t g hok d) default G₃ m₃ d₃ h₃))
    rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', rL, hi'⟩
    simp only [StateT.run_pure]
    exact WP.pure' (WP.pure' ⟨hd', hc', rL, hi'⟩)
  refine WP.bind (wp_loadLock hP (g := L.set g .spin rnil) (by rw [L.ph_set]; decide) (hok' _ _)
    hi fun k₁ hk₁ G₁ m₁ v hc₁ hi₁ => ?_)
  simp only [StateT.run_pure, pure_bind]
  by_cases hv : (v == (3 : BitVec 32)) = true
  · simp only [hv, ↓reduceIte, StateT.run_bind, bind_assoc]
    have hw := hP.toWait (hok' _ _) (L.ph_set _ _ _) hi₁
    rw [L.set_set] at hw
    rw [threadFutexWaitC_eq]
    refine WP.bind (wp_waitOn hP threadMutexW hS (g := L.set g .wait rnil) (L.ph_set _ _ _)
      (hok' _ _) hw fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    rw [L.set_set] at hi₂
    exact hloop G₂ m₂ k₂ ⟨by omega, hc₂, hi₂⟩
  · simp only [Bool.not_eq_true] at hv
    simp only [hv, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hloop G₁ m₁ k₁ ⟨by omega, hc₁, hi₁⟩

/-- `FutexImpl.lock` by thread `t` at `out` (`g`): it holds the mutex. -/
theorem futexLock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc3 : L.c = 3) {p : Ptr}
    (hp : p = L.ptr) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_FutexImpl_lock p) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  unfold Thread_Mutex_FutexImpl_lock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (WP.callC (WP.mono ?_ (tryLock_wp hP hcost hc3 hp t g hg hok G m d hi)))
  rintro r G₁ m₁ d₁ ⟨hd₁, hc₁, ⟨rfl, rL, hi₁⟩ | ⟨rfl, hi₁⟩⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨hd₁, hc₁, rL, hi₁⟩)
  · simp only [Bool.not_false, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callC (WP.mono ?_ (lockSlow_wp hP hcost hc3 hp t g hok G₁ m₁ d₁ hi₁)))
    rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, rL, hi₂⟩
    simp only [StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨by omega, hc₂, rL, hi₂⟩)

/-- `Thread.Mutex.lock` is `FutexImpl.lock` (Linux). -/
theorem lock_eq (p : Ptr) : Thread_Mutex_lock p =
    (Thread_Mutex_FutexImpl_lock p >>= fun _ => pure ()) := by
  unfold Thread_Mutex_lock
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, pure_bind, callC, StateT.run_lift,
    bind_assoc, map_bind, map_pure]

/-- `lock` (Linux) by thread `t` at `out` (`g`): it holds the mutex, with a resource `rL`. -/
theorem lock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (_ : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  rw [lock_eq]
  exact WP.bind (WP.mono (fun _ _ _ _ hq => WP.pure' hq)
    (futexLock_wp hP hcost hc hp t g hg hok G m d hi))

/-- `Thread.Mutex.unlock` is `FutexImpl.unlock` (Linux). -/
theorem unlock_eq (p : Ptr) : Thread_Mutex_unlock p =
    (Thread_Mutex_FutexImpl_unlock p >>= fun _ => pure ()) := by
  unfold Thread_Mutex_unlock
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, pure_bind, callC, StateT.run_lift,
    bind_assoc, map_bind, map_pure]

/-- `unlock` (Linux) by the holder `t` (`g`), the current thread: the owner check passes, and it
goes to `out`. -/
theorem unlock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (hok : ok g) (_ : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) (hcur : m.current = t) :
    P.WP t (Thread_Mutex_unlock p) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d := by
  subst hp
  have hS : threadMutexW.c = L.c := hc.symm
  have hok' : ∀ q h, ok (L.set g q h) := fun _ _ => (hP.ok_set _ _ _).mpr hok
  rw [unlock_eq]
  refine WP.bind (WP.mono (fun _ _ _ _ hq => WP.pure' hq) ?_)
  unfold Thread_Mutex_FutexImpl_unlock
  obtain ⟨rX, hiL, -⟩ := (hP.inv _ _).mp hi
  have hrun := hiL.w.ownerCheck (t := t) (by show L.ph (upd G t g t) = _; rw [upd_self]; exact hg)
    hcur
  refine WP.ownerCheck hrun ?_
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [atomicRmwC_eq]
  refine WP.bind (wp_xchgUnlockOn hP threadMutexW hS (g := g) hg hok hi
    fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [StateT.run_pure, pure_bind]
    refine WP.bind (WP.callRC_ok (by rfl) ?_)
    simp only [show (threadMutexW.one == 3) = false by decide, Bool.false_eq_true, ↓reduceIte,
      StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨by omega, hc₁, hi₁⟩)
  · simp only [StateT.run_pure, pure_bind]
    refine WP.bind (WP.callRC_ok (by rfl) ?_)
    simp only [show (threadMutexW.two == 3) = true by decide, ↓reduceIte, StateT.run_bind,
      bind_assoc]
    rw [threadFutexWakeC_eq]
    refine WP.bind (wp_wakeOn hP (g := L.set g .wake rnil) (L.ph_set _ _ _) (hok' _ _) hi₁
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    rw [L.set_set] at hi₂
    exact WP.pure' (WP.pure' ⟨by omega, hc₂, hi₂⟩)

end_if

if_decl Thread_Mutex_DarwinImpl in

/-- The loop invariant of `os_unfair_lock_lock`: thread `t` is at `out` (`g`, the first try) or at
`spin` (after a futex wait). -/
def lockInvD (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Thread_Mutex_lockLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d ≤ D ∧ ∃ g₀, (g₀ = g ∨ g₀ = L.set g .spin rnil) ∧ P.inv (upd G t g₀) m

/-- The loop ends when thread `t` holds the mutex. -/
def lockPostD (P : Proto Tgt γ) (L : FLock γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Bool × Thread_Mutex_lockLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = false ∧ d < D ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

/-- One repeat of the loop: the `cmpxchg 0 → 1`; the thread holds the mutex, or it waits at the
futex (a stop, so the depth gets smaller). -/
theorem loopD_body (hP : L.Fits K P U ok) (hcost : P.cost = none) (hc1 : L.c = 1) (t : ThreadId)
    (g : γ) (hg : L.ph g = .out) (hok : ok g) (D : Nat) (s : Thread_Mutex_lockLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : lockInvD P L t g D s G m d) :
    P.WP t ((osUnfairLockTry L.ptr : CM Tgt Thread_Mutex_lockLocals Bool).run s) (fun r G' m' d' =>
      if id r.1 then lockInvD P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Thread_Mutex_lockLocals) => 0) s)
      else lockPostD P L t g D r G' m' d') G m d := by
  obtain ⟨hD, g₀, hg₀, hi⟩ := h
  have hset : ∀ q h, L.set g₀ q h = L.set g q h := by
    intro q h; rcases hg₀ with rfl | rfl
    · rfl
    · exact L.set_set _ _ _ _ _
  have hph : L.ph g₀ = .out ∨ L.ph g₀ = .spin := by
    rcases hg₀ with rfl | rfl
    · exact .inl hg
    · exact .inr (L.ph_set _ _ _)
  have hok₀ : ok g₀ := by
    rcases hg₀ with rfl | rfl
    · exact hok
    · exact (hP.ok_set _ _ _).mpr hok
  unfold osUnfairLockTry
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (wp_casD hP hc1 hph hok₀ hi fun k hk G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, rL, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [id, Bool.false_eq_true, ↓reduceIte]
    rw [hset] at hi₁
    exact ⟨rfl, by omega, hc₁, rL, hi₁⟩
  · simp only [StateT.run_bind, bind_assoc, pure_bind]
    rw [hset] at hi₁
    refine WP.bind (wp_waitD hP (g := L.set g .wait rnil) (L.ph_set _ _ _)
      ((hP.ok_set _ _ _).mpr hok) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [id, ↓reduceIte]
    rw [L.set_set] at hi₂
    exact ⟨⟨by omega, _, .inr rfl, hi₂⟩, .inl (by omega)⟩

/-- `lock` (macOS) by thread `t` at `out` (`g`): it holds the mutex. -/
theorem lock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g) (_ : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp
  have hc1 : L.c = 1 := hc
  unfold Thread_Mutex_lock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  unfold osUnfairLockC
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (lockInvD P L t g d) (fun _ => 0) (lockPostD P L t g d)
    (loopD_body hP hcost hc1 t g hg hok d) default G m d ⟨by omega, g, .inl rfl, hi⟩))
  rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', rL, hi'⟩
  simp only [StateT.run_pure, pure_bind]
  exact WP.pure' (WP.pure' ⟨hd', hc', rL, hi'⟩)

/-- `unlock` (macOS) by the holder `t` (`g`), the current thread: it goes to `out`. -/
theorem unlock_wp (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hc : L.c = mutexC) (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (hok : ok g) (_ : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) (hcur : m.current = t) :
    P.WP t (Thread_Mutex_unlock p) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d := by
  subst hp
  have hc1 : L.c = 1 := hc
  unfold Thread_Mutex_unlock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  unfold osUnfairUnlockC
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  -- the owner check: `t` holds the lock, so it made the most recent acquire of the word
  obtain ⟨rX, hiL, -⟩ := (hP.inv _ _).mp hi
  have hrun := hiL.w.ownerCheck (t := t) (by show L.ph (upd G t g t) = _; rw [upd_self]; exact hg)
    hcur
  refine WP.bind (WP.callMC (fun e he => by rw [hrun] at he; cases he) fun _ m₀ hr => ?_)
  rw [hrun] at hr
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  refine ⟨rfl, ?_⟩
  refine WP.bind (wp_xchgRel hP hc1 hg hok hi fun k₁ hk₁ G₁ m₁ r hc₁ hi₁ => ?_)
  simp only [StateT.run_pure, pure_bind]
  rw [threadFutexWakeC_eq]
  refine WP.bind (wp_wakeOn hP (g := L.set g .wake rnil) (L.ph_set _ _ _)
    ((hP.ok_set _ _ _).mpr hok) hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
  simp only [StateT.run_pure, pure_bind]
  rw [L.set_set] at hi₂
  exact WP.pure' (WP.pure' ⟨by omega, hc₂, hi₂⟩)

end_if

end ThreadMutex

/-- **`Thread.Mutex` of this program is a mutex** (`MutexImpl`), on Linux and on macOS. -/
def threadMutex : MutexImpl Tgt where
  lock p _ := Thread_Mutex_lock p
  unlock p _ := Thread_Mutex_unlock p
  c := mutexC
  lock_wp hP hcost := ThreadMutex.lock_wp hP hcost
  unlock_wp hP hcost := ThreadMutex.unlock_wp hP hcost

end Threadsync
