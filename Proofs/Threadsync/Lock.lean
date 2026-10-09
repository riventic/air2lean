import Lean.Elab.Command
import Proofs.Threadsync.Gen
import ZigLean.Conc.LockRules

/-!
# `lock` and `unlock` of the translated `Thread.Mutex` (0.15.2, Linux and macOS)

The control flow of the generated `Thread_Mutex_lock` and `Thread_Mutex_unlock`, with the rules of
a lock (`ZigLean/Conc/LockRules.lean`), for every protocol that has the lock (`Lock.Fits`). The
translation depends on the OS (`tests/golden/0.15.2/threadsync/Gen-darwin.lean`); this file proves
`lock_spec` and `unlock_spec` for both, and the other files do not tell them apart:

- **Linux** (`FutexImpl`, the committed `Gen.lean`): `tryLock` is an acquire `or(1)`, `lockSlow` a
  relaxed load and a loop of `xchg(3)` with a futex wait, `unlock` an `xchg(0)` with a release and
  a wake. The contended value is `3`.
- **macOS** (`DarwinImpl`): `lock` is `os_unfair_lock_lock`, a model of the C function
  (`Zig.osUnfairLockC`): a loop of an acquire `cmpxchg 0 → 1` with a futex wait while the word is
  `1`. `unlock` is a release `xchg 0` and a wake. The contended value is `1`.

The code of the other translation does not exist, so `if_decl` checks the translation before it
compiles the proofs that name it.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock

namespace Threadsync

/-- Compile the commands only if the translation declares `id` (the `Thread.Mutex` of one OS). -/
elab "if_decl " id:ident " in " cmds:command* " end_if" : command => do
  let found ← Lean.Elab.Command.liftCoreM
    (try discard <| Lean.resolveGlobalConstNoOverload id; pure true catch _ => pure false)
  if found then cmds.forM Lean.Elab.Command.elabCommand

/-- The states of `Thread.Mutex.FutexImpl`: `unlocked`, `locked`, `contended` (`3`). -/
def threadMutexS : States (BitVec 32) where
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

if_decl Thread_Mutex_FutexImpl_lock in
/-- The contended value of the mutex word (Linux `FutexImpl`). The lock of the proofs has this
`Lock.c`. -/
def mutexC : Nat := 3

/-- The `Thread.Mutex` with the word `w`. -/
abbrev mutexOf (w : BitVec 32) : Thread_Mutex := { impl := { state := { raw := w } } }
end_if

if_decl Thread_Mutex_DarwinImpl in
/-- The contended value of the mutex word (macOS: the word is only `0` or `1`). The lock of the
proofs has this `Lock.c`. -/
def mutexC : Nat := 1

/-- The `Thread.Mutex` with the word `w`. -/
abbrev mutexOf (w : BitVec 32) : Thread_Mutex :=
  { impl := { oul := { _os_unfair_lock_opaque := w } } }
end_if

namespace ThreadMutexOps

variable {γ : Type} {L : Lock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Mem → Prop}

if_decl Thread_Mutex_FutexImpl_lock in

/-- `tryLock` by thread `t` at `out` (`g`): `true` and `t` holds the mutex, or `false` and `t` is
at `spin`. -/
theorem tryLock_spec (hP : L.Fits P U) (hc3 : L.c = 3) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (hg : L.ph g = .out) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_FutexImpl_tryLock p) (fun r G' m' d' => d' < d ∧ m'.current = t ∧
      ((r = true ∧ ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') ∨
       (r = false ∧ P.inv (upd G' t (L.set g .spin Heap.empty)) m'))) G m d := by
  unfold Thread_Mutex_FutexImpl_tryLock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
  rw [hp]
  refine WP.bind (wp_orLock hP hc3 hg hi fun k hk G₁ m₁ r hc₁ hcase => ?_)
  simp only [StateT.run_pure, pure_bind]
  refine WP.pure' ?_
  rcases hcase with ⟨rfl, hL, hi₁⟩ | ⟨hr, hi₁⟩
  · exact WP.pure' ⟨by omega, hc₁, .inl ⟨by decide, hL, hi₁⟩⟩
  · rcases hr with rfl | rfl
    · exact WP.pure' ⟨by omega, hc₁, .inr ⟨by decide, hi₁⟩⟩
    · exact WP.pure' ⟨by omega, hc₁, .inr ⟨by decide, hi₁⟩⟩

/-- The loop invariant of `lockSlow`: thread `t` is at `spin`. -/
def lockInv (P : Proto Tgt γ) (L : Lock γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Thread_Mutex_FutexImpl_lockSlowLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ P.inv (upd G t (L.set g .spin Heap.empty)) m

/-- The loop of `lockSlow` ends when thread `t` holds the mutex. -/
def lockPost (P : Proto Tgt γ) (L : Lock γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Thread_Mutex_FutexImpl_lockSlowExit × Thread_Mutex_FutexImpl_lockSlowLocals)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = .br15 ∧ d < D ∧ m.current = t ∧ ∃ hL, P.inv (upd G t (L.set g .holds hL)) m

/-- One repeat of `lockSlow`'s loop: `xchg(3)`; the thread holds the mutex, or it waits at the
futex (a stop, so the depth gets smaller). -/
theorem loop16_body (hP : L.Fits P U) (hc3 : L.c = 3) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (D : Nat) (s : Thread_Mutex_FutexImpl_lockSlowLocals) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (h : lockInv P L t g D s G m d) :
    P.WP t ((Thread_Mutex_FutexImpl_lockSlow.loop16 p).run s) (fun r G' m' d' =>
      if Thread_Mutex_FutexImpl_lockSlow.again16 r.1 then lockInv P L t g D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 <
          (fun (_ : Thread_Mutex_FutexImpl_lockSlowLocals) => 0) s)
      else lockPost P L t g D r G' m' d') G m d := by
  obtain ⟨hD, -, hi⟩ := h
  have hS : threadMutexS.c = L.c := hc3.symm
  unfold Thread_Mutex_FutexImpl_lockSlow.loop16
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [hp, atomicRmwC_eq]
  refine WP.bind (wp_xchgLock hP threadMutexS hS (g := L.set g .spin Heap.empty) (L.ph_set _ _ _)
    hi fun k hk G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hL, hi₁⟩ | ⟨hr, hi₁⟩
  · simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [threadMutexS, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Thread_Mutex_FutexImpl_lockSlow.again16]
    rw [L.set_set] at hi₁
    exact ⟨rfl, by omega, hc₁, hL, hi₁⟩
  · have hne : (r != (0 : BitVec 32)) = true := by simpa [threadMutexS] using hr
    simp only [StateT.run_pure, pure_bind]
    simp only [hne, ↓reduceIte, StateT.run_bind, bind_assoc, pure_bind]
    rw [L.set_set] at hi₁
    rw [threadFutexWaitC_eq]
    refine WP.bind (wp_wait hP threadMutexS hS (g := L.set g .wait Heap.empty) (L.ph_set _ _ _)
      hi₁ fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Thread_Mutex_FutexImpl_lockSlow.again16, ↓reduceIte]
    rw [L.set_set] at hi₂
    exact ⟨⟨by omega, hc₂, hi₂⟩, .inl (by omega)⟩

/-- `lockSlow` by thread `t` at `spin`: it holds the mutex. -/
theorem lockSlow_spec (hP : L.Fits P U) (hc3 : L.c = 3) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (L.set g .spin Heap.empty)) m) :
    P.WP t (Thread_Mutex_FutexImpl_lockSlow p) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G m d := by
  have hS : threadMutexS.c = L.c := hc3.symm
  unfold Thread_Mutex_FutexImpl_lockSlow
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [hp]
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
            ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G₄ m₄ d₄)
        G₃ m₃ d₃ := by
    intro G₃ m₃ d₃ h₃
    simp only [StateT.run_bind]
    refine WP.bind (WP.mono ?_ (WP.loop _ _ (lockInv P L t g d) (fun _ => 0) (lockPost P L t g d)
      (loop16_body hP hc3 rfl t g d) default G₃ m₃ d₃ h₃))
    rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', hL, hi'⟩
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    exact WP.pure' ⟨hd', hc', hL, hi'⟩
  refine WP.bind (wp_loadLock hP (g := L.set g .spin Heap.empty) (by rw [L.ph_set]; decide) hi
    fun k₁ hk₁ G₁ m₁ v hc₁ hi₁ => ?_)
  simp only [StateT.run_pure, pure_bind]
  by_cases hv : (v == (3 : BitVec 32)) = true
  · simp only [hv, ↓reduceIte, StateT.run_bind, bind_assoc, pure_bind]
    have hw := hP.toWait (L.ph_set _ _ _) hi₁
    rw [L.set_set] at hw
    rw [threadFutexWaitC_eq]
    refine WP.bind (wp_wait hP threadMutexS hS (g := L.set g .wait Heap.empty) (L.ph_set _ _ _)
      hw fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    rw [L.set_set] at hi₂
    exact hloop G₂ m₂ k₂ ⟨by omega, hc₂, hi₂⟩
  · simp only [Bool.not_eq_true] at hv
    simp only [hv, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hloop G₁ m₁ k₁ ⟨by omega, hc₁, hi₁⟩

/-- `FutexImpl.lock` by thread `t` at `out` (`g`): it holds the mutex. -/
theorem futexLock_spec (hP : L.Fits P U) (hc3 : L.c = 3) {p : Ptr} (hp : p = L.ptr)
    (t : ThreadId) (g : γ) (hg : L.ph g = .out) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_FutexImpl_lock p) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G m d := by
  unfold Thread_Mutex_FutexImpl_lock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (WP.callC (WP.mono ?_ (tryLock_spec hP hc3 hp t g hg G m d hi)))
  rintro r G₁ m₁ d₁ ⟨hd₁, hc₁, ⟨rfl, hL, hi₁⟩ | ⟨rfl, hi₁⟩⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨hd₁, hc₁, hL, hi₁⟩)
  · simp only [Bool.not_false, ↓reduceIte, StateT.run_bind, bind_assoc, pure_bind]
    refine WP.bind (WP.callC (WP.mono ?_ (lockSlow_spec hP hc3 hp t g G₁ m₁ d₁ hi₁)))
    rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hL, hi₂⟩
    simp only [StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨by omega, hc₂, hL, hi₂⟩)

/-- `Thread.Mutex.lock` is `FutexImpl.lock` (Linux). -/
theorem lock_eq (p : Ptr) : Thread_Mutex_lock p =
    (Thread_Mutex_FutexImpl_lock p >>= fun _ => pure ()) := by
  unfold Thread_Mutex_lock
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, pure_bind, callC, StateT.run_lift,
    bind_assoc, map_bind, map_pure, Ptr.add_zero]

/-- `lock` (Linux) by thread `t` at `out` (`g`): it holds the mutex, with a resource `hL`. -/
theorem lockL_spec (hP : L.Fits P U) (hc3 : L.c = 3) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (hg : L.ph g = .out) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G m d := by
  rw [lock_eq]
  exact WP.bind (WP.mono (fun _ _ _ _ hq => WP.pure' hq)
    (futexLock_spec hP hc3 hp t g hg G m d hi))

/-- `FutexImpl.unlock` by the holder `t` (`g`): it goes to `out`. -/
theorem futexUnlock_spec (hP : L.Fits P U) (hc3 : L.c = 3) {p : Ptr} (hp : p = L.ptr)
    (t : ThreadId) (g : γ) (hg : L.ph g = .holds) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_FutexImpl_unlock p) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = t ∧ P.inv (upd G' t (L.set g .out Heap.empty)) m') G m d := by
  have hS : threadMutexS.c = L.c := hc3.symm
  unfold Thread_Mutex_FutexImpl_unlock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [hp, atomicRmwC_eq]
  refine WP.bind (wp_xchgUnlock hP threadMutexS hS (g := g) hg hi
    fun k₁ hk₁ G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [StateT.run_pure, pure_bind]
    refine WP.bind (WP.callRC_ok (by rfl) ?_)
    simp only [show (threadMutexS.one == 3) = false by decide, Bool.false_eq_true, ↓reduceIte,
      StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' ⟨by omega, hc₁, hi₁⟩)
  · simp only [StateT.run_pure, pure_bind]
    refine WP.bind (WP.callRC_ok (by rfl) ?_)
    simp only [show (threadMutexS.two == 3) = true by decide, ↓reduceIte, StateT.run_bind,
      bind_assoc, pure_bind]
    rw [threadFutexWakeC_eq]
    refine WP.bind (wp_wake hP (g := L.set g .wake Heap.empty) (L.ph_set _ _ _) hi₁
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    rw [L.set_set] at hi₂
    exact WP.pure' (WP.pure' ⟨by omega, hc₂, hi₂⟩)

/-- `Thread.Mutex.unlock` is `FutexImpl.unlock` (Linux). -/
theorem unlock_eq (p : Ptr) : Thread_Mutex_unlock p =
    (Thread_Mutex_FutexImpl_unlock p >>= fun _ => pure ()) := by
  unfold Thread_Mutex_unlock
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, pure_bind, callC, StateT.run_lift,
    bind_assoc, map_bind, map_pure, Ptr.add_zero]

/-- `unlock` (Linux) by the holder `t` (`g`): it goes to `out`. -/
theorem unlockL_spec (hP : L.Fits P U) (hc3 : L.c = 3) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (hg : L.ph g = .holds) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_unlock p) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = t ∧ P.inv (upd G' t (L.set g .out Heap.empty)) m') G m d := by
  rw [unlock_eq]
  exact WP.bind (WP.mono (fun _ _ _ _ hq => WP.pure' hq)
    (futexUnlock_spec hP hc3 hp t g hg G m d hi))

end_if

if_decl Thread_Mutex_DarwinImpl in

/-- The loop invariant of `os_unfair_lock_lock`: thread `t` is at `out` (`g`, the first try) or at
`spin` (after a futex wait). -/
def lockInvD (P : Proto Tgt γ) (L : Lock γ) (t : ThreadId) (g : γ) (D : Nat)
    (_ : Thread_Mutex_lockLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d ≤ D ∧ ∃ g₀, (g₀ = g ∨ g₀ = L.set g .spin Heap.empty) ∧ P.inv (upd G t g₀) m

/-- The loop ends when thread `t` holds the mutex. -/
def lockPostD (P : Proto Tgt γ) (L : Lock γ) (t : ThreadId) (g : γ) (D : Nat)
    (r : Bool × Thread_Mutex_lockLocals) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  r.1 = false ∧ d < D ∧ m.current = t ∧ ∃ hL, P.inv (upd G t (L.set g .holds hL)) m

/-- One repeat of the loop: the `cmpxchg 0 → 1`; the thread holds the mutex, or it waits at the
futex (a stop, so the depth gets smaller). -/
theorem loopD_body (hP : L.Fits P U) (hc1 : L.c = 1) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (hg : L.ph g = .out) (D : Nat) (s : Thread_Mutex_lockLocals) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (h : lockInvD P L t g D s G m d) :
    P.WP t ((osUnfairLockTry p : CM Tgt Thread_Mutex_lockLocals Bool).run s) (fun r G' m' d' =>
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
  unfold osUnfairLockTry
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [hp]
  refine WP.bind (wp_casD hP hc1 hph hi fun k hk G₁ m₁ r hc₁ hcase => ?_)
  rcases hcase with ⟨rfl, hL, hi₁⟩ | ⟨rfl, hi₁⟩
  · simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [id, Bool.false_eq_true, ↓reduceIte]
    rw [hset] at hi₁
    exact ⟨rfl, by omega, hc₁, hL, hi₁⟩
  · simp only [StateT.run_bind, bind_assoc, pure_bind]
    rw [hset] at hi₁
    refine WP.bind (wp_waitD hP (g := L.set g .wait Heap.empty) (L.ph_set _ _ _) hi₁
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [id, ↓reduceIte]
    rw [L.set_set] at hi₂
    exact ⟨⟨by omega, _, .inr rfl, hi₂⟩, .inl (by omega)⟩

/-- `lock` (macOS) by thread `t` at `out` (`g`): it holds the mutex. -/
theorem lockD_spec (hP : L.Fits P U) (hc1 : L.c = 1) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (hg : L.ph g = .out) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G m d := by
  unfold Thread_Mutex_lock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  unfold osUnfairLockC
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (lockInvD P L t g d) (fun _ => 0) (lockPostD P L t g d)
    (loopD_body hP hc1 hp t g hg d) default G m d ⟨by omega, g, .inl rfl, hi⟩))
  rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', hL, hi'⟩
  simp only [StateT.run_pure, pure_bind]
  exact WP.pure' (WP.pure' ⟨hd', hc', hL, hi'⟩)

/-- `unlock` (macOS) by the holder `t` (`g`): it goes to `out`. -/
theorem unlockD_spec (hP : L.Fits P U) (hc1 : L.c = 1) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (hg : L.ph g = .holds) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_unlock p) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = t ∧ P.inv (upd G' t (L.set g .out Heap.empty)) m') G m d := by
  unfold Thread_Mutex_unlock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  unfold osUnfairUnlockC
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [hp]
  refine WP.bind (wp_xchgRel hP hc1 hg hi fun k₁ hk₁ G₁ m₁ r hc₁ hi₁ => ?_)
  simp only [StateT.run_pure, pure_bind]
  rw [threadFutexWakeC_eq]
  refine WP.bind (wp_wake hP (g := L.set g .wake Heap.empty) (L.ph_set _ _ _) hi₁
    fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
  simp only [StateT.run_pure, pure_bind]
  rw [L.set_set] at hi₂
  exact WP.pure' (WP.pure' ⟨by omega, hc₂, hi₂⟩)

end_if

/- The rules need `WP` only as a name: unfolding it runs the program. -/
attribute [local irreducible] Proto.WP

/-- `lock` by thread `t` at `out` (`g`): it holds the mutex, with a resource `hL`. The proof is the
one of the translation of the OS. -/
theorem lock_spec (hP : L.Fits P U) (hc : L.c = mutexC) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (hg : L.ph g = .out) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_lock p) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ ∃ hL, P.inv (upd G' t (L.set g .holds hL)) m') G m d := by
  first
  | (have hc3 : L.c = 3 := (by unfold mutexC at hc; exact hc); exact lockL_spec hP hc3 hp t g hg G m d hi)
  | exact lockD_spec hP hc hp t g hg G m d hi

/-- `unlock` by the holder `t` (`g`): it goes to `out`. -/
theorem unlock_spec (hP : L.Fits P U) (hc : L.c = mutexC) {p : Ptr} (hp : p = L.ptr) (t : ThreadId)
    (g : γ) (hg : L.ph g = .holds) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t g) m) :
    P.WP t (Thread_Mutex_unlock p) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = t ∧ P.inv (upd G' t (L.set g .out Heap.empty)) m') G m d := by
  first
  | (have hc3 : L.c = 3 := (by unfold mutexC at hc; exact hc); exact unlockL_spec hP hc3 hp t g hg G m d hi)
  | exact unlockD_spec hP hc hp t g hg G m d hi
end ThreadMutexOps
end Threadsync
